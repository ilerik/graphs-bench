//! Textbook Dijkstra with a binary min-heap.
//!
//! Time `O((n + m) log n)`. Used as the baseline against which the BMSSP
//! algorithm is benchmarked.

use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::graph::Graph;

#[derive(Copy, Clone, Debug)]
struct HeapItem {
    /// Negated so `BinaryHeap` (max-heap) behaves as a min-heap.
    d: f64,
    v: u32,
}

impl PartialEq for HeapItem {
    fn eq(&self, other: &Self) -> bool {
        self.d == other.d && self.v == other.v
    }
}
impl Eq for HeapItem {}
impl Ord for HeapItem {
    fn cmp(&self, other: &Self) -> Ordering {
        // Larger `d` = smaller priority in our max-heap.
        other
            .d
            .partial_cmp(&self.d)
            .unwrap_or(Ordering::Equal)
            .then_with(|| other.v.cmp(&self.v))
    }
}
impl PartialOrd for HeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn dijkstra(g: &Graph, source: usize) -> Vec<f64> {
    let mut dist = vec![f64::INFINITY; g.n];
    dist[source] = 0.0;
    let mut heap: BinaryHeap<HeapItem> = BinaryHeap::with_capacity(g.n);
    heap.push(HeapItem {
        d: 0.0,
        v: source as u32,
    });
    while let Some(HeapItem { d, v }) = heap.pop() {
        let v_us = v as usize;
        if d > dist[v_us] {
            continue;
        }
        for (to, w) in g.out_edges(v_us) {
            let nd = d + w;
            let to_us = to as usize;
            if nd < dist[to_us] {
                dist[to_us] = nd;
                heap.push(HeapItem { d: nd, v: to });
            }
        }
    }
    dist
}

#[cfg(test)]
mod fixture_tests {
    use super::*;
    use crate::graph::Graph;
    use serde::Deserialize;
    use std::fs;

    #[derive(Debug, Deserialize)]
    struct Fixture {
        name: String,
        n: usize,
        source: usize,
        edges: Vec<(u32, u32, f64)>,
        expected_dist: Vec<Option<f64>>,
    }

    fn assert_distances_match(got: &[f64], expected: &[Option<f64>]) {
        assert_eq!(got.len(), expected.len());
        for (i, (g, e)) in got.iter().zip(expected.iter()).enumerate() {
            match e {
                None => assert!(g.is_infinite(), "vertex {i}: expected inf, got {g}"),
                Some(y) => {
                    let diff = (g - y).abs();
                    assert!(
                        diff < 1e-9 || diff < 1e-9 * g.abs().max(y.abs()),
                        "vertex {i}: got {g}, expected {y}"
                    );
                }
            }
        }
    }

    fn load_fixture(path: &str) -> Fixture {
        let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        serde_json::from_str(&text).unwrap_or_else(|e| panic!("parse {path}: {e}"))
    }

    #[test]
    fn shared_json_fixtures() {
        for path in [
            "formal/fixtures/dijkstra/tiny_chain.json",
            "formal/fixtures/dijkstra/diamond_with_ties.json",
            "formal/fixtures/dijkstra/unreachable_vertices.json",
            "formal/fixtures/dijkstra/single_vertex.json",
        ] {
            let fx = load_fixture(path);
            assert!(
                !fx.name.is_empty(),
                "fixture name should not be empty: {path}"
            );
            let edges: Vec<(u32, u32, f64)> = fx.edges;
            let g = Graph::from_edges(fx.n, &edges);
            let got = dijkstra(&g, fx.source);
            assert_distances_match(&got, &fx.expected_dist);
        }
    }
}
