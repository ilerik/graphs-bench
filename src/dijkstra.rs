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
    heap.push(HeapItem { d: 0.0, v: source as u32 });
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
