//! Random graph generators producing instances that are guaranteed connected
//! from vertex 0 (so the SSSP problem is well-defined for every vertex).

use rand::Rng;
use rand::SeedableRng;
use rand::distributions::{Distribution, Standard};
use rand_chacha::ChaCha8Rng;

use crate::graph::Graph;

/// Generate a directed graph with `n` vertices and roughly `target_edges` edges
/// drawn uniformly at random, with `f64` weights in `(0, 1]`.
///
/// A random spanning out-arborescence rooted at vertex `0` is added first so
/// every vertex is reachable from `0`.
pub fn random_directed(n: usize, target_edges: usize, seed: u64) -> Graph {
    assert!(n >= 2);
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut edges: Vec<(u32, u32, f64)> = Vec::with_capacity(target_edges.max(n - 1));

    // Random permutation of 1..n attached one by one to a random earlier vertex
    // → spanning out-arborescence rooted at 0.
    let mut order: Vec<u32> = (1..n as u32).collect();
    for i in (1..order.len()).rev() {
        let j = rng.gen_range(0..=i);
        order.swap(i, j);
    }
    let mut placed: Vec<u32> = Vec::with_capacity(n);
    placed.push(0);
    for &v in &order {
        let parent_idx = rng.gen_range(0..placed.len());
        let u = placed[parent_idx];
        let w = sample_weight(&mut rng);
        edges.push((u, v, w));
        placed.push(v);
    }

    let extra = target_edges.saturating_sub(edges.len());
    for _ in 0..extra {
        let u = rng.gen_range(0..n as u32);
        let mut v = rng.gen_range(0..n as u32);
        if v == u {
            v = (v + 1) % n as u32;
        }
        let w = sample_weight(&mut rng);
        edges.push((u, v, w));
    }

    Graph::from_edges(n, &edges)
}

#[inline]
fn sample_weight(rng: &mut ChaCha8Rng) -> f64 {
    let x: f64 = Standard.sample(rng);
    if x == 0.0 { 1e-12 } else { x }
}
