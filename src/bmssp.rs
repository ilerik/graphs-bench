//! Bounded Multi-Source Shortest Path (BMSSP), the recursive procedure that
//! powers the `O(m log^{2/3} n)`-time SSSP algorithm of Duan, Mao, Mao, Shu,
//! and Yin (arXiv:2504.17033). See `ALGORITHM.md` for a detailed description.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};

use crate::dstruct::DStruct;
use crate::graph::Graph;

/// Compute shortest-path distances from `source` to every vertex.
pub fn sssp_bmssp(g: &Graph, source: usize) -> Vec<f64> {
    let n = g.n;
    assert!(source < n);
    let mut d = vec![f64::INFINITY; n];
    d[source] = 0.0;

    // k = ⌊log^{1/3} n⌋,  t = ⌊log^{2/3} n⌋,  L = ⌈log n / t⌉.
    // The paper's "log" is log₂; that's what makes the bound `k·2^{Lt} ≥ n`
    // (and hence the top-level call always "successful") hold.
    let log2_n = ((n as f64).max(2.0)).log2();
    let k = (log2_n.powf(1.0 / 3.0)).floor() as usize;
    let t = (log2_n.powf(2.0 / 3.0)).floor() as usize;
    let k = k.max(1);
    let t = t.max(1);
    let levels = ((log2_n / t as f64).ceil() as usize).max(1);

    {
        let mut ctx = Context {
            graph: g,
            d: &mut d,
            n,
            k,
            t,
        };
        let _ = bmssp(&mut ctx, levels, f64::INFINITY, &[source as u32]);
    }

    d
}

struct Context<'a> {
    graph: &'a Graph,
    d: &'a mut [f64],
    n: usize,
    k: usize,
    t: usize,
}

impl<'a> Context<'a> {
    /// `min(1 << (a * b), n)`, saturating on overflow so we never allocate
    /// anything larger than `n` for block-size hints.
    #[inline]
    fn pow2_clamped(&self, a: usize, b: usize) -> usize {
        let bits = a.saturating_mul(b);
        if bits >= 60 {
            self.n.max(1)
        } else {
            (1usize << bits).min(self.n.max(1))
        }
    }

    /// `k * 2^{a*b}` clamped to `n+1`, used as an upper bound on `|U|`.
    #[inline]
    fn k_pow2_clamped(&self, a: usize, b: usize) -> usize {
        let bits = a.saturating_mul(b);
        if bits >= 60 {
            self.n.saturating_add(1)
        } else {
            self.k
                .saturating_mul(1usize << bits)
                .min(self.n.saturating_add(1))
        }
    }
}

// ----------------------------------------------------------------------------
// Algorithm 1: FindPivots
// ----------------------------------------------------------------------------

fn find_pivots(ctx: &mut Context, b: f64, s: &[u32]) -> (Vec<u32>, Vec<u32>) {
    let k = ctx.k;
    let s_set: HashSet<u32> = s.iter().copied().collect();

    // W: set of all visited vertices so far (initially S).
    let mut w_set: HashSet<u32> = s_set.clone();
    let mut w_list: Vec<u32> = s.to_vec();
    // Frontier of the current Bellman–Ford round.
    let mut frontier: Vec<u32> = s.to_vec();
    // Tight-edge predecessor inside W (only for non-S vertices).
    let mut parent: HashMap<u32, u32> = HashMap::new();

    let cap = k.saturating_mul(s.len());

    for _round in 0..k {
        let mut next_frontier: Vec<u32> = Vec::new();
        let mut seen_in_next: HashSet<u32> = HashSet::new();
        for &u in &frontier {
            let du = ctx.d[u as usize];
            if !du.is_finite() {
                continue;
            }
            for (v, w) in ctx.graph.out_edges(u as usize) {
                let nd = du + w;
                let dv = ctx.d[v as usize];
                if nd <= dv {
                    if nd < dv {
                        ctx.d[v as usize] = nd;
                    }
                    // Under Assumption 2.1 (distinct path lengths) ties
                    // don't occur; with equal weights the last-visited
                    // tight-edge parent wins, which is fine for pivot selection.
                    if !s_set.contains(&v) {
                        parent.insert(v, u);
                    }
                    if nd < b {
                        if w_set.insert(v) {
                            w_list.push(v);
                        }
                        if seen_in_next.insert(v) {
                            next_frontier.push(v);
                        }
                    }
                }
            }
        }
        frontier = next_frontier;

        if w_list.len() > cap {
            // |W| > k|S|: shortcut — return the full S as pivots.
            return (s.to_vec(), w_list);
        }
        if frontier.is_empty() {
            break;
        }
    }

    // Build the tight-edge forest's tree sizes. Each vertex of W traces its
    // parent chain up to the unique root in S (under Assumption 2.1) and
    // increments that root's counter.
    //
    // If `parent[cur]` is missing (should not happen for v ∈ W \ S under a
    // consistent run) or the chain cycles, we stop without counting — that
    // vertex simply does not contribute to any pivot's subtree size.
    let max_chain = w_list.len().saturating_add(1);
    let mut tree_size: HashMap<u32, usize> = HashMap::new();
    for &v in &w_list {
        let mut cur = v;
        for _ in 0..max_chain {
            if s_set.contains(&cur) {
                *tree_size.entry(cur).or_insert(0) += 1;
                break;
            }
            match parent.get(&cur) {
                Some(&p) => cur = p,
                None => break,
            }
        }
    }

    let pivots: Vec<u32> = s
        .iter()
        .copied()
        .filter(|u| tree_size.get(u).copied().unwrap_or(0) >= k)
        .collect();

    (pivots, w_list)
}

// ----------------------------------------------------------------------------
// Algorithm 2: BaseCase  (a mini Dijkstra from a single source vertex)
// ----------------------------------------------------------------------------

#[derive(Copy, Clone)]
struct HeapItem {
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

fn base_case(ctx: &mut Context, b: f64, s: &[u32]) -> (f64, Vec<u32>) {
    debug_assert_eq!(s.len(), 1, "base case requires |S| = 1");
    let x = s[0];
    let k = ctx.k;

    let mut in_u0 = HashSet::new();
    in_u0.insert(x);
    let mut u0_list: Vec<u32> = vec![x];

    let mut heap: BinaryHeap<HeapItem> = BinaryHeap::new();
    heap.push(HeapItem {
        d: ctx.d[x as usize],
        v: x,
    });

    while u0_list.len() < k + 1 {
        let Some(HeapItem { d: du, v: u }) = heap.pop() else {
            break;
        };
        // Skip stale heap entries.
        if du > ctx.d[u as usize] {
            continue;
        }
        if !in_u0.contains(&u) {
            in_u0.insert(u);
            u0_list.push(u);
        }
        for (to, w) in ctx.graph.out_edges(u as usize) {
            let nd = du + w;
            if nd <= ctx.d[to as usize] {
                // Per Alg. 2: relax `d[v]` whenever an improvement is found,
                // but only push the neighbour onto the heap if the new value
                // is strictly below `B` (otherwise it's not in scope here).
                if nd < ctx.d[to as usize] {
                    ctx.d[to as usize] = nd;
                }
                if nd < b {
                    heap.push(HeapItem { d: nd, v: to });
                }
            }
        }
    }

    if u0_list.len() <= k {
        // We exhausted everything reachable below `B` without filling k+1 slots.
        (b, u0_list)
    } else {
        // We popped k+1 vertices; cap the result at the smallest k of them.
        let bprime = u0_list
            .iter()
            .map(|&v| ctx.d[v as usize])
            .fold(f64::NEG_INFINITY, f64::max);
        let u: Vec<u32> = u0_list
            .into_iter()
            .filter(|&v| ctx.d[v as usize] < bprime)
            .collect();
        (bprime, u)
    }
}

// ----------------------------------------------------------------------------
// Algorithm 3: BMSSP
// ----------------------------------------------------------------------------

fn bmssp(ctx: &mut Context, l: usize, b: f64, s: &[u32]) -> (f64, Vec<u32>) {
    if l == 0 {
        return base_case(ctx, b, s);
    }

    let (pivots, w) = find_pivots(ctx, b, s);

    let m = ctx.pow2_clamped(l - 1, ctx.t);
    let u_bound = ctx.k_pow2_clamped(l, ctx.t);

    let mut data = DStruct::new(m, b);
    let mut bprime_0 = f64::INFINITY;
    for &x in &pivots {
        let dx = ctx.d[x as usize];
        data.insert(x, dx);
        if dx < bprime_0 {
            bprime_0 = dx;
        }
    }
    if pivots.is_empty() {
        bprime_0 = b;
    }

    // `U` is a union of recursive returns; the same vertex can appear in more
    // than one `U_i`, so we dedupe for the `|U|` workload cap.
    let mut u: HashSet<u32> = HashSet::new();

    let mut last_bprime: f64 = bprime_0;

    let success: bool;
    loop {
        if data.is_empty() {
            success = true;
            break;
        }
        let (bi, si) = data.pull();
        if si.is_empty() {
            success = true;
            break;
        }

        let (bp_i, ui) = bmssp(ctx, l - 1, bi, &si);
        last_bprime = bp_i;
        for &v in &ui {
            u.insert(v);
        }

        let mut kk: Vec<(u32, f64)> = Vec::new();
        for &uv in &ui {
            let du = ctx.d[uv as usize];
            for (v, ew) in ctx.graph.out_edges(uv as usize) {
                let nd = du + ew;
                let dv = ctx.d[v as usize];
                if nd <= dv {
                    if nd < dv {
                        ctx.d[v as usize] = nd;
                    }
                    if nd >= bi && nd < b {
                        data.insert(v, nd);
                    } else if nd >= bp_i && nd < bi {
                        kk.push((v, nd));
                    }
                }
            }
        }
        // Re-add S_i entries that landed in [B'_i, B_i).
        for &x in &si {
            let dx = ctx.d[x as usize];
            if dx >= bp_i && dx < bi {
                kk.push((x, dx));
            }
        }
        data.batch_prepend(kk);

        if u.len() >= u_bound {
            success = false;
            break;
        }
    }

    let final_bprime = if success { b } else { last_bprime.min(b) };

    // Returned U must be a subset of {v : d̂[v] < B'}. In a partial execution
    // the last-iteration B'_i can be strictly below earlier B'_j, so we
    // filter accumulated `u` against the final B'.
    u.retain(|&v| ctx.d[v as usize] < final_bprime);
    for &x in &w {
        if ctx.d[x as usize] < final_bprime {
            u.insert(x);
        }
    }
    let result: Vec<u32> = u.into_iter().collect();

    (final_bprime, result)
}

// ----------------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dijkstra::dijkstra;
    use crate::random_graph::random_directed;

    fn assert_distances_match(a: &[f64], b: &[f64]) {
        assert_eq!(a.len(), b.len());
        for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
            if x.is_infinite() && y.is_infinite() {
                continue;
            }
            let diff = (x - y).abs();
            assert!(
                diff < 1e-9 || diff < 1e-9 * x.abs().max(y.abs()),
                "vertex {}: bmssp={} dijkstra={}",
                i,
                x,
                y
            );
        }
    }

    #[test]
    fn tiny_chain() {
        let g = Graph::from_edges(4, &[(0, 1, 1.0), (1, 2, 2.0), (2, 3, 3.0)]);
        let d = sssp_bmssp(&g, 0);
        assert_eq!(d, vec![0.0, 1.0, 3.0, 6.0]);
    }

    #[test]
    fn small_random() {
        for seed in 0..16u64 {
            let g = random_directed(50, 200, seed);
            let d_bmssp = sssp_bmssp(&g, 0);
            let d_dij = dijkstra(&g, 0);
            assert_distances_match(&d_bmssp, &d_dij);
        }
    }

    #[test]
    fn medium_random() {
        let g = random_directed(2_000, 8_000, 42);
        let d_bmssp = sssp_bmssp(&g, 0);
        let d_dij = dijkstra(&g, 0);
        assert_distances_match(&d_bmssp, &d_dij);
    }

    #[test]
    fn random_sweep() {
        for &(n, m) in &[
            (20usize, 80usize),
            (100, 400),
            (500, 2_000),
            (1_500, 6_000),
            (3_000, 12_000),
        ] {
            for seed in 0..8u64 {
                let g = random_directed(n, m, seed);
                let d_bmssp = sssp_bmssp(&g, 0);
                let d_dij = dijkstra(&g, 0);
                for (i, (a, b)) in d_bmssp.iter().zip(d_dij.iter()).enumerate() {
                    let diff = (a - b).abs();
                    assert!(
                        diff < 1e-9 || diff < 1e-9 * a.abs().max(b.abs()),
                        "n={} m={} seed={} v={} bmssp={} dij={}",
                        n,
                        m,
                        seed,
                        i,
                        a,
                        b,
                    );
                }
            }
        }
    }

    #[test]
    fn diamond_with_ties() {
        // Path 0→1→3 has length 2, path 0→2→3 has length 2: a tie. Both
        // algorithms should agree (Dijkstra picks one canonical path).
        let g = Graph::from_edges(4, &[(0, 1, 1.0), (0, 2, 1.0), (1, 3, 1.0), (2, 3, 1.0)]);
        let d_bmssp = sssp_bmssp(&g, 0);
        let d_dij = dijkstra(&g, 0);
        assert_distances_match(&d_bmssp, &d_dij);
    }

    #[test]
    fn unreachable_vertices() {
        // Two disconnected components: 0→1→2 and isolated 3→4.
        // Vertices 3 and 4 are unreachable from source 0.
        let g = Graph::from_edges(5, &[(0, 1, 1.0), (1, 2, 2.0), (3, 4, 1.0)]);
        let d_bmssp = sssp_bmssp(&g, 0);
        let d_dij = dijkstra(&g, 0);
        assert_distances_match(&d_bmssp, &d_dij);
        assert_eq!(d_bmssp[0], 0.0);
        assert_eq!(d_bmssp[1], 1.0);
        assert_eq!(d_bmssp[2], 3.0);
        assert!(d_bmssp[3].is_infinite());
        assert!(d_bmssp[4].is_infinite());
    }
}
