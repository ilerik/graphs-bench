# Breaking the Sorting Barrier for Directed SSSP

This document summarizes the algorithm from

> Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> arXiv:2504.17033 (v2, July 2025).

The paper gives a deterministic algorithm that solves single-source shortest
paths (SSSP) on directed graphs with non-negative real weights in
**O(m · log^{2/3} n)** time in the comparison-addition model, breaking the
**O(m + n log n)** bound that Dijkstra's algorithm achieves with a Fibonacci
or relaxed heap. It is the first SSSP algorithm to break the "sorting barrier"
for directed real-weighted graphs.

## 1. Notation and setting

* `G = (V, E)` directed graph, `n = |V|`, `m = |E|`.
* Non-negative weight `w_{uv} ≥ 0` on each edge `(u, v) ∈ E`.
* Source `s ∈ V`; we assume every vertex is reachable from `s`, so `m ≥ n − 1`.
* `d(v)` = true distance from `s` to `v`.
* `d̂[v]` = current upper-bound estimate, updated only by edge relaxations.
  Initially `d̂[s] = 0` and `d̂[v] = ∞` for `v ≠ s`.
* A vertex `v` is *complete* when `d̂[v] = d(v)`; otherwise it is *incomplete*.

By a standard reduction (Frederickson '83 style: split each vertex into a
zero-weight cycle of degree-2 copies) we may assume both in- and out-degree are
≤ 2; then `m = O(n)` so we can write `O(m log^{2/3} n) = O(n log^{2/3} n)` in the
analysis. The implementation here works on the original graph directly; the
analysis still holds because we never read more than O(deg(u)) edges per visit
of u.

The algorithm runs in the **comparison-addition model**, which is the natural
model for real-number weights: only additions of weights/distances and
comparisons of them are allowed.

## 2. Parameters

Let

```
k = ⌊ log^{1/3}(n) ⌋
t = ⌊ log^{2/3}(n) ⌋
L = ⌈ log(n) / t ⌉   (= ⌈ log^{1/3}(n) ⌉)
```

`k` is the Bellman–Ford "shrinking radius" used to collapse frontiers, `t` is
the geometric factor that the frontier shrinks by between recursion levels, and
`L` is the recursion depth.

## 3. Key idea

Dijkstra spends `Θ(log n)` per vertex because it sorts the entire frontier `S`
of explored-but-not-yet-finalized vertices. The frontier can grow to `Θ(n)`,
forcing `Θ(n log n)` time.

The new algorithm replaces the global priority queue with a **divide-and-conquer
over bounded distance ranges** combined with a "frontier-shrinking" trick:

Given a frontier `S` and bound `B`, define
`Ũ = { v : d(v) < B and the shortest s→v path visits some vertex of S }`.

We can prove that the size of the frontier we *actually need* is at most
`|Ũ| / k` by extracting a set `P ⊆ S` of "pivots":

* Run `k` Bellman–Ford steps from `S` (always restricted to distances `< B`).
  This produces a set `W ⊆ Ũ` of `O(k|S|)` vertices.
* If `|W| > k|S|`, the frontier is already small enough (size `≤ |W|/k`).
* Otherwise every still-incomplete vertex of `Ũ` has a shortest path that goes
  through some vertex `y ∈ S` whose "tight-edge" tree in `W` has size `≥ k`.
  Such `y` are the **pivots** `P`, and `|P| ≤ |W|/k ≤ |Ũ|/k`.

This is `FindPivots`. Then the recursion (`BMSSP`) processes only the pivots,
saving a factor of `k` of work at each level.

To make the recursion well-defined, sub-problems are described by a level `l`,
a bound `B`, and a frontier `S` of size `≤ 2^{lt}`. The level-0 base case is a
mini Dijkstra. Level `l > 0` splits the work into recursive calls on
`l − 1`-level problems whose frontiers come from a specialised partial-sorting
data structure `D`.

## 4. Sub-routines

### 4.1 `FindPivots(B, S)`  (Algorithm 1)

Goal: shrink `S` to a small pivot set `P`, and collect a set `W` of vertices
already finalised by `k` Bellman–Ford steps.

```
W ← S
W_0 ← S
for i = 1..k:
    W_i ← ∅
    for each edge (u, v) with u ∈ W_{i-1}:
        if d̂[u] + w_{uv} ≤ d̂[v]:
            d̂[v] ← d̂[u] + w_{uv}
            if d̂[u] + w_{uv} < B:
                W_i ← W_i ∪ {v}
    W ← W ∪ W_i
    if |W| > k|S|:
        return (P = S, W)
F ← { (u, v) ∈ E : u, v ∈ W and d̂[v] = d̂[u] + w_{uv} }   # "tight" edges
P ← { u ∈ S : u is the root of a tree of ≥ k vertices in F }
return (P, W)
```

**Guarantee (Lemma 3.2).** `|W| = O(k|S|)`, `|P| ≤ |W|/k`, and for every
`x ∈ Ũ` either `x ∈ W` and `x` is complete, or the shortest path to `x` passes
through some complete `y ∈ P`. Running time `O(k|W|) = O(min{k² |S|, k|Ũ|})`.

### 4.2 `BaseCase(B, S)`  (Algorithm 2)

`l = 0` case: `S = {x}` with `x` already complete.

```
U_0 ← {x}
H ← min-heap with single entry (x, d̂[x])
while H non-empty and |U_0| < k + 1:
    (u, _) ← H.extractMin()
    U_0 ← U_0 ∪ {u}
    for each edge (u, v):
        if d̂[u] + w_{uv} ≤ d̂[v] and d̂[u] + w_{uv} < B:
            d̂[v] ← d̂[u] + w_{uv}
            insert-or-decrease(v, d̂[v]) in H
if |U_0| ≤ k:
    return (B' = B, U = U_0)
else:
    B' ← max_{v ∈ U_0} d̂[v]
    return (B', U = { v ∈ U_0 : d̂[v] < B' })
```

I.e. a tiny Dijkstra that pops up to `k + 1` vertices. If only `k` or fewer
exist below `B`, we return all of them; otherwise we report `B' < B` and
return the (≤ `k`) closer ones. Time `O(k log k)`.

### 4.3 The partial-sorting data structure `D` (Lemma 3.3)

`D` stores `(key, value)` pairs and supports three operations:

* `Insert(key, value)` — amortised `O(max{1, log(N/M)})`, where `N` is the
  total number of insertions and `M` is the block size. If the key exists, the
  smaller value wins.
* `BatchPrepend(L)` — insert `|L|` pairs, all with values strictly smaller than
  everything currently stored, in amortised `O(|L| · max{1, log(|L|/M)})`.
* `Pull()` — return a subset `S' ⊆ D` of the `|S'| ≤ M` *smallest* values and a
  separator `x` with `max(values in S') < x ≤ min(values left in D)` (or
  `x = B` if `D` becomes empty), in amortised `O(|S'|)`.

The structure is two block-linked lists:

* `D1` for inserted items: a sequence of blocks each holding ≤ `M` pairs.
  Blocks are kept in increasing block-upper-bound order, with the upper bounds
  stored in a balanced BST so that `Insert` can binary-search the correct
  block. When a block overflows `M` elements, split it at the median.
* `D0` for batch-prepended items: a sequence of blocks at the front of `D`.
  When the prepended batch has size `> M`, split it into median chunks.

`Pull()` greedily walks the prefix of `D0` then `D1`, gathers up to `M`
elements, picks the smallest `M`, and removes them. The remaining minimum is
the separator `x`.

With the choice `M = 2^{(l−1)t}` and the bound `N = O(k · 2^{lt})` proved in
the analysis, `Insert` costs `O(t)` and `BatchPrepend` `O(log k) = O(log log n)`
per element.

### 4.4 `BMSSP(l, B, S)`  (Algorithm 3)

Pre-conditions: `|S| ≤ 2^{lt}`, `B > max_{x ∈ S} d̂[x]`, and every incomplete
`v` with `d(v) < B` has its shortest path going through some complete vertex
of `S`.

```
if l = 0: return BaseCase(B, S)

P, W ← FindPivots(B, S)
D.init(M = 2^{(l-1)t}, B)
for x in P: D.insert(x, d̂[x])

B'_0 ← min_{x ∈ P} d̂[x]    (or B if P = ∅)
U ← ∅
i ← 0
while |U| < k · 2^{lt} and D is non-empty:
    i += 1
    (B_i, S_i) ← D.pull()
    (B'_i, U_i) ← BMSSP(l - 1, B_i, S_i)
    U ← U ∪ U_i
    K ← ∅
    for each edge (u, v) with u ∈ U_i:
        if d̂[u] + w_{uv} ≤ d̂[v]:
            d̂[v] ← d̂[u] + w_{uv}
            if  B_i ≤ d̂[u] + w_{uv} < B:
                D.insert(v, d̂[u] + w_{uv})
            elif B'_i ≤ d̂[u] + w_{uv} < B_i:
                K.push((v, d̂[u] + w_{uv}))
    D.batchPrepend( K  ∪  { (x, d̂[x]) : x ∈ S_i, d̂[x] ∈ [B'_i, B_i) } )

B' ← min(B'_i, B)
return (B', U ∪ { x ∈ W : d̂[x] < B' })
```

Two ways the loop terminates:

* **Successful execution.** `D` empties and the procedure returns `B' = B`.
  Then `U = T_{<B}(S)` (all vertices below `B` whose shortest path uses
  `S`), and all of `U` is complete.
* **Partial execution.** `|U|` reaches `k · 2^{lt}` first. We bail out with
  the current `B' = B'_i < B`; `U = T_{<B'}(S)`, still complete, and the
  caller will continue from `B'`.

### 4.5 Top-level call

`Distances(s)` runs

```
d̂[s] ← 0;  d̂[v] ← ∞ for v ≠ s
BMSSP(L, ∞, {s})        with L = ⌈log(n) / t⌉
```

Because `|U| ≤ n = o(k · 2^{Lt})`, the top call is always a successful
execution, so all distances are computed.

## 5. Why this is `O(m · log^{2/3} n)`

Per Lemma 3.12 the total running time of `BMSSP(L, ∞, {s})` is bounded by

```
O( (k + 2t/k) · L · n  +  (t + L log k) · m )
= O( (log^{1/3} n + log^{1/3} n) · log^{1/3} n · n
      + (log^{2/3} n + log^{1/3} n · log log n) · m )
= O( n · log^{2/3} n  +  m · log^{2/3} n )
= O( m · log^{2/3} n ).
```

The four ingredients:

1. `FindPivots` over a whole level contributes `O(n k)` per level → `O(n k L) =
   O(n log^{2/3} n)` total.
2. The data structure `D`: inserting pivots costs `O(t)` each; `O(n/k)` pivots
   per level over `L` levels gives `O(n t L / k) = O(n log^{2/3} n)`.
3. Edge relaxations leading to a `D.insert`: each edge can trigger at most one
   such direct insert across the whole algorithm, paying `O(t)` per edge →
   `O(m t) = O(m log^{2/3} n)`.
4. Edges that go through `BatchPrepend`: each level pays `O(m log k)`, with `L`
   levels → `O(m log k · L) = O(m · log^{1/3} n · log log n)`.

All four sum to `O(m log^{2/3} n)`.

## 6. Comparison to Dijkstra

| Algorithm                         | Frontier size  | Per-edge work    | Total                       |
|-----------------------------------|----------------|------------------|-----------------------------|
| Dijkstra + binary heap            | up to `n`      | `O(log n)`       | `O((n + m) log n)`          |
| Dijkstra + Fibonacci heap         | up to `n`      | `O(1) am.`       | `O(m + n log n)`            |
| **BMSSP (this paper)**            | up to `n / k`  | `O(log^{2/3} n)` | `O(m · log^{2/3} n)`        |

For sparse graphs (`m = O(n)`) BMSSP improves the `n log n` term to
`n · log^{2/3} n`, which is the first asymptotic improvement over Dijkstra for
directed real-weighted SSSP.

In practice the constants are large: BMSSP has nested recursion of depth
`O(log^{1/3} n)`, maintains an auxiliary block-linked-list per recursive
frame, and runs Bellman–Ford steps inside `FindPivots`. So while the
asymptotic curve is steeper, for the input sizes we can reasonably benchmark
on a workstation Dijkstra typically wins by a substantial constant factor.
The benchmark in this repo measures that gap directly.

## 7. Implementation notes (this crate)

* `src/graph.rs` — CSR directed graph with `f64` weights.
* `src/dijkstra.rs` — textbook Dijkstra using `BinaryHeap<Reverse<…>>`.
* `src/dstruct.rs` — block-based partial-sorting data structure `D`, with
  lazy deletion via a `key → best-value` map.
* `src/bmssp.rs` — `find_pivots`, `base_case`, `bmssp`, and the top-level
  `sssp_bmssp` entry point.
* `src/random_graph.rs` — Erdős–Rényi-style random directed graphs with a
  guaranteed spanning out-arborescence so every vertex is reachable from `s`.
* `src/bench.rs` — timed comparisons over a sweep of `(n, avg-degree)`.

For tie-breaking we rely on continuous random weights so the
`Assumption 2.1` (all path lengths distinct) holds with probability 1. The
code uses strict `<` for comparisons and `≤` for relaxations exactly as in the
paper.
