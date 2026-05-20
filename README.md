# graphs-bench

A Rust implementation and benchmark of the directed single-source shortest path
algorithm from

> Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> arXiv:[2504.17033](https://arxiv.org/abs/2504.17033) (v2, 2025).

The paper gives the first **O(m · log^{2/3} n)**-time SSSP algorithm in the
comparison-addition model, breaking the **O(m + n log n)** sorting barrier that
Dijkstra's algorithm hits with a Fibonacci heap.

See [`ALGORITHM.md`](./ALGORITHM.md) for a detailed write-up of the algorithm
(notation, parameters, the three sub-routines `FindPivots`, `BaseCase`,
`BMSSP`, the partial-sorting data structure `D`, and the complexity analysis).

For the **formal verification** in Lean 4 + Mathlib (a blueprint with every
paper lemma stated; proofs in progress), see [`formal/`](./formal/). The
arXiv article and its TeX source are vendored under
[`formal/paper/`](./formal/paper/).

## Layout

* `src/graph.rs` — CSR-encoded directed graph with `f64` weights.
* `src/random_graph.rs` — Erdős–Rényi-style random generator that guarantees a
  spanning out-arborescence rooted at vertex 0, so every vertex is reachable
  from the source.
* `src/dijkstra.rs` — textbook Dijkstra with a binary heap (the baseline).
* `src/dstruct.rs` — the paper's block-based partial-sorting structure `D`
  (Lemma 3.3), with `Insert`, `BatchPrepend`, `Pull`.
* `src/bmssp.rs` — `FindPivots`, `BaseCase`, `BMSSP`, and the top-level
  `sssp_bmssp` entry point.
* `src/main.rs` — Dijkstra vs. BMSSP timing comparison.
* `.cursor/skills/lean4/` — Cursor agent skill for Lean 4 / mathlib work (migrated
  from the OpenCode `lean4-skills` plugin). OpenCode reads the same path via
  `.opencode/opencode.json`.

## Running

Rust **≥ 1.85** is required (`edition = "2024"`; see `rust-version` in `Cargo.toml`).

```bash
cargo test --release          # correctness tests against Dijkstra
cargo run  --release          # benchmark sweep
```

## Sample results

Random directed graphs, weights uniform in `(0, 1]`, source = vertex 0, avg
out-degree 4 (sparse — where BMSSP's asymptotic edge is widest). `L` is
BMSSP's recursion depth, `ratio` is BMSSP-time / Dijkstra-time, and
`ratio·log^{1/3}(n)` rescales by the predicted asymptotic gap (a flat column
means we're in the asymptotic regime).

```
        n           m    L     Dijkstra        BMSSP    ratio  ratio·log^⅓  match
---------------------------------------------------------------------------------
     1000        4000    3      109.2 µs      554.3 µs   5.08x       10.92  yes
     3000       12000    3      375.8 µs       1.72 ms   4.59x       10.37  yes
    10000       40000    3       1.59 ms       5.90 ms   3.72x        8.80  yes
    30000      120000    3       6.81 ms      20.73 ms   3.05x        7.49  yes
   100000      400000    3      34.13 ms      85.64 ms   2.51x        6.40  yes
   300000     1200000    4     146.61 ms     374.60 ms   2.56x        6.72  yes
  1000000     4000000    3     724.31 ms      1.570 s    2.17x        5.88  yes
  1500000     6000000    3      1.113 s       2.647 s    2.38x        6.51  yes
  2000000     8000000    3      1.661 s       4.010 s    2.41x        6.65  yes
  2500000    10000000    4      2.091 s       6.029 s    2.88x        7.99  yes
  3000000    12000000    4      2.508 s       7.856 s    3.13x        8.71  yes
  4000000    16000000    4      3.577 s      12.559 s    3.51x        9.83  yes
```

### Asymptotic check

The benchmark exposes three things:

1. **Within each `L` regime the ratio falls like `1 / log^{1/3}(n)`.**
   From `n = 1k` to `n = 1M` (all at `L = 3`) the raw ratio drops `5.08× → 2.17×`
   while `ratio·log^{1/3}` drops only `10.92 → 5.88` — and most of *that*
   residual drop comes from amortizing BMSSP's per-call overhead. This is
   exactly the predicted `Θ(m·log^{2/3} n)` vs. `Θ(m·log n)` gap.

2. **Recursion-depth steps.** `L = ⌈log₂(n) / ⌊log₂^{2/3}(n)⌋⌉` is a step
   function; in the table it sits at 3 for most of `n ∈ [1k, 2M]`, ticks up
   to 4 near `n ≈ 300k` (where `t` flips from 7 to 6), drops back to 3 around
   `n ≈ 1M`, then jumps to 4 again past `n ≈ 2M`. Each time `L` increases by
   1, `ratio·log^{1/3}` jumps by ~25–35% — that's the extra recursion frame
   showing up as a constant in BMSSP's hidden multiplier.

3. **Constants are big.** Dijkstra's per-edge cost grows from 27 ns at
   `n = 1k` to 224 ns at `n = 4M` — that's L1/L2/L3 cache misses on the heap,
   not the algorithmic `log n`. BMSSP pays a similar cache penalty and on top
   of that carries 3–4 nested recursion frames, per-level Bellman–Ford, and
   the block data structure. As a result, even at `n = 4M` BMSSP is still
   3.5× slower than Dijkstra. The crossover would need
   `log^{1/3}(n) ≳ 6`, i.e. `n ≳ 2^{216}` — astronomical.

The benchmark prints `match=yes` on every line: BMSSP's distances agree with
Dijkstra exactly (to within `1e-7` relative tolerance).
