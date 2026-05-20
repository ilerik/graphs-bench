# Future work (post–Phase 3)

This document records the remaining verification and engineering work after
completing **Phase 3** (verified Dijkstra, Refine operational model, shared
JSON fixtures).  See `formal/README.md` for the full multi-phase roadmap.

## Phase 3 follow-ups (near term)

### 1. Lean executable cross-check on fixtures

**Status:** done — `Sssp.Fixtures.Dijkstra` uses `distsMatch` + `#guard` /
`native_decide` on `Sssp.Refine.dijkstra`.  Rust runs
`cargo test shared_json_fixtures`.  CI: `.github/workflows/ci.yml` and
`formal/scripts/check-fixtures.sh`.

**Remaining:**

- Optionally parse JSON in Lean (via `Lean.Json` or code-gen) so fixture files
  are the single source of truth instead of duplicated edge lists in
  `Sssp.Fixtures.Graph`.
- The verified `Sssp.Algo.dijkstra` is **noncomputable** (`DistEstimate` over
  `WithTop NNReal`); executable checks stay on Refine/Rust unless we add a
  separate computable extraction path.

### 2. Refine step lemmas (done in this pass)

`distStale`, `dijkstraStep_stale`, and `dijkstraStep_fresh` are proved using
`match distStale … with` instead of a `Prop`-backed `if`, avoiding Float
`split_ifs` pain.

**Next:** induction on `dijkstraRun` fuel to relate heap Dijkstra to
`relaxRound` / `trueDist` on restricted graph classes (integer weights, no
stale duplicates after settlement).

### 3. NNReal ↔ Float bridge

**Status:** partial — `floatWeight` / `nnrealWeight` in `Sssp.Refine.Dijkstra`;
shared edge lists in `Sssp.Fixtures.Graph` build both `Graph n` and `RustGraph`.

**Remaining:**

- Prove CSR ↔ multiset correspondence (`rust_outEdge_mem_graph` style lemmas).
- Prove `Refine.dijkstra` matches `Algo.dijkstra` on that image for **integer
  weights** (then extend to dyadic / rational via monotonicity).
- Handle `distInf` vs `⊤` for unreachable vertices explicitly in the proof.

### 4. Refine ≡ Algo structural equivalence

Long-term refinement proof (Phase 9 overlap):

| Layer | Role |
|-------|------|
| `Sssp.Algo.Dijkstra` | Verified `n`-round relaxation → `dijkstraSpec` |
| `Sssp.Refine.Dijkstra` | Lazy heap, `Float`, mirrors `src/dijkstra.rs` |
| Rust `dijkstra.rs` | Production implementation |

Goal: `Refine.dijkstra` = extract(`Algo.dijkstra`) on shared inputs, or a
simulation relation preserved by `dijkstraStep`.

---

## Roadmap phases 4–11 (summary)

| Phase | Deliverable | Depends on |
|------:|-------------|------------|
| 4 | `Sssp.Algo.DStruct` — block-list, amortised `Pull` | Phase 2 cost monad (optional for correctness first) |
| 5 | `Sssp.Algo.FindPivots` — k-round Bellman-Ford, Lemma 3.2 | Phase 4 |
| 6 | `Sssp.Algo.BaseCase` — bounded mini-Dijkstra, Lemma 3.1 base | Phase 3 |
| 7 | `Sssp.Algo.BMSSP` — well-founded recursion, Lemmas 3.1/3.10/3.12 | Phases 4–6 |
| 8 | `Sssp.Algo.Main` — top-level driver + equivalence | Phase 7 |
| 9 | Rust↔Lean refinement (extraction or hand proof) | Phases 3–8 |
| 10 | Rust polish: LICENSE, CI, criterion benches | — |
| 11 | Paper + submission | Phases 7–9 |

### Phase 2 reminder: `CostM`

The paper’s `O(m log^{2/3} n)` bound (Lemma 3.12) needs a cost-counting monad
threading comparisons and pointer moves through `DStruct`, `FindPivots`, and
`BMSSP`.  Can be deferred for **functional correctness** proofs but not for the
complexity theorem.

---

## Suggested order of attack

1. ~~**Fixture CI**~~ — done (`.github/workflows/ci.yml`, `#guard` checks).
2. **Refine ↔ Algo on integer fixtures** — shared edge lists done; prove equivalence.
3. **Phase 4 DStruct** — unlocks pivot finding (Phase 5).
4. **Cost monad** — parallel track once DStruct API stabilises.
5. **BMSSP well-founded recursion** — highest proof risk; reuse Dijkstra +
   Distance truncation lemmas.

---

## Open proof risks

- **BMSSP recursion measure** — paper’s potential function / batch size `B`
  must be reflected in a Lean `WellFounded` relation.
- **DStruct amortised analysis** — block-list invariants vs paper’s Lemma 3.3.
- **Constant-degree reduction** — Lean graphs already assume `outDeg ≤ 2`; Rust
  CSR is general; show reduction preserves answers used in benchmarks.

---

## Commands (regression)

```bash
cd formal/lean && lake build
./formal/scripts/check-fixtures.sh   # Lean guards + Rust JSON tests
cd /path/to/graphs-bench && cargo test shared_json_fixtures
```

Expected Refine `#eval` (source 0):

| Fixture | Distances |
|---------|-----------|
| tiny_chain | `[0, 1, 3, 6]` |
| diamond_with_ties | `[0, 1, 1, 2]` |
| unreachable_vertices | `[0, 1, 3, inf, inf]` |
| single_vertex | `[0]` |
