# Future work

## Current priority: Dijkstra refinement (all inputs)

**Do not start new algorithm proofs** (Phase 4 DStruct, FindPivots, BMSSP, …)
until the **complete Refine ≡ Algo proof for all inputs** is finished.

Phase 3 delivered:

| Layer | Module | Role |
|-------|--------|------|
| Verified algorithm | `Sssp.Algo.Dijkstra` | `dijkstra_correct` — `n`-round relaxation = `trueDist` |
| Operational model | `Sssp.Refine.Dijkstra` | Lazy heap + `Float`, mirrors `src/dijkstra.rs` |
| Regression only | `Sssp.Fixtures.*`, `Sssp.Refine.Bridge` | `#guard` / CI on JSON fixtures — **not** the proof target |

The gap: prove that `Sssp.Refine.dijkstra` (on every valid `RustGraph` with
`outDeg ≤ 2` and non-negative weights) computes the same distances as
`Sssp.Algo.dijkstra` after the graph bridge — for **all inputs**, not just
fixtures.

### Proof plan (Phase 3b)

Work bottom-up; no new paper modules until this closes.

1. **Graph bridge (general)**
   - `RustGraph.toGraph : Graph n` with `outDeg_le` preserved.
   - Lemmas: CSR `outEdges` ↔ multiset `Graph.edges` (not fixture-specific).

2. **Numeric bridge**
   - Embed `NNReal` weights into `Float` (or restrict to dyadic/rational class
     first); relate `distInf` to `⊤` for unreachable vertices.

3. **Simulation relation**
   - Invariant relating `dijkstraStep` state `(dist, heap)` to `DistEstimate`
     from `Algo.dijkstra` / `relaxRound`.
   - Extend `dijkstraStep_stale` / `dijkstraStep_fresh` by induction on
     `dijkstraRun` fuel.

4. **Main theorem (target)**
   ```lean
   theorem refine_dijkstra_correct {n} (G : Graph n) (g : RustGraph) … (s : Fin n) (v : Fin n) :
     nnrealToFloat (Algo.dijkstra G s v) = (Refine.dijkstra g s.val)[v.val]!
   ```
   (Exact statement to be fixed once the bridge API stabilises.)

5. **Rust corollary**
   - Hand proof or extraction that `src/dijkstra.rs` refines
     `Sssp.Refine.Dijkstra` (Phase 9 overlap, but Dijkstra-only can land here).

Fixtures and CI stay as regression harnesses while the general proof is in
progress; do not add further fixture-only theorems unless they directly unlock
step (1)–(4).

---

## Deferred (blocked on Phase 3b)

| Phase | Deliverable | Blocked by |
|------:|-------------|------------|
| 4 | `Sssp.Algo.DStruct` | Phase 3b |
| 5 | `Sssp.Algo.FindPivots` | Phase 4 |
| 6 | `Sssp.Algo.BaseCase` | Phase 3b (mini-Dijkstra reuse) |
| 7–8 | BMSSP + Main | Phases 4–6 |
| 9 | Full-stack Rust↔Lean | Phase 3b for Dijkstra slice |
| 2 | `CostM` (complexity) | Can run in parallel with 3b if desired; not required for functional refinement |

---

## Regression (unchanged)

```bash
cd formal/lean && lake build
./formal/scripts/check-fixtures.sh
cargo test shared_json_fixtures
```

These guard against regressions while Phase 3b is in flight; passing them does
**not** substitute for the all-inputs refinement proof.
