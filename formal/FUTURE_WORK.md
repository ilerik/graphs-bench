# Future work

## Current priority: Phase 3c — zero axioms for Dijkstra

Phase 3b is **done**: `refine_dijkstra_correct` on every `ValidRustGraph`.
See `formal/VERIFICATION.md` for the full stack diagram and elimination order.

**Phase 3c goal:** replace all trusted axioms in the Dijkstra proof chain, then
document Rust refinement for `src/dijkstra.rs`.

| Step | Target | Module | Status |
|------|--------|--------|--------|
| 3c.1 | `nnrealToFloat_add_weight`, float order lemmas | `NumericBridge` | in progress (21 axioms) |
| 3c.2 | `floatRelax*_aligned` (3 axioms) | `RelaxBridge` | **DONE** |
| 3c.3 | `outEdge_floatWeight_preimage` | `GraphBridge` | **DONE** |
| 3c.4 | Prove `HeapSettlement` (or its fields) → discharge `dijkstraHeap_eq_dijkstraRelax` | `HeapSimulation` / `HeapBridge` | open (1 axiom; `*_of_settlement` wired) |
| 3c.5 | Rust ↔ `Refine.dijkstra` refinement note | `formal/RUST_DIJKSTRA_REFINEMENT.md` | **DONE** (doc) |

**Proved recently:** `dijkstraRun_{fresh,stale}Count`, `dijkstraRun_freshCount_add_staleCount`,
`dijkstraRun_freshCount_ge_n_add_one_{of_stale_bound,at_heapFuel}`, `HeapSettlement`,
`dijkstraRun_dHat_all_complete_at_heapFuel`, `dijkstraRun_dHat_schedule_of_settlement`,
`dijkstraHeap_eq_dijkstraRelax_of_settlement`, `dijkstraHeap_eq_dijkstraRelax_of_{upper,complete,edgeUpper}`,
`freshPop_isComplete_of_setComplete`, unconditional `refine_dijkstra_correct`.

**Open inside `HeapSettlement`:** `staleBound`, per-step `setComplete` / `processed_univ` (see settlement comments in `HeapSimulation.lean`).

**Do not start Phase 4** until 3c is done or explicitly deferred.

---

## Phase 3b deliverables (complete)

| Layer | Module | Role |
|-------|--------|------|
| Verified algorithm | `Sssp.Algo.Dijkstra` | `dijkstra_correct` |
| Operational model | `Sssp.Refine.Dijkstra` | Lazy heap, mirrors Rust |
| Proof API | `Sssp.Refine.Verification` | `dijkstra_verified` |
| Regression | `Sssp.Fixtures.*` | `#guard` / CI |

```lean
theorem refine_dijkstra_correct (vg : ValidRustGraph n g) (s v : Fin n) :
  (dijkstra g s.val)[v.val]! = withTopNatToFloat (trueDistNat vg.toGraph s v)
```

---

## Deferred (blocked on Phase 3c)

| Phase | Deliverable | Blocked by |
|------:|-------------|------------|
| 4 | `Sssp.Algo.DStruct` | Phase 3c |
| 5 | `Sssp.Algo.FindPivots` | Phase 4 |
| 6 | `Sssp.Algo.BaseCase` | Phase 3c |
| 7–8 | BMSSP + Main | Phases 4–6 |
| 9 | Full-stack Rust↔Lean | Phase 3c |

---

## Regression

```bash
cd formal/lean && lake build
./formal/scripts/check-fixtures.sh
cargo test shared_json_fixtures
```
