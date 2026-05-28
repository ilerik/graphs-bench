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
| 3c.4 | `dijkstraRun_dHat_all_complete_at_heapFuel` → discharge `dijkstraHeap_eq_dijkstraRelax` via `dijkstraHeap_eq_dijkstraRelax_of_complete` | `HeapBridge` | open (1 axiom + 3 conditional theorems proved) |
| 3c.5 | Rust ↔ `Refine.dijkstra` refinement note | `src/dijkstra.rs` | not started |

**Proved recently:** `dijkstraHeap_eq_dijkstraRelax_of_{upper,complete,edgeUpper}`,
`dijkstraRun_dHat_schedule_of_{all_complete,upper}`, `dijkstraRun_processed_card_le_fuel`,
`freshPop_isComplete_of_processed_pred`, `outEdge_floatWeight_preimage`,
fixture `ValidRustGraph`, `nnrealToFloat_add_weight_ofNat`,
`floatRelaxEdge_aligned_ne`, unconditional `refine_dijkstra_correct`.

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
