# Future work

## Current priority: Phase 3c — zero axioms for Dijkstra

Phase 3b is **done**: `refine_dijkstra_correct` on every `ValidRustGraph`.
See `formal/VERIFICATION.md` for the full stack diagram and elimination order.

**Phase 3c goal:** replace all trusted axioms in the Dijkstra proof chain, then
document Rust refinement for `src/dijkstra.rs`.

| Step | Target | Module |
|------|--------|--------|
| 3c.1 | `nnrealToFloat_add_weight`, float order lemmas | `NumericBridge` |
| 3c.2 | `floatRelax*_aligned` (3 axioms) | `RelaxBridge` |
| 3c.3 | `outEdge_floatWeight_preimage` | `GraphBridge` |
| 3c.4 | `dijkstraHeap_eq_dijkstraRelax` | `HeapBridge` |
| 3c.5 | Rust ↔ `Refine.dijkstra` refinement note | `src/dijkstra.rs` |

**Proved recently:** fixture `ValidRustGraph`, `nnrealToFloat_add_weight_ofNat`,
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
