# Rust ↔ Lean refinement: lazy-heap Dijkstra (Phase 3c.5)

This note maps `src/dijkstra.rs` to `Sssp.Refine.Dijkstra` / `HeapSimulation` for reviewers and future linking work.

## Operational correspondence

| Rust (`src/dijkstra.rs`) | Lean (`Sssp.Refine.Dijkstra`) |
|--------------------------|-------------------------------|
| `Vec<f64>` distances, `distInf` / `∞` for unreachable | `List Float` via `initDist`, `distInf` |
| `BinaryHeap<HeapItem>` min-heap via negated `Ord` | `List HeapItem` + `heapPopMin` (linear scan) |
| Stale skip: `if d > dist[v] { continue }` | `distStale dist item` → `dijkstraStep_stale` |
| Relax out-edges, `heap.push` on improvement | `floatRelaxOut` + `heapPush` in `dijkstraStep_fresh` |
| Unbounded `while heap.pop()` | Fuel-bounded `dijkstraRun` with `dijkstraHeapFuel g` |

Lean uses fuel `g.n * g.edgeTo.length + g.n + 1` so the run matches the CSR edge budget used in proofs (stale pops consume fuel without relaxing).

## Proof entry points

- **Headline (unconditional on `ValidRustGraph`):** `Sssp.Refine.refine_dijkstra_correct` — still uses `axiom dijkstraHeap_eq_dijkstraRelax` in `HeapBridge`.
- **Conditional discharge:** `dijkstraHeap_eq_dijkstraRelax_of_{schedule,complete,edgeUpper,settlement}`.
- **Settlement target:** `HeapSettlement` in `HeapSimulation` bundles stale bound, `processed = univ`, `SetComplete` / `ProcessedEdgeUpper` on the run; implies `dijkstraRun_dHat_all_complete_at_heapFuel` and schedule alignment.

## Regression (not the proof)

- Lean: `Sssp.Fixtures.*` + `distsMatch` / `#guard` on fixture graphs.
- Rust: `dijkstra.rs` `fixture_tests` reads shared JSON under `fixtures/`.
- Shell: `formal/scripts/check-fixtures.sh`, `cargo test shared_json_fixtures`.

## Remaining proof work (HeapBridge)

1. `dijkstraRun_staleCount ≤ n * |edgeTo|` at `dijkstraHeapFuel` (fuel accounting is ready).
2. Per-step settlement: heap min-key ⇒ min `trueDist` outside processed set (`freshPop_isComplete_of_setComplete`).
3. Inductive `SetComplete` + `ProcessedEdgeUpper` through `dijkstraRun_processedAcc`.
4. Optional: `HasDistinctVertexDistances` on `vg.toGraph` for fixture graphs (or keep as typeclass on settlement lemmas).

Until (1–3) are proved, `HeapSettlement` documents the exact heap-side contract.
