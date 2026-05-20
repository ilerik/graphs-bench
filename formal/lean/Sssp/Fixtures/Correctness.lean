/-
  Sssp.Fixtures.Correctness

  Phase 3 Dijkstra completeness: ties together the verified algorithm,
  operational Refine model, CSR bridge, and shared JSON fixtures.
-/

import Sssp.Fixtures.Dijkstra
import Sssp.Refine.Bridge

namespace Sssp
namespace Fixtures

open Sssp Algo Refine

/-- Verified `n`-round relaxation computes true shortest-path distance. -/
theorem dijkstra_verified {n : ℕ} (G : Graph n) (s v : Fin n) :
    Algo.dijkstra G s v = trueDist G s v := by
  rw [dijkstra_correct, dijkstraSpec_correct]

/-- All four shared JSON fixtures: Refine heap Dijkstra matches expected vectors. -/
theorem refine_dijkstra_all_fixtures :
    distsMatch (Refine.dijkstra tinyChainRust 0) tinyChainExpected ∧
    distsMatch (Refine.dijkstra diamondRust 0) diamondExpected ∧
    distsMatch (Refine.dijkstra unreachableRust 0) unreachableExpected ∧
    distsMatch (Refine.dijkstra singleVertexRust 0) singleVertexExpected := by
  native_decide

/-!
  **Phase 3 Dijkstra is complete** when the following hold jointly:

  1. `dijkstra_verified` — `Sssp.Algo.dijkstra` = `trueDist` (proved).
  2. `refine_dijkstra_all_fixtures` — `Sssp.Refine.dijkstra` matches JSON vectors.
  3. `Sssp.Refine.Bridge` — CSR/multiset topology aligned on fixtures.
  4. Rust `cargo test shared_json_fixtures` — same JSON files (see CI).

  The lazy-heap step lemmas live in `Sssp.Refine.Dijkstra`
  (`dijkstraStep_stale`, `dijkstraStep_fresh`).  A general Refine ≡ Algo
  refinement proof remains Phase 9 work.
-/

end Fixtures
end Sssp
