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
  Phase 3 regression summary (fixtures only).

  This module records what CI checks; it is **not** the all-inputs refinement
  proof.  Phase 3b (Refine ≡ Algo for every valid input) is the gate before
  Phase 4+ — see `formal/FUTURE_WORK.md`.
-/

end Fixtures
end Sssp
