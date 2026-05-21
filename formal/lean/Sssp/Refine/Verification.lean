/-
  Sssp.Refine.Verification

  End-to-end Dijkstra verification API: operational heap model → `trueDistNat`.
  See `formal/VERIFICATION.md` for the full stack and axiom elimination plan.
-/

import Sssp.Refine.RefineCorrectness

namespace Sssp
namespace Refine

open Sssp Algo Fixtures FloatNat

/-- Verified shortest-path distance on the abstract `Graph n`. -/
noncomputable abbrev VerifiedDist (n : ℕ) (G : Graph n) (s v : Fin n) : WithTop Nat :=
  trueDistNat G s v

/-- Operational heap Dijkstra on a valid CSR graph refines the verified distance. -/
theorem dijkstra_verified (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstra g s.val)[v.val]! = withTopNatToFloat (VerifiedDist n vg.toGraph s v) :=
  refine_dijkstra_correct vg s v

/-- Relaxation model refines the verified distance (no heap axiom). -/
theorem dijkstraRelax_verified (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! = withTopNatToFloat (VerifiedDist n vg.toGraph s v) :=
  refine_dijkstraRelax_correct vg s v

/-- Fixture instances: heap model on shared JSON graphs. -/
theorem dijkstra_verified_fixtures :
    (dijkstra tinyChainRust 0)[3]! = withTopNatToFloat (VerifiedDist 4 tinyChainValid.toGraph 0 3) ∧
    (dijkstra diamondRust 0)[3]! = withTopNatToFloat (VerifiedDist 4 diamondValid.toGraph 0 3) ∧
    (dijkstra unreachableRust 0)[2]! = withTopNatToFloat (VerifiedDist 5 unreachableValid.toGraph 0 2) ∧
    (dijkstra singleVertexRust 0)[0]! = withTopNatToFloat (VerifiedDist 1 singleVertexValid.toGraph 0 0) :=
  refine_dijkstra_correct_fixtures

end Refine
end Sssp
