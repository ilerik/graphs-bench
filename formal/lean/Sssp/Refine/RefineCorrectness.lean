/-
  Sssp.Refine.RefineCorrectness

  Main Phase 3b theorem: operational `Refine.dijkstra` (lazy heap) matches verified
  `Sssp.Algo.dijkstra` (hence `trueDist`) on every valid `RustGraph`.
-/

import Sssp.Refine.HeapBridge

namespace Sssp
namespace Refine

open Sssp Algo Fixtures FloatNat

variable {n : ℕ} {g : RustGraph}

/-- **Phase 3b:** relaxation-model distances match `withTopNatToFloat (trueDistNat …)`. -/
theorem refine_dijkstraRelax_correct (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! = withTopNatToFloat (trueDistNat vg.toGraph s v) := by
  rw [dijkstraRelax_dist_eq_nnreal, trueDistNat_toFloat]

/-- **Phase 3b (heap):** lazy-heap `dijkstra` matches `trueDistNat` on every valid graph. -/
theorem refine_dijkstra_correct (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstra g s.val)[v.val]! = withTopNatToFloat (trueDistNat vg.toGraph s v) := by
  rw [dijkstra_get_eq_dijkstraRelax vg s v, refine_dijkstraRelax_correct vg s v]

theorem refine_dijkstra_nnreal (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! = nnrealToFloat (Algo.dijkstra vg.toGraph s v) :=
  dijkstraRelax_dist_eq_nnreal vg s v

theorem refine_dijkstra_trueDist (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! = nnrealToFloat (trueDist vg.toGraph s v) := by
  rw [dijkstraRelax_dist_eq_nnreal, dijkstra_correct, dijkstraSpec_correct]

theorem refine_dijkstra_sound (vg : ValidRustGraph n g) (s v : Fin n) :
    nnrealToFloat (trueDist vg.toGraph s v) ≤ (dijkstraRelax g s.val)[v.val]! := by
  calc
    nnrealToFloat (trueDist vg.toGraph s v) ≤ nnrealToFloat (Algo.dijkstra vg.toGraph s v) :=
      nnrealToFloat_monotone (dijkstra_ge_trueDist (G := vg.toGraph) (s := s) (v := v))
    _ = (dijkstraRelax g s.val)[v.val]! := (dijkstraRelax_dist_eq_nnreal vg s v).symm

theorem refine_dijkstra_complete (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! ≤ nnrealToFloat (Algo.dijkstra vg.toGraph s v) :=
  dijkstraRelax_dist_eq_nnreal vg s v ▸ float_le_refl _

theorem refine_dijkstra_sound_nat (vg : ValidRustGraph n g) (s v : Fin n) :
    withTopNatToFloat (trueDistNat vg.toGraph s v) ≤ (dijkstraRelax g s.val)[v.val]! := by
  rw [refine_dijkstraRelax_correct vg s v]
  exact float_le_refl _

theorem refine_dijkstra_correct_fixtures :
    (dijkstra tinyChainRust 0)[3]! = withTopNatToFloat (trueDistNat tinyChainValid.toGraph 0 3) ∧
    (dijkstra diamondRust 0)[3]! = withTopNatToFloat (trueDistNat diamondValid.toGraph 0 3) ∧
    (dijkstra unreachableRust 0)[2]! = withTopNatToFloat (trueDistNat unreachableValid.toGraph 0 2) ∧
    (dijkstra singleVertexRust 0)[0]! = withTopNatToFloat (trueDistNat singleVertexValid.toGraph 0 0) :=
  ⟨refine_dijkstra_correct tinyChainValid 0 3,
   refine_dijkstra_correct diamondValid 0 3,
   refine_dijkstra_correct unreachableValid 0 2,
   refine_dijkstra_correct singleVertexValid 0 0⟩

end Refine
end Sssp
