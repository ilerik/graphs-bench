/-
  Sssp.Refine.Simulation

  Soundness / completeness invariants for `floatRelaxRound` (the proof-relevant
  operational Dijkstra on `RustGraph`), and heap-model regression checks.
-/

import Mathlib
import Sssp.Refine.GraphBridge
import Sssp.Refine.NumericBridge
import Sssp.Refine.RelaxBridge
import Sssp.Fixtures.Graph
import Sssp.Fixtures.Dijkstra

namespace Sssp
namespace Refine

open Sssp Algo Fixtures FloatNat

variable {n : ℕ} {g : RustGraph}

lemma initDist_length (g : RustGraph) (source : Nat) : (initDist g source).length = g.n := by
  simp [initDist]

lemma initDist_get {vg : ValidRustGraph n g} (s v : Fin n) :
    (initDist g s.val)[v.val]! = if v.val == s.val then 0.0 else distInf := by
  have hv : v.val < g.n := by rw [vg.hn]; exact v.isLt
  have hlen : v.val < (initDist g s.val).length := by simp [initDist_length, vg.hn]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp [initDist, List.getElem_map, List.getElem_range, beq_iff_eq]

def DistSound (G : Graph n) (s : Fin n) (dist : List Float) : Prop :=
  dist.length = n ∧
  ∀ v : Fin n, nnrealToFloat (trueDist G s v) ≤ dist[v.val]!

def DistComplete (G : Graph n) (s : Fin n) (dist : List Float) : Prop :=
  dist.length = n ∧
  ∀ v : Fin n, dist[v.val]! ≤ nnrealToFloat (Algo.dijkstra G s v)

theorem nnrealToFloat_zero : nnrealToFloat (0 : WithTop NNReal) = 0.0 := by
  simp [nnrealToFloat, floatWeight_zero]

theorem initDist_sound {vg : ValidRustGraph n g} (s : Fin n) :
    DistSound vg.toGraph s (initDist g s.val) := by
  constructor
  · simp [initDist_length, vg.hn]
  · intro v
    rw [initDist_get (vg := vg) s v]
    by_cases h : v.val == s.val
    · have heq : v = s := Fin.ext (beq_iff_eq.mp h)
      subst heq
      simp only [h, trueDist_self, nnrealToFloat_zero]
      exact float_le_refl _
    · have hs : v.val ≠ s.val := (beq_iff_eq.not.mp h)
      simp [hs]
      exact float_le_top _

theorem initSimInv {vg : ValidRustGraph n g} (s : Fin n) :
    SimInv vg s (initDist g s.val) (initEstimate s) where
  len := by simp [initDist_length, vg.hn]
  aligned := by
    intro v
    rw [initDist_get (vg := vg) s v]
    by_cases h : v.val == s.val
    · have heq : v = s := Fin.ext (beq_iff_eq.mp h)
      subst heq
      simp [initEstimate_self, nnrealToFloat_zero]
    · have hs : v.val ≠ s.val := (beq_iff_eq.not.mp h)
      have hv : v ≠ s := fun heq => hs (congrArg Fin.val heq)
      simp [hs, initEstimate_ne _ _ hv, nnrealToFloat_top]
  sound := initEstimate_sound vg.toGraph s

theorem floatRelaxRound_simInv (vg : ValidRustGraph n g) (s : Fin n) (fuel : Nat)
    (dist : List Float) (dHat : DistEstimate n) (h : SimInv vg s dist dHat) :
    SimInv vg s (floatRelaxRound fuel g dist) (relaxRound vg.toGraph fuel dHat) := by
  induction fuel generalizing dist dHat h with
  | zero => simpa [floatRelaxRound] using h
  | succ fuel ih =>
    dsimp [floatRelaxRound]
    exact ih (floatRelaxAll g dist) (relaxAll vg.toGraph dHat)
      (floatRelaxAll_simInv vg s dist dHat h)

theorem floatRelaxRound_sound (vg : ValidRustGraph n g) (s v : Fin n) (fuel : Nat) :
    nnrealToFloat (trueDist vg.toGraph s v) ≤ (floatRelaxRound fuel g (initDist g s.val))[v.val]! := by
  have hSim := floatRelaxRound_simInv (vg := vg) s fuel (initDist g s.val) (initEstimate s)
    (initSimInv (vg := vg) s)
  calc
    nnrealToFloat (trueDist vg.toGraph s v) ≤ nnrealToFloat (relaxRound vg.toGraph fuel (initEstimate s) v) :=
      nnrealToFloat_monotone (hSim.sound v)
    _ = (floatRelaxRound fuel g (initDist g s.val))[v.val]! := (hSim.aligned v).symm

theorem floatRelaxRound_complete (vg : ValidRustGraph n g) (s v : Fin n) :
    (floatRelaxRound n g (initDist g s.val))[v.val]! ≤ nnrealToFloat (Algo.dijkstra vg.toGraph s v) := by
  have h := (floatRelaxRound_simInv (vg := vg) s n (initDist g s.val) (initEstimate s)
    (initSimInv (vg := vg) s)).aligned v
  rw [h, Algo.dijkstra]
  exact float_le_refl _

theorem dijkstraRelax_dist_eq_nnreal (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstraRelax g s.val)[v.val]! = nnrealToFloat (Algo.dijkstra vg.toGraph s v) := by
  rw [dijkstraRelax, vg.hn]
  exact (floatRelaxRound_simInv (vg := vg) s n (initDist g s.val) (initEstimate s)
    (initSimInv (vg := vg) s)).aligned v

end Refine
end Sssp
