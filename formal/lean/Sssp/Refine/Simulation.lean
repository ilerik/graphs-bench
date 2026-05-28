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
  have hlen : v.val < (initDist g s.val).length := by simpa [initDist_length, vg.hn] using hv
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp [initDist, List.getElem_map, List.getElem_range, hv, beq_iff_eq]

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
  · simp [DistSound, initDist_length, vg.hn]
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
      simp [h, initEstimate_self, nnrealToFloat_zero]
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

/-- Two distance lists carrying the same `SimInv` estimate agree pointwise, hence as lists. -/
private theorem simInv_get_eq {vg : ValidRustGraph n g} {s : Fin n}
    {d1 d2 : List Float} {dHat : DistEstimate n}
    (h1 : SimInv vg s d1 dHat) (h2 : SimInv vg s d2 dHat) (v : Fin n) :
    d1[v.val]! = d2[v.val]! := by
  rw [h1.aligned v, h2.aligned v]

private theorem getElem_eq_getElem! {l : List Float} {i : Nat} (hi : i < l.length) :
    l[i]'hi = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem getElem_eq_of_getElem! {l1 l2 : List Float} {i : Nat} (hi : i < l1.length)
    (hlen : l1.length = l2.length) (h : l1[i]! = l2[i]!) :
    l1[i]'hi = l2[i]'(hlen ▸ hi) :=
  (getElem_eq_getElem! hi).trans (h.trans (getElem_eq_getElem! (hlen ▸ hi)).symm)

theorem simInv_dist_eq {vg : ValidRustGraph n g} {s : Fin n}
    {d1 d2 : List Float} {dHat : DistEstimate n}
    (h1 : SimInv vg s d1 dHat) (h2 : SimInv vg s d2 dHat) :
    d1 = d2 := by
  refine List.ext_getElem (by rw [h1.len, h2.len]) fun i hi _ => by
    have hi' : i < n := lt_of_lt_of_eq hi h1.len
    exact getElem_eq_of_getElem! hi (h1.len.trans h2.len.symm)
      (simInv_get_eq (vg := vg) (s := s) h1 h2 ⟨i, hi'⟩)

theorem dist_eq_of_simInv_dHat_eq {vg : ValidRustGraph n g} {s : Fin n}
    {d1 d2 : List Float} {dHat1 dHat2 : DistEstimate n}
    (heq : dHat1 = dHat2) (h1 : SimInv vg s d1 dHat1) (h2 : SimInv vg s d2 dHat2) :
    d1 = d2 := by
  subst heq
  exact simInv_dist_eq h1 h2

/-- Equal float distances when both `SimInv` estimates are complete at every vertex. -/
theorem dist_eq_of_simInv_both_complete {vg : ValidRustGraph n g} {s : Fin n}
    {d1 d2 : List Float} {dHat1 dHat2 : DistEstimate n}
    (h1 : SimInv vg s d1 dHat1) (h2 : SimInv vg s d2 dHat2)
    (hc1 : ∀ v, IsComplete vg.toGraph s dHat1 v)
    (hc2 : ∀ v, IsComplete vg.toGraph s dHat2 v) :
    d1 = d2 := by
  refine List.ext_getElem (by rw [h1.len, h2.len]) ?_
  intro i hi _
  have hi' : i < n := lt_of_lt_of_eq hi h1.len
  let v : Fin n := ⟨i, hi'⟩
  exact getElem_eq_of_getElem! hi (h1.len.trans h2.len.symm)
    (by rw [h1.aligned v, h2.aligned v, hc1 v, hc2 v])

theorem relaxRound_n_all_complete (G : Graph n) (s : Fin n) (v : Fin n) :
    IsComplete G s (relaxRound G n (initEstimate s)) v := by
  simpa [Algo.dijkstra] using
    (Algo.dijkstra_correct (G := G) (s := s) (v := v)).trans (dijkstraSpec_correct G s v)

end Refine
end Sssp
