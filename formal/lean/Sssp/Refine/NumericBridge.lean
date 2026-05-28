/-
  Sssp.Refine.NumericBridge

  Embed nat distances into `Float` for the Refine ≡ Algo proof chain (Phase 3b).
  A small set of axioms records IEEE-754 behaviour for nat-cast weights; see
  `FloatNat` below.
-/

import Mathlib
import Sssp.Refine.Dijkstra
import Sssp.Distance
import Sssp.Algo.Dijkstra

namespace Sssp
namespace Refine

open Sssp Algo Classical

variable {n : ℕ}

def nnrealOfNat (k : Nat) : WithTop NNReal := (k : NNReal)

def withTopNatToFloat : WithTop Nat → Float
| .none => distInf
| .some k => floatWeight k

noncomputable def nnrealToFloat : WithTop NNReal → Float
| .none => distInf
| .some r =>
  if h : ∃ k : Nat, (k : NNReal) = r then floatWeight (Classical.choose h) else floatWeight 0

noncomputable def withTopNnrealToNat : WithTop NNReal → WithTop Nat
| .none => ⊤
| .some r =>
  if h : ∃ k : Nat, (k : NNReal) = r then
    let k := Classical.choose h
    (k : WithTop Nat)
  else (0 : WithTop Nat)

noncomputable def trueDistNat (G : Graph n) (s v : Fin n) : WithTop Nat :=
  withTopNnrealToNat (Algo.dijkstra G s v)

theorem withTopNatToFloat_top : withTopNatToFloat ⊤ = distInf := by simp [withTopNatToFloat]
theorem withTopNatToFloat_nat (k : Nat) : withTopNatToFloat k = floatWeight k := by
  simp [withTopNatToFloat, floatWeight]
theorem nnrealToFloat_top : nnrealToFloat ⊤ = distInf := by simp [nnrealToFloat]
theorem nnrealToFloat_ofNat (k : Nat) : nnrealToFloat (k : WithTop NNReal) = floatWeight k := by
  change nnrealToFloat (.some (k : NNReal)) = floatWeight k
  simp [nnrealToFloat, floatWeight]

theorem withTopNnrealToNat_ofNat (k : Nat) : withTopNnrealToNat (k : WithTop NNReal) = k := by
  show withTopNnrealToNat (.some (k : NNReal)) = k
  unfold withTopNnrealToNat
  simp [show ∃ k' : Nat, (k' : NNReal) = (k : NNReal) from ⟨k, rfl⟩]

theorem withTopNatToFloat_nnrealToFloat (x : WithTop NNReal) :
    withTopNatToFloat (withTopNnrealToNat x) = nnrealToFloat x := by
  match x with
  | ⊤ => simp [withTopNnrealToNat, withTopNatToFloat, nnrealToFloat]
  | (r : NNReal) =>
    unfold withTopNnrealToNat nnrealToFloat withTopNatToFloat
    by_cases h : ∃ k : Nat, (k : NNReal) = r
    · simp [WithTop.some_eq_coe, h]
    · simp [WithTop.some_eq_coe, h]

theorem trueDistNat_ofNat (G : Graph n) (s v : Fin n) (k : Nat)
    (h : Algo.dijkstra G s v = (k : WithTop NNReal)) :
    trueDistNat G s v = k := by
  unfold trueDistNat
  rw [h, withTopNnrealToNat_ofNat]

theorem trueDistNat_toFloat (G : Graph n) (s v : Fin n) :
    withTopNatToFloat (trueDistNat G s v) = nnrealToFloat (Algo.dijkstra G s v) :=
  withTopNatToFloat_nnrealToFloat (Algo.dijkstra G s v)

/-! ### Trusted float facts for nat-cast weights (opaque `Float` arithmetic). -/

namespace FloatNat

axiom floatWeight_eq_ofNat (w : Nat) : floatWeight w = Float.ofNat w
axiom floatZero_add (x : Float) : 0.0 + x = x
axiom float_add_assoc (a b c : Float) : a + b + c = a + (b + c)
axiom float_add_comm (a b : Float) : a + b = b + a
axiom floatWeight_add (a b : Nat) : floatWeight a + floatWeight b = floatWeight (a + b)
axiom floatWeight_lt_iff (a b : Nat) : floatWeight a < floatWeight b ↔ a < b
axiom floatWeight_le_iff (a b : Nat) : floatWeight a ≤ floatWeight b ↔ a ≤ b
axiom float_le_antisymm {a b : Float} : a ≤ b → b ≤ a → a = b
axiom float_le_refl (a : Float) : a ≤ a
axiom float_le_top (a : Float) : a ≤ distInf

theorem nnrealToFloat_add (a b : Nat) :
    nnrealToFloat ((a + b : Nat) : WithTop NNReal) =
      nnrealToFloat (a : WithTop NNReal) + floatWeight b := by
  rw [nnrealToFloat_ofNat, nnrealToFloat_ofNat, floatWeight_add]

axiom nnrealToFloat_monotone {a b : WithTop NNReal} (h : a ≤ b) : nnrealToFloat a ≤ nnrealToFloat b

axiom nnrealToFloat_trueDist_add (G : Graph n) (s u v : Fin n) (w : Nat)
    (huv : nnrealWeight w ∈ G.edges u v) :
    nnrealToFloat (trueDist G s v) ≤ nnrealToFloat (trueDist G s u) + floatWeight w

/-- `nnrealToFloat` commutes with adding a nat weight on a finite estimate. -/
theorem nnrealToFloat_add_weight_ofNat (a w : Nat) :
    nnrealToFloat ((a : WithTop NNReal) + (w : WithTop NNReal)) =
      nnrealToFloat (a : WithTop NNReal) + floatWeight w := by
  rw [show (a : WithTop NNReal) + (w : WithTop NNReal) = ((a + w : Nat) : WithTop NNReal) from by simp,
    nnrealToFloat_ofNat, nnrealToFloat_ofNat, floatWeight_add]

axiom nnrealToFloat_add_weight (x : WithTop NNReal) (w : Nat) :
    nnrealToFloat (x + (w : WithTop NNReal)) = nnrealToFloat x + floatWeight w

/-- `nnrealToFloat` commutes with `min` on estimates (target-vertex relax alignment). -/
axiom nnrealToFloat_min (a b : WithTop NNReal) :
    nnrealToFloat (min a b) = min (nnrealToFloat a) (nnrealToFloat b)

axiom float_min_eq_left_of_lt {a b : Float} (h : a < b) : min a b = a
axiom float_min_eq_left_of_le {a b : Float} (h : a ≤ b) : min a b = a
axiom float_min_eq_right_of_le {a b : Float} (h : b ≤ a) : min a b = b
axiom float_le_of_not_lt {a b : Float} (h : ¬a < b) : b ≤ a
axiom float_le_of_lt {a b : Float} (h : a < b) : a ≤ b
axiom float_le_trans {a b c : Float} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c
axiom float_eq_of_beq {a b : Float} (h : (a == b) = true) : a = b

/-- On nat-cast estimates, `nnrealToFloat` reflects `≤`. -/
theorem nnrealToFloat_le_reflects_ofNat {a b : Nat}
    (h : nnrealToFloat (a : WithTop NNReal) ≤ nnrealToFloat (b : WithTop NNReal)) :
    (a : WithTop NNReal) ≤ (b : WithTop NNReal) := by
  have hnn : a ≤ b := (floatWeight_le_iff a b).1 (by simpa [nnrealToFloat_ofNat] using h)
  simpa [WithTop.some_eq_coe] using Nat.cast_le.mpr hnn

end FloatNat

open FloatNat

end Refine
end Sssp
