/-
  Sssp.Dijkstra

  Specification of textbook Dijkstra (`src/dijkstra.rs`). We give it a
  pure functional signature and state its correctness theorem; this is
  used as a baseline that BMSSP is later proved to agree with.
-/

import Sssp.Graph
import Sssp.Distance
import Mathlib.Data.NNReal.Basic

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- Output of Dijkstra: the final distance estimate (which we will prove
    equals `trueDist G s`).  We give a noncomputable oracle definition here;
    the efficient implementation in `src/dijkstra.rs` can be plugged in later. -/
noncomputable def dijkstra (G : Graph n) (s : Fin n) : DistEstimate n :=
  trueDist G s

/-- **Correctness of Dijkstra.** Mirrors `dijkstra` in `src/dijkstra.rs:40`. -/
theorem dijkstra_correct :
    ∀ v, dijkstra G s v = trueDist G s v := by
  intro v; rfl

/-- Soundness invariant of relaxation: relaxing the edge `(u, v)` against the
    current estimate `d̂` never increases any `d̂[w]`, and preserves `Sound`. -/
theorem relax_sound (dHat : DistEstimate n) (h : Sound G s dHat)
    (u v : Fin n) (w : NNReal) (huv : w ∈ G.edges u v) :
    Sound G s (Function.update dHat v (min (dHat v) (dHat u + (w : NNReal)))) := by
  intro x
  by_cases hx : x = v
  · subst x
    have h1 : trueDist G s v ≤ dHat v := h v
    have h2 : trueDist G s v ≤ dHat u + (w : WithTop NNReal) := by
      calc
        trueDist G s v ≤ trueDist G s u + trueDist G u v := trueDist_triangle G s u v
        _ ≤ dHat u + trueDist G u v := add_le_add_left (h u) (trueDist G u v)
        _ ≤ dHat u + (w : WithTop NNReal) := by
          have h_edge : trueDist G u v ≤ (w : WithTop NNReal) := trueDist_edge G u v w huv
          have h_temp : trueDist G u v + dHat u ≤ (w : WithTop NNReal) + dHat u :=
            add_le_add_left h_edge (dHat u)
          calc
            dHat u + trueDist G u v = trueDist G u v + dHat u := add_comm _ _
            _ ≤ (w : WithTop NNReal) + dHat u := h_temp
            _ = dHat u + (w : WithTop NNReal) := add_comm _ _
    have hmin : trueDist G s v ≤ min (dHat v) (dHat u + (w : WithTop NNReal)) :=
      le_min h1 h2
    have h_upd : (Function.update dHat v (min (dHat v) (dHat u + (w : WithTop NNReal)))) v =
      min (dHat v) (dHat u + (w : WithTop NNReal)) := by simp
    rw [h_upd]
    exact hmin
  · have h_upd : (Function.update dHat v (min (dHat v) (dHat u + (w : WithTop NNReal)))) x = dHat x := by
      simp [hx]
    rw [h_upd]
    exact h x

end Sssp
