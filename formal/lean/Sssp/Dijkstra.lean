/-
  Sssp.Dijkstra

  **Status: SPECIFICATION ONLY — not the verified algorithm.**

  This file states what Dijkstra's algorithm is *supposed* to compute and
  proves the relaxation soundness lemma.  The function `dijkstraSpec` is
  defined by `dijkstraSpec G s := trueDist G s` (i.e. it is the answer the
  algorithm should produce) and `dijkstraSpec_correct` therefore holds by
  `rfl` — no algorithm is verified by this file.

  The honest, computable implementation of Dijkstra lives in
  `Sssp.Algo.Dijkstra` and is proven correct against this specification
  there.

  Naming convention adopted in Phase 0 of the verification roadmap (see
  `formal/README.md`):

  * `<op>Spec`       — abstract input-output relation, vacuous proof.
  * `<op>Spec_*`     — corollaries about the spec.
  * `Sssp.Algo.<Op>` — real algorithm + theorem that it satisfies `<op>Spec`.
-/

import Sssp.Graph
import Sssp.Distance
import Mathlib.Data.NNReal.Basic

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- **Specification (oracle) of Dijkstra.**  Returns `trueDist G s` by
    definition; the actual heap-based algorithm lives in `Sssp.Algo.Dijkstra`.
    This definition is `noncomputable` because `trueDist` is. -/
noncomputable def dijkstraSpec (G : Graph n) (s : Fin n) : DistEstimate n :=
  trueDist G s

/-- The specification matches `trueDist` by construction.  Holds by `rfl`. -/
theorem dijkstraSpec_correct :
    ∀ v, dijkstraSpec G s v = trueDist G s v := by
  intro v; rfl

/-- Soundness of the edge-relaxation primitive used by every shortest-path
    algorithm in this development.  Relaxing the edge `(u, v)` against the
    current estimate never breaks the invariant `dHat ≥ trueDist`. -/
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
