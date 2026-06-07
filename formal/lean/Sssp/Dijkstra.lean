/-
  Sssp.Dijkstra

  Specification of Dijkstra's output plus shared lemmas used by the verified
  implementation in `Sssp.Algo.Dijkstra` (`relax_sound`, `initEstimate_sound`
  in `Sssp.Distance`).

  The function `dijkstraSpec` is defined by `dijkstraSpec G s := trueDist G s`
  (i.e. it is the answer the algorithm should produce); its vacuous
  `dijkstraSpec_correct` holds by `rfl`.  Real algorithmic correctness is
  proved in `Sssp.Algo.Dijkstra`.

  Naming convention adopted in Phase 0 of the verification roadmap (see
  `formal/README.md`):

  * `<op>Spec`       — abstract input-output relation, vacuous proof.
  * `<op>Spec_*`     — corollaries about the spec.
  * `Sssp.Algo.<Op>` — real algorithm + theorem that it satisfies `<op>Spec`.
-/

import Sssp.Graph
import Sssp.Distance
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- Relax the edge `(u, v)` with weight `w` in the current estimate. -/
def relaxEdge (dHat : DistEstimate n) (u v : Fin n) (w : NNReal) : DistEstimate n :=
  Function.update dHat v (min (dHat v) (dHat u + (w : WithTop NNReal)))

/-- Relaxing a nonnegative self-loop cannot improve the source estimate. -/
lemma relaxEdge_self (dHat : DistEstimate n) (u : Fin n) (w : NNReal) :
    relaxEdge dHat u u w = dHat := by
  funext x
  by_cases hx : x = u
  · subst x
    simp [relaxEdge, Function.update]
  · simp [relaxEdge, Function.update, hx]

/-- Relaxing an outgoing edge leaves the source estimate unchanged. -/
lemma relaxEdge_source (dHat : DistEstimate n) (u v : Fin n) (w : NNReal) :
    relaxEdge dHat u v w u = dHat u := by
  by_cases h : v = u
  · subst v
    simp [relaxEdge_self]
  · have h' : u ≠ v := fun huv => h huv.symm
    simp [relaxEdge, Function.update, h']

/-- Folding relaxations over edges from one source leaves that source estimate unchanged. -/
lemma foldl_relaxEdges_source (dHat : DistEstimate n) (u : Fin n)
    (l : List (Fin n × NNReal)) :
    (l.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2) dHat) u = dHat u := by
  induction l generalizing dHat with
  | nil => rfl
  | cons p xs ih =>
    calc
      (xs.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2)
          (relaxEdge dHat u p.1 p.2)) u
          = (relaxEdge dHat u p.1 p.2) u := ih (relaxEdge dHat u p.1 p.2)
      _ = dHat u := relaxEdge_source dHat u p.1 p.2

private lemma relaxEdge_same_target_comm (dHat : DistEstimate n) (u a : Fin n)
    (wa wb : NNReal) :
    relaxEdge (relaxEdge dHat u a wa) u a wb =
      relaxEdge (relaxEdge dHat u a wb) u a wa := by
  funext x
  by_cases hx : x = a
  · subst x
    have hsrc1 : (relaxEdge dHat u a wa) u = dHat u := relaxEdge_source dHat u a wa
    have hsrc2 : (relaxEdge dHat u a wb) u = dHat u := relaxEdge_source dHat u a wb
    calc
      relaxEdge (relaxEdge dHat u a wa) u a wb a
          = min ((relaxEdge dHat u a wa) a) ((relaxEdge dHat u a wa) u + ↑wb) := by
            simp [relaxEdge, Function.update]
      _ = min (min (dHat a) (dHat u + ↑wa)) (dHat u + ↑wb) := by
            rw [hsrc1]
            simp [relaxEdge, Function.update]
      _ = min (min (dHat a) (dHat u + ↑wb)) (dHat u + ↑wa) := by
            ac_rfl
      _ = min ((relaxEdge dHat u a wb) a) ((relaxEdge dHat u a wb) u + ↑wa) := by
            rw [hsrc2]
            simp [relaxEdge, Function.update]
      _ = relaxEdge (relaxEdge dHat u a wb) u a wa a := by
            simp [relaxEdge, Function.update]
  · simp [relaxEdge, Function.update, hx]

private lemma relaxEdge_diff_target_comm (dHat : DistEstimate n) (u a b : Fin n)
    (wa wb : NNReal) (hab : a ≠ b) :
    relaxEdge (relaxEdge dHat u a wa) u b wb =
      relaxEdge (relaxEdge dHat u b wb) u a wa := by
  funext x
  by_cases hxa : x = a
  · subst x
    have hsrc : (relaxEdge dHat u b wb) u = dHat u := relaxEdge_source dHat u b wb
    have hget : (relaxEdge dHat u b wb) a = dHat a := by
      simp [relaxEdge, Function.update, hab]
    calc
      relaxEdge (relaxEdge dHat u a wa) u b wb a
          = (relaxEdge dHat u a wa) a := by
            simp [relaxEdge, Function.update, hab]
      _ = min (dHat a) (dHat u + ↑wa) := by
            simp [relaxEdge, Function.update]
      _ = min ((relaxEdge dHat u b wb) a) ((relaxEdge dHat u b wb) u + ↑wa) := by
            rw [hget, hsrc]
      _ = relaxEdge (relaxEdge dHat u b wb) u a wa a := by
            simp [relaxEdge, Function.update]
  · by_cases hxb : x = b
    · subst x
      have hsrc : (relaxEdge dHat u a wa) u = dHat u := relaxEdge_source dHat u a wa
      have hget : (relaxEdge dHat u a wa) b = dHat b := by
        simp [relaxEdge, Function.update, hxa]
      calc
        relaxEdge (relaxEdge dHat u a wa) u b wb b
            = min ((relaxEdge dHat u a wa) b) ((relaxEdge dHat u a wa) u + ↑wb) := by
              simp [relaxEdge, Function.update]
        _ = min (dHat b) (dHat u + ↑wb) := by
              rw [hget, hsrc]
        _ = (relaxEdge dHat u b wb) b := by
              simp [relaxEdge, Function.update]
        _ = relaxEdge (relaxEdge dHat u b wb) u a wa b := by
              simp [relaxEdge, Function.update, hxa]
    · simp [relaxEdge, Function.update, hxa, hxb]

/-- Relaxing two edges out of the same source is order-independent. -/
lemma relaxEdge_right_comm (dHat : DistEstimate n) (u a b : Fin n) (wa wb : NNReal) :
    relaxEdge (relaxEdge dHat u a wa) u b wb =
      relaxEdge (relaxEdge dHat u b wb) u a wa := by
  by_cases hab : a = b
  · subst b
    exact relaxEdge_same_target_comm dHat u a wa wb
  · exact relaxEdge_diff_target_comm dHat u a b wa wb hab

instance (u : Fin n) :
    RightCommutative (fun dHat' (p : Fin n × NNReal) => relaxEdge dHat' u p.1 p.2) where
  right_comm dHat p q := relaxEdge_right_comm dHat u p.1 q.1 p.2 q.2

/-- Relaxing a permuted list of edges out of one source gives the same estimate. -/
lemma foldl_relaxEdges_perm (dHat : DistEstimate n) (u : Fin n)
    {l₁ l₂ : List (Fin n × NNReal)} (hp : List.Perm l₁ l₂) :
    l₁.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2) dHat =
      l₂.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2) dHat :=
  List.Perm.foldl_eq hp dHat

/-- Relax all out-edges of `u`. -/
noncomputable def relaxOutEdges (G : Graph n) (dHat : DistEstimate n) (u : Fin n) : DistEstimate n :=
  (G.outEdges u).toList.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2) dHat

/-- Relaxing all outgoing edges leaves the source estimate unchanged. -/
lemma relaxOutEdges_source (dHat : DistEstimate n) (u : Fin n) :
    relaxOutEdges G dHat u u = dHat u := by
  unfold relaxOutEdges
  exact foldl_relaxEdges_source dHat u (G.outEdges u).toList

lemma mem_outEdges_iff {u v : Fin n} {w : NNReal} :
    (v, w) ∈ G.outEdges u ↔ w ∈ G.edges u v := by
  simp [Graph.outEdges, Multiset.mem_bind, Multiset.mem_map]

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

/-- Soundness of relaxing every out-edge of `u`. -/
theorem relaxOutEdges_sound (dHat : DistEstimate n) (h : Sound G s dHat) (u : Fin n) :
    Sound G s (relaxOutEdges G dHat u) := by
  unfold relaxOutEdges
  suffices hfold : ∀ (l : List (Fin n × NNReal)) (dHat : DistEstimate n),
      Sound G s dHat → (∀ p, p ∈ l → p ∈ G.outEdges u) →
      Sound G s (l.foldl (fun dHat' p => relaxEdge dHat' u p.1 p.2) dHat) by
    exact hfold (G.outEdges u).toList dHat h (fun p hp => Multiset.mem_toList.mp hp)
  intro l dHat h hl
  induction l generalizing dHat with
  | nil =>
    simpa [List.foldl] using h
  | cons p l ih =>
    simp only [List.foldl]
    have hmem : p.2 ∈ G.edges u p.1 :=
      (mem_outEdges_iff (G := G) (u := u)).mp (hl p (List.Mem.head l))
    have h' := relax_sound G s dHat h u p.1 p.2 hmem
    exact ih (relaxEdge dHat u p.1 p.2) h' (fun q hq => hl q (List.mem_cons.mpr (Or.inr hq)))

end Sssp
