/-
  Sssp.Algo.Dijkstra

  Verified single-source shortest paths on `Graph n` with non-negative weights.

  `n` global relaxation rounds compute exact distances (`trueDist`).  On
  non-negative weights this matches Dijkstra's result.  The lazy heap code in
  `src/dijkstra.rs` is modelled in `Sssp.Refine.Dijkstra`.
-/

import Sssp.Dijkstra
import Sssp.Path

namespace Sssp
namespace Algo

variable {n : ℕ}

noncomputable def relaxAll (G : Graph n) (dHat : DistEstimate n) : DistEstimate n :=
  (Finset.univ : Finset (Fin n)).toList.foldl (fun dHat' u => relaxOutEdges G dHat' u) dHat

noncomputable def relaxRound (G : Graph n) (fuel : ℕ) (dHat : DistEstimate n) : DistEstimate n :=
  match fuel with
  | 0 => dHat
  | fuel + 1 => relaxRound G fuel (relaxAll G dHat)

noncomputable def dijkstra (G : Graph n) (s : Fin n) : DistEstimate n :=
  relaxRound G n (initEstimate s)

private lemma le_relaxEdge (dHat : DistEstimate n) (u v : Fin n) (w : NNReal) (x : Fin n) :
    (relaxEdge dHat u v w) x ≤ dHat x := by
  unfold relaxEdge
  by_cases hx : x = v
  · subst hx; simp [Function.update, le_min]
  · simp [Function.update, hx, le_min]

private lemma relaxEdge_le_add (dHat : DistEstimate n) (src tgt : Fin n) (w : NNReal) :
    (relaxEdge dHat src tgt w) tgt ≤ dHat src + (w : WithTop NNReal) := by
  simp [relaxEdge, le_min]

private lemma relaxEdge_mono (d₁ d₂ : DistEstimate n) (h : ∀ x, d₂ x ≤ d₁ x) (u tgt : Fin n)
    (w : NNReal) (x : Fin n) : (relaxEdge d₂ u tgt w) x ≤ (relaxEdge d₁ u tgt w) x := by
  unfold relaxEdge
  by_cases hx : x = tgt
  · simpa [relaxEdge, hx, Function.update, if_pos hx, le_min] using
      min_le_min (h tgt) (add_le_add_left (h u) (w : WithTop NNReal))
  · simp [relaxEdge, Function.update, hx, h]

private lemma foldl_relaxEdges_le (u : Fin n) (l : List (Fin n × NNReal)) (dHat : DistEstimate n)
    (v : Fin n) :
    (l.foldl (fun d p => relaxEdge d u p.1 p.2) dHat) v ≤ dHat v := by
  induction l generalizing dHat v with
  | nil => simp [List.foldl]
  | cons p xs ih =>
    simp [List.foldl]
    exact (ih _ _).trans (le_relaxEdge dHat u p.1 p.2 v)

private lemma foldl_relaxEdges_mono (src : Fin n) (l : List (Fin n × NNReal)) (d₁ d₂ : DistEstimate n)
    (v : Fin n) (h : ∀ x, d₂ x ≤ d₁ x) :
    (l.foldl (fun d p => relaxEdge d src p.1 p.2) d₂) v ≤
      (l.foldl (fun d p => relaxEdge d src p.1 p.2) d₁) v := by
  induction l generalizing d₁ d₂ v with
  | nil => simpa [List.foldl] using h v
  | cons p xs ih =>
    simp [List.foldl]
    have h' : ∀ x, (relaxEdge d₂ src p.1 p.2) x ≤ (relaxEdge d₁ src p.1 p.2) x :=
      fun x => relaxEdge_mono d₁ d₂ h src p.1 p.2 x
    exact ih (relaxEdge d₁ src p.1 p.2) (relaxEdge d₂ src p.1 p.2) v h'

private lemma le_relaxOutEdges {G : Graph n} (dHat : DistEstimate n) (u v : Fin n) :
    (relaxOutEdges G dHat u) v ≤ dHat v := by
  unfold relaxOutEdges
  exact foldl_relaxEdges_le u (G.outEdges u).toList dHat v

private lemma foldl_relaxOutEdges_le_add {G : Graph n} (dHat : DistEstimate n) (src tgt : Fin n)
    (w : NNReal) (l : List (Fin n × NNReal)) (h : (tgt, w) ∈ l)
    (hl : ∀ p, p ∈ l → p.2 ∈ G.edges src p.1) :
    (l.foldl (fun d p => relaxEdge d src p.1 p.2) dHat) tgt ≤ dHat src + (w : WithTop NNReal) := by
  induction l with
  | nil => simp at h
  | cons p xs ih =>
    simp only [List.foldl]
    by_cases hp : p = (tgt, w)
    · subst hp
      calc
        (xs.foldl (fun d p => relaxEdge d src p.1 p.2) (relaxEdge dHat src tgt w)) tgt
            ≤ (relaxEdge dHat src tgt w) tgt := foldl_relaxEdges_le src xs (relaxEdge dHat src tgt w) tgt
        _ ≤ dHat src + (w : WithTop NNReal) := relaxEdge_le_add _ _ _ _
    · have hxs : (tgt, w) ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd (Eq.symm h) hp
        · exact h
      calc
        (xs.foldl (fun d p => relaxEdge d src p.1 p.2) (relaxEdge dHat src p.1 p.2)) tgt
            ≤ (xs.foldl (fun d p => relaxEdge d src p.1 p.2) dHat) tgt :=
          foldl_relaxEdges_mono src xs dHat (relaxEdge dHat src p.1 p.2) tgt
            (fun x => le_relaxEdge dHat src p.1 p.2 x)
        _ ≤ dHat src + (w : WithTop NNReal) := ih hxs (fun q hq => hl q (List.mem_cons.mpr (Or.inr hq)))

private lemma relaxOutEdges_mono {G : Graph n} (d₁ d₂ : DistEstimate n) (h : ∀ x, d₂ x ≤ d₁ x)
    (u v : Fin n) : (relaxOutEdges G d₂ u) v ≤ (relaxOutEdges G d₁ u) v := by
  unfold relaxOutEdges
  exact foldl_relaxEdges_mono u (G.outEdges u).toList d₁ d₂ v h

private lemma relaxOutEdges_le_add_edge {G : Graph n} (dHat : DistEstimate n) (src tgt : Fin n)
    (w : NNReal) (h : w ∈ G.edges src tgt) :
    (relaxOutEdges G dHat src) tgt ≤ dHat src + (w : WithTop NNReal) := by
  unfold relaxOutEdges
  exact foldl_relaxOutEdges_le_add dHat src tgt w (G.outEdges src).toList
    (by simpa [Multiset.mem_toList, mem_outEdges_iff] using h)
    (fun p hp => (mem_outEdges_iff (G := G) (u := src)).mp (Multiset.mem_toList.mp hp))

private lemma foldl_relaxAll_le {G : Graph n} (us : List (Fin n)) (dHat : DistEstimate n) (v : Fin n) :
    (us.foldl (fun d u => relaxOutEdges G d u) dHat) v ≤ dHat v := by
  induction us generalizing dHat v with
  | nil => simp [List.foldl]
  | cons u us ih =>
    simp [List.foldl]
    exact (ih (relaxOutEdges G dHat u) v).trans (le_relaxOutEdges (G := G) dHat u v)

private lemma le_relaxAll {G : Graph n} (dHat : DistEstimate n) (v : Fin n) :
    (relaxAll G dHat) v ≤ dHat v :=
  foldl_relaxAll_le (Finset.univ : Finset (Fin n)).toList dHat v

private lemma foldl_relaxAll_mono {G : Graph n} (us : List (Fin n)) (d₁ d₂ : DistEstimate n)
    (v : Fin n) (h : ∀ x, d₂ x ≤ d₁ x) :
    (us.foldl (fun d u => relaxOutEdges G d u) d₂) v ≤
      (us.foldl (fun d u => relaxOutEdges G d u) d₁) v := by
  induction us generalizing d₁ d₂ v with
  | nil => simpa [List.foldl] using h v
  | cons u us ih =>
    simp [List.foldl]
    have h' : ∀ x, (relaxOutEdges G d₂ u) x ≤ (relaxOutEdges G d₁ u) x :=
      fun x => relaxOutEdges_mono (G := G) d₁ d₂ h u x
    exact ih (relaxOutEdges G d₁ u) (relaxOutEdges G d₂ u) v h'

private lemma foldl_relaxAll_le_add {G : Graph n} (dHat : DistEstimate n) (src tgt : Fin n)
    (w : NNReal) (us : List (Fin n)) (h : w ∈ G.edges src tgt) (hsrc : src ∈ us) :
    (us.foldl (fun d u => relaxOutEdges G d u) dHat) tgt ≤ dHat src + (w : WithTop NNReal) := by
  revert h hsrc
  induction us generalizing dHat with
  | nil => intro _ hsrc; simp at hsrc
  | cons u us ih =>
    intro h hsrc
    simp only [List.foldl]
    rcases List.mem_cons.mp hsrc with hhead | htail
    · subst hhead
      calc
        (us.foldl (fun d u => relaxOutEdges G d u) (relaxOutEdges G dHat src)) tgt
            ≤ (relaxOutEdges G dHat src) tgt :=
          foldl_relaxAll_le (G := G) us (relaxOutEdges G dHat src) tgt
        _ ≤ dHat src + (w : WithTop NNReal) := relaxOutEdges_le_add_edge (G := G) dHat src tgt w h
    · calc
        (us.foldl (fun d u => relaxOutEdges G d u) (relaxOutEdges G dHat u)) tgt
            ≤ relaxOutEdges G dHat u src + (w : WithTop NNReal) :=
          ih (relaxOutEdges G dHat u) h htail
        _ ≤ dHat src + (w : WithTop NNReal) :=
          add_le_add_left (le_relaxOutEdges (G := G) dHat u src) (w : WithTop NNReal)

private lemma relaxAll_le_add_edge {G : Graph n} (dHat : DistEstimate n) (src tgt : Fin n)
    (w : NNReal) (h : w ∈ G.edges src tgt) :
    (relaxAll G dHat) tgt ≤ dHat src + (w : WithTop NNReal) := by
  have hsrc : src ∈ (Finset.univ : Finset (Fin n)).toList :=
    Finset.mem_toList.mpr (Finset.mem_univ src)
  exact foldl_relaxAll_le_add dHat src tgt w (Finset.univ : Finset (Fin n)).toList h hsrc

private lemma relaxRound_le {G : Graph n} (fuel : ℕ) (dHat : DistEstimate n) (v : Fin n) :
    relaxRound G fuel dHat v ≤ dHat v := by
  induction fuel generalizing dHat v with
  | zero => simp [relaxRound]
  | succ fuel ih =>
    dsimp [relaxRound]
    exact (ih (relaxAll G dHat) v).trans (le_relaxAll (G := G) dHat v)

private theorem relaxRound_le_add_walk {G : Graph n} {src u : Fin n} (fuel : ℕ)
    (dHat : DistEstimate n) (w : Walk G src u) (hk : w.numEdges ≤ fuel) :
    relaxRound G fuel dHat u ≤ dHat src + (w.length : WithTop NNReal) := by
  induction fuel generalizing dHat w src u with
  | zero =>
    simp [relaxRound]
    have hz : w.numEdges = 0 := Nat.eq_zero_of_not_pos (Nat.not_lt.mpr hk)
    rcases w with ⟨steps, valid⟩
    have hnil : steps = [] := by
      cases steps with
      | nil => rfl
      | cons _ _ => simp [Walk.numEdges] at hz
    subst hnil
    cases valid with
    | nil h =>
      subst h
      simp [Walk.length]
  | succ fuel ih =>
    dsimp [relaxRound]
    by_cases h0 : w.numEdges = 0
    · have hu : u = src := by
        rcases w with ⟨steps, valid⟩
        have hnil : steps = [] := by
          cases steps with
          | nil => rfl
          | cons _ _ => simp [Walk.numEdges] at h0
        subst hnil
        rcases valid with ⟨h⟩
        exact h.symm
      subst hu
      have hzlen : (w.length : WithTop NNReal) = 0 := by
        rcases w with ⟨steps, valid⟩
        have hnil : steps = [] := by
          cases steps with
          | nil => rfl
          | cons _ _ => simp [Walk.numEdges] at h0
        subst hnil
        simp [Walk.length]
      calc
        relaxRound G fuel (relaxAll G dHat) u ≤ relaxAll G dHat u :=
          relaxRound_le (G := G) fuel (relaxAll G dHat) u
        _ ≤ dHat u := le_relaxAll (G := G) dHat u
        _ ≤ dHat u + (w.length : WithTop NNReal) := by rw [hzlen, add_zero]
    · obtain ⟨v, w0, w', hwsteps, h_edge⟩ := Walk.exists_first_step_tail (Nat.pos_of_ne_zero h0)
      have hk' : w'.numEdges ≤ fuel := by
        simp [Walk.numEdges, hwsteps] at hk h0 ⊢
        omega
      have hlen : (w.length : WithTop NNReal) = (w0 : WithTop NNReal) + (w'.length : WithTop NNReal) := by
        simp [Walk.length, hwsteps]
      calc
        relaxRound G fuel (relaxAll G dHat) u
            ≤ (relaxAll G dHat) v + (w'.length : WithTop NNReal) := ih (relaxAll G dHat) w' hk'
        _ ≤ dHat src + (w0 : WithTop NNReal) + (w'.length : WithTop NNReal) := by
          gcongr
          exact relaxAll_le_add_edge (G := G) dHat src v w0 h_edge
        _ = dHat src + (w.length : WithTop NNReal) := by rw [hlen, add_assoc]

private theorem relaxRound_le_initWalk {G : Graph n} {s u : Fin n} (fuel : ℕ) (w : Walk G s u)
    (hk : w.numEdges ≤ fuel) :
    relaxRound G fuel (initEstimate s) u ≤ (w.length : WithTop NNReal) := by
  have h := relaxRound_le_add_walk fuel (initEstimate s) w hk
  simpa [initEstimate_self, zero_add] using h

theorem relaxAll_sound {G : Graph n} {s : Fin n} (dHat : DistEstimate n)
    (h : Sound G s dHat) : Sound G s (relaxAll G dHat) := by
  unfold relaxAll
  revert dHat h
  induction (Finset.univ : Finset (Fin n)).toList with
  | nil => intro dHat h v; exact h v
  | cons u us ih =>
    intro dHat h v
    dsimp [List.foldl]
    exact ih (relaxOutEdges G dHat u) (relaxOutEdges_sound (G := G) (s := s) dHat h u) v

private theorem relaxRound_sound {G : Graph n} {s : Fin n} (fuel : ℕ) (dHat : DistEstimate n)
    (h : Sound G s dHat) : Sound G s (relaxRound G fuel dHat) := by
  induction fuel generalizing dHat h with
  | zero => exact h
  | succ fuel ih =>
    dsimp [relaxRound]
    exact ih (relaxAll G dHat) (relaxAll_sound dHat h)

private lemma relaxEdge_preserves_zero_at_source {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (h : dHat s = 0) (u v : Fin n) (w : NNReal) :
    (relaxEdge dHat u v w) s = 0 := by
  by_cases hv : v = s
  · subst hv
    simp [relaxEdge, h, le_min, min_eq_left (zero_le _)]
  · simp [relaxEdge, Function.update, ne_comm.mp hv, h]

private lemma relaxOutEdges_preserves_zero_at_source {G : Graph n} {s u : Fin n} {dHat : DistEstimate n}
    (h : dHat s = 0) :
    (relaxOutEdges G dHat u) s = 0 := by
  unfold relaxOutEdges
  suffices hfold : ∀ (l : List (Fin n × NNReal)) (dHat' : DistEstimate n), dHat' s = 0 →
      (l.foldl (fun d p => relaxEdge d u p.1 p.2) dHat') s = 0 by
    exact hfold _ dHat h
  intro l dHat' h'
  induction l generalizing dHat' with
  | nil => simp [List.foldl, h']
  | cons p xs ih =>
    simp only [List.foldl]
    exact ih _ (relaxEdge_preserves_zero_at_source (G := G) h' u p.1 p.2)

private lemma relaxAll_preserves_zero_at_source {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (h : dHat s = 0) : (relaxAll G dHat) s = 0 := by
  unfold relaxAll
  suffices hfold : ∀ (us : List (Fin n)) (dHat' : DistEstimate n), dHat' s = 0 →
      (us.foldl (fun d u => relaxOutEdges G d u) dHat') s = 0 by
    exact hfold _ dHat h
  intro us dHat' h'
  induction us generalizing dHat' with
  | nil => simp [List.foldl, h']
  | cons u us ih =>
    simp only [List.foldl]
    exact ih _ (relaxOutEdges_preserves_zero_at_source (G := G) h')

private lemma relaxRound_preserves_zero_at_source {G : Graph n} {s : Fin n} (fuel : ℕ)
    {dHat : DistEstimate n} (h : dHat s = 0) :
    relaxRound G fuel dHat s = 0 := by
  induction fuel generalizing dHat h with
  | zero => simpa [relaxRound]
  | succ fuel ih =>
    dsimp [relaxRound]
    exact ih (relaxAll_preserves_zero_at_source (G := G) h)

private theorem relaxRound_init_self {G : Graph n} {s : Fin n} (fuel : ℕ) :
    relaxRound G fuel (initEstimate s) s = 0 :=
  relaxRound_preserves_zero_at_source fuel (initEstimate_self (s := s))

theorem dijkstra_ge_trueDist {G : Graph n} {s v : Fin n} :
    trueDist G s v ≤ dijkstra G s v := by
  unfold dijkstra
  exact relaxRound_sound n (initEstimate s) (initEstimate_sound G s) v

theorem dijkstra_le_trueDist {G : Graph n} {s v : Fin n} :
    dijkstra G s v ≤ trueDist G s v := by
  unfold dijkstra
  by_cases h : trueDist G s v = ⊤
  · rw [h]; exact le_top
  · have hlt : trueDist G s v < ⊤ := lt_top_iff_ne_top.mpr h
    obtain ⟨w, hwlen, hwedges⟩ := exists_shortest_bounded_walk G s v hlt
    exact (relaxRound_le_initWalk n w hwedges).trans (le_of_eq hwlen)

theorem dijkstra_correct {G : Graph n} {s v : Fin n} :
    dijkstra G s v = dijkstraSpec G s v := by
  rw [dijkstraSpec]
  exact le_antisymm (dijkstra_le_trueDist (G := G) (s := s) (v := v))
    (dijkstra_ge_trueDist (G := G) (s := s) (v := v))

end Algo
end Sssp
