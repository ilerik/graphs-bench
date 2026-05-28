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
  (List.finRange n).foldl (fun dHat' u => relaxOutEdges G dHat' u) dHat

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

theorem le_relaxOutEdges {G : Graph n} (dHat : DistEstimate n) (u v : Fin n) :
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

theorem relaxOutEdges_mono {G : Graph n} (d₁ d₂ : DistEstimate n) (h : ∀ x, d₂ x ≤ d₁ x)
    (u v : Fin n) : (relaxOutEdges G d₂ u) v ≤ (relaxOutEdges G d₁ u) v := by
  unfold relaxOutEdges
  exact foldl_relaxEdges_mono u (G.outEdges u).toList d₁ d₂ v h

private lemma relaxEdge_mono_le (d₁ d₂ : DistEstimate n) (h : ∀ x, d₁ x ≤ d₂ x) (u tgt : Fin n)
    (w : NNReal) (x : Fin n) : (relaxEdge d₁ u tgt w) x ≤ (relaxEdge d₂ u tgt w) x := by
  unfold relaxEdge
  by_cases hx : x = tgt
  · simpa [relaxEdge, hx, Function.update, if_pos hx, le_min] using
      min_le_min (h tgt) (add_le_add_left (h u) (w : WithTop NNReal))
  · simp [relaxEdge, Function.update, hx, h]

theorem relaxOutEdges_mono_le {G : Graph n} {d₁ d₂ : DistEstimate n} (h : ∀ x, d₁ x ≤ d₂ x)
    (u v : Fin n) : (relaxOutEdges G d₁ u) v ≤ (relaxOutEdges G d₂ u) v := by
  unfold relaxOutEdges
  suffices hfold : ∀ (l : List (Fin n × NNReal)) (d₁' d₂' : DistEstimate n) (v : Fin n),
      (∀ x, d₁' x ≤ d₂' x) →
        (l.foldl (fun d p => relaxEdge d u p.1 p.2) d₁') v ≤
          (l.foldl (fun d p => relaxEdge d u p.1 p.2) d₂') v by
    exact hfold (G.outEdges u).toList d₁ d₂ v h
  intro l d₁' d₂' v h'
  induction l generalizing d₁' d₂' v with
  | nil => simpa [List.foldl] using h' v
  | cons p xs ih =>
    simp [List.foldl]
    have h'edge : ∀ x, (relaxEdge d₁' u p.1 p.2) x ≤ (relaxEdge d₂' u p.1 p.2) x :=
      fun x => relaxEdge_mono_le d₁' d₂' h' u p.1 p.2 x
    exact ih (relaxEdge d₁' u p.1 p.2) (relaxEdge d₂' u p.1 p.2) v h'edge

theorem relaxOutEdges_le_add_edge {G : Graph n} (dHat : DistEstimate n) (src tgt : Fin n)
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

theorem le_relaxAll {G : Graph n} (dHat : DistEstimate n) (v : Fin n) :
    (relaxAll G dHat) v ≤ dHat v :=
  foldl_relaxAll_le (List.finRange n) dHat v

private theorem foldl_relaxAll_le_relaxOutEdges_at {G : Graph n} (us : List (Fin n))
    (dHat : DistEstimate n) (u : Fin n) (hu : u ∈ us) (v : Fin n) :
    (us.foldl (fun d u' => relaxOutEdges G d u') dHat) v ≤ (relaxOutEdges G dHat u) v := by
  induction us generalizing dHat u v with
  | nil => cases hu
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hx : x = u
    · subst hx
      exact foldl_relaxAll_le (G := G) xs (relaxOutEdges G dHat x) v
    · have hne : u ≠ x := fun heq => hx heq.symm
      have hu' : u ∈ xs := by
        rcases List.mem_cons.mp hu with h | h
        · exact absurd h hne
        · exact h
      calc
        (xs.foldl (fun d u' => relaxOutEdges G d u') (relaxOutEdges G dHat x)) v
            ≤ (relaxOutEdges G (relaxOutEdges G dHat x) u) v :=
          ih (relaxOutEdges G dHat x) u hu' v
        _ ≤ (relaxOutEdges G dHat u) v := by
          have hmono : ∀ w, (relaxOutEdges G dHat x) w ≤ dHat w :=
            fun w => le_relaxOutEdges (G := G) dHat x w
          exact relaxOutEdges_mono (G := G) dHat (relaxOutEdges G dHat x) hmono u v

/-- One full `relaxAll` pass is at least as tight as relaxing a single vertex. -/
theorem relaxAll_le_relaxOutEdges {G : Graph n} (dHat : DistEstimate n) (u v : Fin n) :
    (relaxAll G dHat) v ≤ (relaxOutEdges G dHat u) v := by
  unfold relaxAll
  exact foldl_relaxAll_le_relaxOutEdges_at (List.finRange n) dHat u (List.mem_finRange u) v

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

theorem relaxAll_mono {G : Graph n} {d₁ d₂ : DistEstimate n} (h : ∀ x, d₂ x ≤ d₁ x)
    (v : Fin n) : (relaxAll G d₂) v ≤ (relaxAll G d₁) v :=
  foldl_relaxAll_mono (G := G) (List.finRange n) d₁ d₂ v h

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
  have hsrc : src ∈ List.finRange n := List.mem_finRange src
  exact foldl_relaxAll_le_add dHat src tgt w (List.finRange n) h hsrc

private lemma relaxRound_le {G : Graph n} (fuel : ℕ) (dHat : DistEstimate n) (v : Fin n) :
    relaxRound G fuel dHat v ≤ dHat v := by
  induction fuel generalizing dHat v with
  | zero => simp [relaxRound]
  | succ fuel ih =>
    dsimp [relaxRound]
    exact (ih (relaxAll G dHat) v).trans (le_relaxAll (G := G) dHat v)

private lemma relaxRound_mono_aux (G : Graph n) :
    ∀ (fuel : ℕ) (d₁ d₂ : DistEstimate n), (∀ x, d₂ x ≤ d₁ x) → ∀ v,
      relaxRound G fuel d₂ v ≤ relaxRound G fuel d₁ v
  | 0, d₁, d₂, h, v => h v
  | fuel + 1, d₁, d₂, h, v => by
      dsimp [relaxRound]
      have hAll : ∀ x, (relaxAll G d₂) x ≤ (relaxAll G d₁) x :=
        fun x => relaxAll_mono (G := G) (d₁ := d₁) (d₂ := d₂) h x
      exact relaxRound_mono_aux G fuel (relaxAll G d₁) (relaxAll G d₂) hAll v

theorem relaxRound_mono {G : Graph n} {d₁ d₂ : DistEstimate n} (fuel : ℕ)
    (h : ∀ x, d₂ x ≤ d₁ x) (v : Fin n) :
    relaxRound G fuel d₂ v ≤ relaxRound G fuel d₁ v :=
  relaxRound_mono_aux G fuel d₁ d₂ h v

theorem relaxRound_succ_le {G : Graph n} (fuel : ℕ) (dHat : DistEstimate n) (v : Fin n) :
    relaxRound G (fuel + 1) dHat v ≤ relaxRound G fuel dHat v := by
  dsimp [relaxRound]
  exact relaxRound_mono (G := G) (fuel := fuel) (d₁ := dHat) (d₂ := relaxAll G dHat)
    (fun x => le_relaxAll (G := G) dHat x) v

theorem relaxRound_ge_le {G : Graph n} {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂)
    (dHat : DistEstimate n) (v : Fin n) :
    relaxRound G fuel₂ dHat v ≤ relaxRound G fuel₁ dHat v := by
  induction h with
  | refl => rfl
  | @step fuel h ih =>
    exact (relaxRound_succ_le (G := G) fuel dHat v).trans ih

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
  induction List.finRange n with
  | nil => intro dHat h v; exact h v
  | cons u us ih =>
    intro dHat h v
    dsimp [List.foldl]
    exact ih (relaxOutEdges G dHat u) (relaxOutEdges_sound (G := G) (s := s) dHat h u) v

theorem relaxRound_sound {G : Graph n} {s : Fin n} (fuel : ℕ) (dHat : DistEstimate n)
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

theorem relaxOutEdges_preserves_zero_at_source {G : Graph n} {s u : Fin n} {dHat : DistEstimate n}
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

private lemma trueDist_le_add_edge {G : Graph n} {s src tgt : Fin n} {dHat : DistEstimate n}
    (hSound : Sound G s dHat) (w : NNReal) (h : w ∈ G.edges src tgt) :
    trueDist G s tgt ≤ dHat src + (w : WithTop NNReal) := by
  calc
    trueDist G s tgt ≤ trueDist G s src + trueDist G src tgt := trueDist_triangle G s src tgt
    _ ≤ dHat src + trueDist G src tgt := add_le_add_left (hSound src) _
    _ ≤ dHat src + (w : WithTop NNReal) := add_le_add_right (trueDist_edge G src tgt w h) _

private lemma relaxEdge_self_eq_of_all_complete {G : Graph n} {s u tgt : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ x, IsComplete G s dHat x) (hSound : Sound G s dHat)
    (w : NNReal) (h : w ∈ G.edges u tgt) :
    (relaxEdge dHat u tgt w) tgt = dHat tgt := by
  have hget : (relaxEdge dHat u tgt w) tgt = min (dHat tgt) (dHat u + (w : WithTop NNReal)) := by
    simp [relaxEdge, Function.update_self]
  rw [hget, (hComplete tgt)]
  exact min_eq_left (trueDist_le_add_edge (G := G) (s := s) hSound w h)

private lemma relaxEdge_eq_of_all_complete {G : Graph n} {s u : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ x, IsComplete G s dHat x) (hSound : Sound G s dHat)
    (tgt : Fin n) (w : NNReal) (h : w ∈ G.edges u tgt) :
    relaxEdge dHat u tgt w = dHat := by
  ext x
  by_cases hx : x = tgt
  · rw [hx, relaxEdge_self_eq_of_all_complete (G := G) (s := s) hComplete hSound w h]
  · simp [relaxEdge, Function.update, hx]

private lemma foldl_relaxOutEdges_eq_of_all_complete {G : Graph n} {s u : Fin n}
    {dHat : DistEstimate n} (hComplete : ∀ x, IsComplete G s dHat x) (hSound : Sound G s dHat)
    (l : List (Fin n × NNReal)) (hl : ∀ p, p ∈ l → p ∈ G.outEdges u) :
    (l.foldl (fun d p => relaxEdge d u p.1 p.2) dHat) = dHat := by
  induction l with
  | nil => rfl
  | cons p xs ih =>
    simp only [List.foldl]
    have hmem : p.2 ∈ G.edges u p.1 :=
      (Sssp.mem_outEdges_iff (G := G) (u := u)).mp (hl p (List.Mem.head xs))
    rw [relaxEdge_eq_of_all_complete (G := G) (s := s) hComplete hSound p.1 p.2 hmem]
    exact ih (fun q hq => hl q (List.mem_cons.mpr (Or.inr hq)))

theorem relaxOutEdges_eq_of_all_complete {G : Graph n} {s u : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ x, IsComplete G s dHat x) (hSound : Sound G s dHat) :
    relaxOutEdges G dHat u = dHat := by
  unfold relaxOutEdges
  exact foldl_relaxOutEdges_eq_of_all_complete (G := G) (s := s) hComplete hSound
    (G.outEdges u).toList (fun p hp => Multiset.mem_toList.mp hp)

private lemma foldl_relaxAll_eq_of_all_complete {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ x, IsComplete G s dHat x) (hSound : Sound G s dHat)
    (us : List (Fin n)) :
    (us.foldl (fun d u => relaxOutEdges G d u) dHat) = dHat := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [List.foldl]
    rw [relaxOutEdges_eq_of_all_complete (G := G) (s := s) hComplete hSound]
    exact ih

/-- When every vertex is complete, a full `relaxAll` pass is a no-op. -/
theorem relaxAll_idempotent_of_all_complete {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ v, IsComplete G s dHat v) (hSound : Sound G s dHat) :
    relaxAll G dHat = dHat := by
  unfold relaxAll
  exact foldl_relaxAll_eq_of_all_complete (G := G) (s := s) hComplete hSound (List.finRange n)

private theorem relaxRound_eq_of_all_complete {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hComplete : ∀ v, IsComplete G s dHat v) (hSound : Sound G s dHat) :
    ∀ fuel, relaxRound G fuel dHat = dHat
  | 0 => rfl
  | fuel + 1 => by
      dsimp [relaxRound]
      rw [relaxAll_idempotent_of_all_complete (G := G) (s := s) hComplete hSound]
      exact relaxRound_eq_of_all_complete (G := G) (s := s) hComplete hSound fuel

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

/-- After `n` rounds from `initEstimate`, further rounds change nothing. -/
theorem relaxRound_ge_n_eq {G : Graph n} {s : Fin n} (fuel : ℕ) (h : n ≤ fuel) :
    relaxRound G fuel (initEstimate s) = relaxRound G n (initEstimate s) := by
  ext v
  apply le_antisymm
  · exact relaxRound_ge_le h (initEstimate s) v
  · have heq : relaxRound G n (initEstimate s) v = trueDist G s v := by
      change dijkstra G s v = trueDist G s v
      rw [dijkstra_correct, dijkstraSpec_correct]
    rw [heq]
    exact relaxRound_sound fuel (initEstimate s) (initEstimate_sound G s) v

end Algo
end Sssp
