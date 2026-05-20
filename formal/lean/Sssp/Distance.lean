/-
  Sssp.Distance

  True distance `d(v)`, the upper-bound estimate `dHat[v]`, completeness, and
  the `T(S) / T(S^*)` notations of §3.5 of the paper. These are the central
  vocabulary used in every BMSSP correctness statement.

  Mirrors §2 ("Labels Used in the Algorithm") of
  `formal/paper/source/preliminary.tex` and the `d` field of `Context` in
  `src/bmssp.rs:42`.

  Naming convention: in Lean source we write `dHat` for the paper's `d̂`
  to avoid combining-mark headaches. Documentation still uses `d̂`.
-/

import Sssp.Graph
import Sssp.Path
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.WithBot
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin

namespace Sssp

open Classical

/-- True distance from `s` to `v`: the infimum length of any walk `s ⇝ v`,
    or `+∞` if no such walk exists. -/
noncomputable def trueDist {n : ℕ} (G : Graph n) (s v : Fin n) :
    WithTop NNReal :=
  ⨅ (w : Walk G s v), (w.length : WithTop NNReal)

/-- The empty walk shows distance from `s` to itself is zero. -/
theorem trueDist_self {n : ℕ} (G : Graph n) (s : Fin n) : trueDist G s s = 0 := by
  let w : Walk G s s := ⟨[], WalkValid.nil rfl⟩
  have hlen : (w.length : WithTop NNReal) = 0 := by
    simp [w, Walk.length]
  apply le_antisymm
  · calc
      trueDist G s s ≤ (w.length : WithTop NNReal) := iInf_le _ w
      _ = 0 := hlen
  · refine le_iInf fun w' => ?_
    have h : (0 : NNReal) ≤ w'.length := zero_le _
    exact WithTop.coe_le_coe.mpr h

/-- Any walk provides an upper bound on the true distance. -/
theorem trueDist_le_walk_length {n : ℕ} (G : Graph n) (s v : Fin n) (w : Walk G s v) :
    trueDist G s v ≤ (w.length : WithTop NNReal) :=
  iInf_le _ w

/-- A single edge gives an upper bound on distance. -/
theorem trueDist_edge {n : ℕ} (G : Graph n) (u v : Fin n) (w : NNReal)
    (h : w ∈ G.edges u v) : trueDist G u v ≤ (w : WithTop NNReal) := by
  let walk : Walk G u v := ⟨[(v, w)], WalkValid.cons u v w [] h (WalkValid.nil rfl)⟩
  have hlen : walk.length = w := by
    simp [walk, Walk.length]
  simpa [hlen] using trueDist_le_walk_length G u v walk

/-- Triangle inequality for true distance. -/
theorem trueDist_triangle {n : ℕ} (G : Graph n) (s u v : Fin n) :
    trueDist G s v ≤ trueDist G s u + trueDist G u v := by
  have h1 : ∀ (w2 : Walk G u v), trueDist G s v ≤ trueDist G s u + (w2.length : WithTop NNReal) := by
    intro w2
    have concat_bound : ∀ (w1 : Walk G s u), trueDist G s v ≤
        (w1.length : WithTop NNReal) + (w2.length : WithTop NNReal) := by
      intro w1
      have h := trueDist_le_walk_length G s v (w1.append w2)
      rw [Walk.length_append] at h
      exact h
    calc
      trueDist G s v ≤ ⨅ (w1 : Walk G s u), ((w1.length : WithTop NNReal) + (w2.length : WithTop NNReal)) :=
        le_iInf concat_bound
      _ = (⨅ (w1 : Walk G s u), (w1.length : WithTop NNReal)) + (w2.length : WithTop NNReal) := by
        have h := (ENNReal.iInf_add (f := fun (w1 : Walk G s u) => (w1.length : WithTop NNReal))
          (a := (w2.length : WithTop NNReal))).symm
        simpa using h
      _ = trueDist G s u + (w2.length : WithTop NNReal) := rfl
  calc
    trueDist G s v ≤ ⨅ (w2 : Walk G u v), (trueDist G s u + (w2.length : WithTop NNReal)) :=
      le_iInf h1
    _ = trueDist G s u + ⨅ (w2 : Walk G u v), (w2.length : WithTop NNReal) := by
      have h := (ENNReal.add_iInf (a := trueDist G s u)
        (f := fun (w2 : Walk G u v) => (w2.length : WithTop NNReal))).symm
      simpa using h
    _ = trueDist G s u + trueDist G u v := rfl

/-- The estimate `d̂[v]` maintained by the algorithm. -/
abbrev DistEstimate (n : ℕ) := Fin n → WithTop NNReal

/-- Initial estimate: `d̂[s] = 0`, `d̂[v] = ∞` elsewhere. -/
noncomputable def initEstimate {n : ℕ} (s : Fin n) : DistEstimate n :=
  fun v => if v = s then ((0 : NNReal) : WithTop NNReal) else ⊤

/-- Soundness invariant maintained throughout the algorithm:
    `d̂[v] ≥ d(v)` for every `v`. -/
def Sound {n : ℕ} (G : Graph n) (s : Fin n) (dHat : DistEstimate n) : Prop :=
  ∀ v, trueDist G s v ≤ dHat v

/-- A vertex `v` is **complete** w.r.t. `dHat` iff its current estimate
    equals its true distance. -/
def IsComplete {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (v : Fin n) : Prop :=
  dHat v = trueDist G s v

/-- A set `S` is **complete** iff every vertex in `S` is complete. -/
def SetComplete {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ S, IsComplete G s dHat v

/-- `S^*` — the complete vertices of `S`. -/
noncomputable def completeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (IsComplete G s dHat)

lemma mem_completeOf_iff {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} {v : Fin n} : v ∈ completeOf G s dHat S ↔ v ∈ S ∧ IsComplete G s dHat v := by
  simp [completeOf]

lemma completeOf_subset {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} : completeOf G s dHat S ⊆ S := by
  intro v hv; rcases (mem_completeOf_iff.mp hv) with ⟨hvS, _⟩; exact hvS

/-- `T(v) = { u | d(s,u) = d(s,v) + d(v,u) }` — vertices whose unique
    shortest path from `s` passes through `v`. Under `HasDistinctLengths`
    this is exactly the subtree rooted at `v` in the shortest-path tree. -/
noncomputable def subtree {n : ℕ} (G : Graph n) (s v : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun u => trueDist G s u = trueDist G s v + trueDist G v u)

/-- `T(S) = ⋃ v ∈ S, T(v)`. -/
noncomputable def subtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  S.biUnion (subtree G s)

lemma subtreeOf_empty {n : ℕ} (G : Graph n) (s : Fin n) : subtreeOf G s ∅ = ∅ := by
  simp [subtreeOf]

/-- `T_{<B}(S) = { v ∈ T(S) : d(v) < B }`. -/
noncomputable def boundedSubtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) (B : WithTop NNReal) : Finset (Fin n) :=
  (subtreeOf G s S).filter (fun v => trueDist G s v < B)

lemma mem_boundedSubtreeOf_iff {n : ℕ} {G : Graph n} {s : Fin n}
    {S : Finset (Fin n)} {B : WithTop NNReal} {v : Fin n} :
    v ∈ boundedSubtreeOf G s S B ↔ v ∈ subtreeOf G s S ∧ trueDist G s v < B := by
  simp [boundedSubtreeOf]

lemma boundedSubtreeOf_empty {n : ℕ} (G : Graph n) (s : Fin n) (B : WithTop NNReal) :
    boundedSubtreeOf G s ∅ B = ∅ := by
  simp [boundedSubtreeOf, subtreeOf_empty]

/-- `T_{[a, b)}(S)` — the "annulus" used in the proof of Lemma 3.6 et seq. -/
noncomputable def rangeSubtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) (a b : WithTop NNReal) : Finset (Fin n) :=
  (subtreeOf G s S).filter (fun v => a ≤ trueDist G s v ∧ trueDist G s v < b)

/-- The `Ũ` of the paper (top of §3.4): vertices below `B` whose shortest
    path visits a complete vertex of `S`. Coincides with `T_{<B}(S^*)`. -/
noncomputable def expectU {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (B : WithTop NNReal) : Finset (Fin n) :=
  boundedSubtreeOf G s (completeOf G s dHat S) B

lemma mem_expectU_iff {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} {B : WithTop NNReal} {v : Fin n} :
    v ∈ expectU G s dHat S B ↔
      v ∈ subtreeOf G s (completeOf G s dHat S) ∧ trueDist G s v < B :=
  mem_boundedSubtreeOf_iff

/-- Strengthening of `HasDistinctLengths`: every pair of distinct vertices
    has distinct true distance from `s`.  The paper achieves this with
    probability 1 by sampling continuous random edge weights; we expose it
    as an explicit assumption.  This is what makes "the `k+1` closest
    vertices to `x`" a well-defined set, hence what makes the size bound
    `|U| ≤ 4k` of `baseCase` constructively provable. -/
class HasDistinctVertexDistances {n : ℕ} (G : Graph n) (s : Fin n) : Prop where
  distinct : ∀ {u v : Fin n}, u ≠ v → trueDist G s u ≠ trueDist G s v

/-! ### Truncation witness

    The combinatorial backbone of both `BaseCase` and the inductive step of
    `BMSSP`: under `HasDistinctVertexDistances`, for any frontier `S`, any
    cap `B`, and any `k * M`-sized "budget", we can pick a truncated bound
    `B' ≤ B` whose induced bounded subtree has size at most `4 * k * M`,
    *and* if we strictly cut down (`B' < B`) we kept at least `k * M`
    vertices.  This is the key fact that makes the BMSSP size bound
    (Lemma 3.10) algorithmically realisable. -/

/-- Combinatorial helper: for any `Finset α` over a linear order, the
    number of elements strictly below the `i`-th smallest is exactly
    `i`. -/
private lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (s.filter (· < s.orderEmbOfFin h i)).card = i := by
  set e := s.orderEmbOfFin h with he
  conv_lhs =>
    rw [show s = Finset.image e Finset.univ from
          (Finset.image_orderEmbOfFin_univ s h).symm]
  rw [Finset.filter_image]
  have h_filter_eq :
      ((Finset.univ : Finset (Fin k)).filter (fun a => e a < e i)) =
        (Finset.univ : Finset (Fin k)).filter (fun a => a < i) := by
    ext j; simp [e.lt_iff_lt]
  rw [h_filter_eq, Finset.card_image_of_injective _ e.injective]
  have := @Fin.card_filter_val_lt k i.val
  rw [Nat.min_eq_right (Nat.le_of_lt i.isLt)] at this
  exact this

/-- **Truncation witness.** For every frontier `S`, cap `B`, and budget
    parameters `k, M`, there exists a truncated bound `B' ≤ B` such that
    the bounded subtree below `B'` has at most `4 * k * M` vertices, and
    (if we strictly cut, `B' < B`) at least `k * M` vertices.  The proof
    is a direct order-theoretic argument on the finset of distances. -/
theorem exists_truncation_witness {n : ℕ} (G : Graph n) (s : Fin n)
    [HasDistinctVertexDistances G s]
    (k M : ℕ) (B : WithTop NNReal) (S : Finset (Fin n)) :
    ∃ B', B' ≤ B ∧
      (boundedSubtreeOf G s S B').card ≤ 4 * k * M ∧
      (B' < B → k * M ≤ (boundedSubtreeOf G s S B').card) := by
  set T := boundedSubtreeOf G s S B with hT_def
  by_cases h_small : T.card ≤ 4 * k * M
  · -- Case A: T already fits; take `B' := B`, in which case `T_{<B} = T`.
    refine ⟨B, le_refl _, ?_, ?_⟩
    · simpa [hT_def] using h_small
    · intro h_lt; exact absurd h_lt (lt_irrefl _)
  · -- Case B: `T.card > 4 * k * M`.  Sort distances and pick the
    -- `(k * M)`-th smallest as the new bound.
    have h_small : 4 * k * M < T.card := Nat.lt_of_not_le h_small
    set f : Fin n → WithTop NNReal := trueDist G s with hf_def
    set DT : Finset (WithTop NNReal) := T.image f with hDT_def
    -- Distinct vertex distances ⇒ `f` is injective on `T`.
    have h_inj_on : Set.InjOn f (T : Set (Fin n)) := by
      intro u _ v _ h_eq
      by_contra h_ne
      exact (HasDistinctVertexDistances.distinct h_ne) h_eq
    have hDT_card : DT.card = T.card := Finset.card_image_of_injOn h_inj_on
    have h_kM_le_4kM : k * M ≤ 4 * k * M := by
      have : k * M ≤ 4 * (k * M) := Nat.le_mul_of_pos_left _ (by norm_num)
      simpa [Nat.mul_assoc] using this
    have h_kM_lt_card : k * M < DT.card := by
      rw [hDT_card]; exact lt_of_le_of_lt h_kM_le_4kM h_small
    set B' : WithTop NNReal := DT.orderEmbOfFin rfl ⟨k * M, h_kM_lt_card⟩ with hB'_def
    -- `B'` is a real distance to some `v ∈ T`, hence `B' < B`.
    have hB'_in_DT : B' ∈ DT := Finset.orderEmbOfFin_mem DT rfl _
    rw [hDT_def, Finset.mem_image] at hB'_in_DT
    obtain ⟨v, hv_in_T, hv_eq⟩ := hB'_in_DT
    have hv_lt_B : f v < B := by
      rw [hT_def, mem_boundedSubtreeOf_iff] at hv_in_T; exact hv_in_T.2
    have hB'_lt_B : B' < B := by rw [← hv_eq]; exact hv_lt_B
    have hB'_le_B : B' ≤ B := le_of_lt hB'_lt_B
    -- Cardinalities transfer through the bijection `T ↔ DT`.
    have h_T_filter_card : (T.filter (fun v => f v < B')).card = k * M := by
      have h_image_eq :
          DT.filter (· < B') = (T.filter (fun v => f v < B')).image f := by
        rw [hDT_def, Finset.filter_image]
      have h_card_eq :
          (DT.filter (· < B')).card = (T.filter (fun v => f v < B')).card := by
        rw [h_image_eq]
        apply Finset.card_image_of_injOn
        intro u hu v hv h_uv_eq
        simp at hu hv
        exact h_inj_on hu.1 hv.1 h_uv_eq
      rw [← h_card_eq]
      exact card_filter_lt_orderEmbOfFin DT rfl ⟨k * M, h_kM_lt_card⟩
    -- The filter equals `boundedSubtreeOf G s S B'` because `B' ≤ B`.
    have h_filter_eq :
        T.filter (fun v => f v < B') = boundedSubtreeOf G s S B' := by
      rw [hT_def]
      ext u
      rw [Finset.mem_filter, mem_boundedSubtreeOf_iff, mem_boundedSubtreeOf_iff]
      refine ⟨fun ⟨⟨h_sub, _⟩, h_lt_B'⟩ => ⟨h_sub, h_lt_B'⟩, ?_⟩
      intro ⟨h_sub, h_lt_B'⟩
      exact ⟨⟨h_sub, lt_of_lt_of_le h_lt_B' hB'_le_B⟩, h_lt_B'⟩
    have h_card_BS : (boundedSubtreeOf G s S B').card = k * M := by
      rw [← h_filter_eq, h_T_filter_card]
    refine ⟨B', hB'_le_B, ?_, ?_⟩
    · rw [h_card_BS]; exact h_kM_le_4kM
    · intro _; rw [h_card_BS]

end Sssp
