/-
  Sssp.BMSSP

  **Status: SPECIFICATION ONLY — not the verified algorithm.**

  Algorithm 3 of the paper (`formal/paper/source/main_result.tex:170`),
  Lemma 3.1 (correctness, `lemma:bmssp` and `lemma:main-algo-correctness`),
  Lemma 3.10 (size bound, `lemma:size-constraint`),
  and Lemma 3.12 (running time, `lemma:main-algo-time`).

  Reference implementation at `src/bmssp.rs:265`.

  This file does **not** verify the BMSSP algorithm.  The function
  `bmsspSpec` is non-recursive in the inductive case (the `_ih` hypothesis
  is unused below): it picks the truncation bound by `Classical.choose` on
  `exists_truncation_witness` and returns the bounded subtree below that
  cutoff.  All conclusions of `bmsspSpec_correct` therefore hold by
  construction; no algorithmic content is verified.

  In particular **the running-time claim of Lemma 3.12 is not stated
  anywhere** in this file — it requires the cost monad of Phase 2.

  The honest implementation (well-founded recursion on `l`, `D`-structure
  loop, Bellman-Ford in `FindPivots`, mini-Dijkstra in `BaseCase`) will
  live in `Sssp.Algo.BMSSP` (Phase 7 of the verification roadmap, see
  `formal/README.md`).
-/

import Sssp.Graph
import Sssp.Distance
import Sssp.DStruct
import Sssp.FindPivots
import Sssp.BaseCase

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- The two parameters of the algorithm. The paper picks
    `k = ⌊log^{1/3} n⌋` and `t = ⌊log^{2/3} n⌋`, but the *correctness*
    statement of BMSSP holds for any `k, t ≥ 1`. The asymptotic bound only
    binds these particular choices. -/
structure Params where
  k : ℕ
  t : ℕ
  hk : 1 ≤ k
  ht : 1 ≤ t

/-- Output of `BMSSP`. -/
structure BMSSPResult (n : ℕ) where
  newBound : WithTop NNReal     -- `B'`
  result : Finset (Fin n)        -- `U`
  newDist : DistEstimate n

/-- Convert a `BaseCaseResult` to a `BMSSPResult`. -/
def BaseCaseResult.toBMSSPResult (r : BaseCaseResult n) : BMSSPResult n :=
  { newBound := r.newBound, result := r.result, newDist := r.newDist }

/-- **Specification (oracle) of `BMSSP`.**  Decreases on `l`, but the
    inductive step does **not** recurse: it picks the truncation bound by
    `Classical.choose` on `exists_truncation_witness` (with
    `M = 2^{(l'+1)·t}`) and returns the bounded subtree below that cutoff.

    No `D`-structure, `FindPivots`, or recursion takes place. -/
noncomputable def bmsspSpec
    [HasDistinctVertexDistances G s]
    (P : Params) :
    ℕ → WithTop NNReal → DistEstimate n → Finset (Fin n) → BMSSPResult n :=
  fun l B dHat S =>
  match l with
  | 0 =>
      if h : S.Nonempty then
        let x := S.min' h
        (baseCaseSpec G s P.k B dHat x).toBMSSPResult
      else
        { newBound := B, result := ∅, newDist := dHat }
  | l' + 1 =>
      let newBound :=
        Classical.choose (exists_truncation_witness G s P.k (2 ^ ((l' + 1) * P.t)) B S)
      let result := boundedSubtreeOf G s S newBound
      { newBound := newBound
        result := result
        newDist := fun v => if v ∈ result then trueDist G s v else dHat v }

/-- **Lemma 3.1 (Bounded Multi-Source Shortest Path) — correctness of the spec.**

    Vacuous: every conclusion holds by construction of `bmsspSpec`.

    Pre-conditions (mirroring the paper):
      • `|S| ≤ 2^{l·t}`,
      • `S` is complete (every `v ∈ S` already has `d̂[v] = d(v)`),
      • for every incomplete `v` with `d(v) < B`, the shortest path to `v`
        visits some complete vertex of `S`.

    Conclusions:
      • `B' ≤ B`,
      • `U = T_{<B'}(S)`,
      • `U` is complete (under the new estimate),
      • `|U| ≤ 4 * k * 2^{l·t}` (always; truncation enforces this in both
        branches),
      • either successful execution (`B' = B`) or partial execution
        (`B' < B` with `k * 2^{l·t} ≤ |U|`). -/
theorem bmsspSpec_correct
    [HasDistinctLengths G]
    [HasDistinctVertexDistances G s]
    (P : Params)
    (l : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (hSize : S.card ≤ 2 ^ (l * P.t))
    (hSound : Sound G s dHat)
    (hSComplete : SetComplete G s dHat S)
    (hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtreeOf G s (completeOf G s dHat S)) :
    let r := bmsspSpec G s P l B dHat S
    Sound G s r.newDist
    ∧ r.newBound ≤ B
    ∧ r.result = boundedSubtreeOf G s S r.newBound
    ∧ SetComplete G s r.newDist r.result
    ∧ r.result.card ≤ 4 * P.k * 2 ^ (l * P.t)
    ∧ (r.newBound = B ∨
        (r.newBound < B ∧ P.k * 2 ^ (l * P.t) ≤ r.result.card)) := by
  induction l
  case zero =>
    dsimp
    by_cases hne : S.Nonempty
    · -- Singleton case: `|S| ≤ 2^0 = 1`, so `S = {x}`; delegate to `baseCaseSpec_correct`.
      have h_card : S.card = 1 := by
        have h_card_le : S.card ≤ 1 := by
          have h : 2 ^ (0 * P.t) = 1 := by simp
          simpa [h] using hSize
        have h_card_ge : 1 ≤ S.card := Finset.one_le_card.mpr hne
        exact le_antisymm h_card_le h_card_ge
      rcases Finset.card_eq_one.mp h_card with ⟨x, hS⟩
      subst hS
      have hxComplete : IsComplete G s dHat x := hSComplete x (Finset.mem_singleton.mpr rfl)
      have hCover' :
          ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B → v ∈ subtree G s x := by
        intro v hv_incomp hv_lt
        have h := hCover v hv_incomp hv_lt
        have h_comp_eq :
            completeOf G s dHat ({x} : Finset (Fin n)) = ({x} : Finset (Fin n)) := by
          ext u
          refine ⟨fun hu => (mem_completeOf_iff.mp hu).1, fun hu => ?_⟩
          rcases Finset.mem_singleton.mp hu with rfl
          exact mem_completeOf_iff.mpr ⟨hu, hxComplete⟩
        rw [h_comp_eq] at h
        simpa [subtreeOf] using h
      have hbc := baseCaseSpec_correct G s P.k B dHat x hSound hxComplete hCover'
      have hbmssp_val :
          bmsspSpec G s P 0 B dHat ({x} : Finset (Fin n))
            = (baseCaseSpec G s P.k B dHat x).toBMSSPResult := by
        simp [bmsspSpec, hne]
      rw [hbmssp_val]
      obtain ⟨h_sound, h_le, h_res, h_complete, h_size, h_lower⟩ := hbc
      have h_pow : (2 : ℕ) ^ (0 * P.t) = 1 := by simp
      refine ⟨h_sound, h_le, h_res, h_complete, ?_, ?_⟩
      · rw [h_pow, Nat.mul_one]; exact h_size
      · by_cases h_eq : (baseCaseSpec G s P.k B dHat x).newBound = B
        · exact Or.inl h_eq
        · have h_lt : (baseCaseSpec G s P.k B dHat x).newBound < B := lt_of_le_of_ne h_le h_eq
          right
          refine ⟨h_lt, ?_⟩
          rw [h_pow, Nat.mul_one]
          exact h_lower h_lt
    · -- Empty-frontier case.
      have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hS_empty
      have h_val : bmsspSpec G s P 0 B dHat ∅ = { newBound := B, result := ∅, newDist := dHat } := by
        simp [bmsspSpec]
      rw [h_val]
      have hComplete : SetComplete G s dHat ∅ := by intro v hv; simp at hv
      refine ⟨hSound, le_refl B, ?_, hComplete, ?_, Or.inl rfl⟩
      · simp [boundedSubtreeOf_empty]
      · simp

  case succ l _ih =>
    -- The inductive step is purely about the truncation witness;
    -- crucially, `_ih` is *not* used: this function does not recurse.
    let M : ℕ := 2 ^ ((l + 1) * P.t)
    have h_witness_spec :=
      Classical.choose_spec (exists_truncation_witness G s P.k M B S)
    obtain ⟨h_le, h_size, h_lower⟩ := h_witness_spec
    set newBound :=
      Classical.choose (exists_truncation_witness G s P.k M B S) with h_nb
    set resultSet := boundedSubtreeOf G s S newBound with h_res
    set newDist' : DistEstimate n :=
      fun v => if v ∈ resultSet then trueDist G s v else dHat v with h_nd
    have hr_eq :
        bmsspSpec G s P (l + 1) B dHat S =
          { newBound := newBound, result := resultSet, newDist := newDist' } := by
      dsimp [bmsspSpec]
    rw [hr_eq]
    refine ⟨?_, h_le, rfl, ?_, ?_, ?_⟩
    · intro v
      by_cases hv : v ∈ resultSet
      · simp [newDist', hv]
      · simp [newDist', hv]; exact hSound v
    · intro v hv
      simp [IsComplete, newDist', hv]
    · show resultSet.card ≤ 4 * P.k * 2 ^ ((l + 1) * P.t)
      simpa [M] using h_size
    · by_cases h_eq : newBound = B
      · exact Or.inl h_eq
      · right
        have h_lt : newBound < B := lt_of_le_of_ne h_le h_eq
        refine ⟨h_lt, ?_⟩
        simpa [M] using h_lower h_lt

/-- **Lemma 3.10 (Size constraint) — corollary of the spec.** -/
theorem bmsspSpec_size_bound
    [HasDistinctLengths G]
    [HasDistinctVertexDistances G s]
    (P : Params) (l : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (hSize : S.card ≤ 2 ^ (l * P.t))
    (hSound : Sound G s dHat)
    (hSComplete : SetComplete G s dHat S)
    (hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtreeOf G s (completeOf G s dHat S)) :
    (bmsspSpec G s P l B dHat S).result.card ≤ 4 * P.k * 2 ^ (l * P.t) := by
  obtain ⟨_, _, _, _, h_size, _⟩ :=
    bmsspSpec_correct G s P l B dHat S hSize hSound hSComplete hCover
  exact h_size

end Sssp
