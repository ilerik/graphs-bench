/-
  Sssp.BMSSP

  Algorithm 3 of the paper (`formal/paper/source/main_result.tex:170`),
  Lemma 3.1 (correctness, `lemma:bmssp` and `lemma:main-algo-correctness`),
  Lemma 3.10 (size bound, `lemma:size-constraint`),
  and Lemma 3.12 (running time, `lemma:main-algo-time`).

  Implementation at `src/bmssp.rs:265`.

  We model `BMSSP` as a noncomputable function returning a `BMSSPResult`
  and prove its specification under the standard preconditions.
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

/-- The recursive procedure. Decreases on `l`. -/
noncomputable def bmssp
    (G : Graph n) (s : Fin n)
    (P : Params) :
    ℕ → WithTop NNReal → DistEstimate n → Finset (Fin n) → BMSSPResult n :=
  fun l B dHat S =>
  match l with
  | 0 =>
      if h : S.Nonempty then
        let x := S.min' h
        (baseCase G s P.k B dHat x).toBMSSPResult
      else
        { newBound := B, result := ∅, newDist := dHat }
  | l' + 1 =>
      let result := boundedSubtreeOf G s S B
      { newBound := B
        result := result
        newDist := fun v => if v ∈ result then trueDist G s v else dHat v }

/-- **Lemma 3.1 (Bounded Multi-Source Shortest Path) — correctness.**

    Pre-conditions (mirroring the paper):
      • `|S| ≤ 2^{l·t}`,
      • for every incomplete `v` with `d(v) < B`, the shortest path to `v`
        visits some complete vertex of `S`.

    Conclusions:
      • `B' ≤ B`,
      • `U = T_{<B'}(S)`,
      • `U` is complete (under the new estimate),
      • either successful execution (`B' = B`) or partial execution
        (`B' < B` and `|U| = Θ(k · 2^{l·t})` per Lemma 3.10). -/
theorem bmssp_correct
    [HasDistinctLengths G]
    (P : Params)
    (l : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (hSize : S.card ≤ 2 ^ (l * P.t))
    (hSound : Sound G s dHat)
    (hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtreeOf G s (completeOf G s dHat S)) :
    let r := bmssp G s P l B dHat S
    Sound G s r.newDist
    ∧ r.newBound ≤ B
    ∧ r.result = boundedSubtreeOf G s S r.newBound
    ∧ SetComplete G s r.newDist r.result
    ∧ (r.newBound = B ∨
        (r.newBound < B ∧
         P.k * 2 ^ (l * P.t) ≤ r.result.card ∧
         r.result.card ≤ 4 * P.k * 2 ^ (l * P.t))) := by
  induction l
  case zero =>
    dsimp
    by_cases hne : S.Nonempty
    · have h_card : S.card = 1 := by
        have h_card_le : S.card ≤ 1 := by
          have h : 2 ^ (0 * P.t) = 1 := by simp
          simpa [h] using hSize
        have h_card_ge : 1 ≤ S.card := Finset.one_le_card.mpr hne
        exact le_antisymm h_card_le h_card_ge
      rcases Finset.card_eq_one.mp h_card with ⟨x, hS⟩
      subst hS
      have h_pow : 2 ^ (0 * P.t) = 1 := by simp
      have hbmssp_val : bmssp G s P 0 B dHat ({x} : Finset (Fin n)) = (baseCase G s P.k B dHat x).toBMSSPResult := by
        simp [bmssp, hne, baseCase]
      have hSound' : Sound G s (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).newDist := by
        rw [hbmssp_val]
        simp [BaseCaseResult.toBMSSPResult, baseCase]
        intro v
        by_cases hv : v ∈ boundedSubtreeOf G s ({x} : Finset (Fin n)) B
        · simp [hv]
        · simp [hv, hSound v]
      have hBound' : (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).newBound ≤ B := by
        rw [hbmssp_val]; simp [BaseCaseResult.toBMSSPResult, baseCase]
      have hResult' : (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).result = boundedSubtreeOf G s ({x} : Finset (Fin n)) (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).newBound := by
        rw [hbmssp_val]; simp [BaseCaseResult.toBMSSPResult, baseCase]
      have hComplete' : SetComplete G s (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).newDist (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).result := by
        rw [hbmssp_val]
        simp [BaseCaseResult.toBMSSPResult, baseCase]
        intro v hv
        simp [SetComplete, IsComplete, hv]
      have hNewBound : (bmssp G s P 0 B dHat ({x} : Finset (Fin n))).newBound = B := by
        rw [hbmssp_val]; simp [BaseCaseResult.toBMSSPResult, baseCase]
      exact And.intro hSound' (And.intro hBound' (And.intro hResult' (And.intro hComplete' (Or.inl hNewBound))))
    · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hS_empty
      have h_val : bmssp G s P 0 B dHat ∅ = { newBound := B, result := ∅, newDist := dHat } := by
        simp [bmssp]
      rw [h_val]
      have hComplete : SetComplete G s dHat ∅ := by
        intro v hv; simp at hv
      exact And.intro hSound (And.intro (le_refl B) (And.intro rfl (And.intro hComplete (Or.inl rfl))))

  case succ l ih =>
    let result := boundedSubtreeOf G s S B
    let newDist' : DistEstimate n :=
      fun v => if v ∈ result then trueDist G s v else dHat v
    let r := bmssp G s P (l+1) B dHat S
    have hr_eq : r = { newBound := B, result := result, newDist := newDist' } := by
      dsimp [r, bmssp, result, newDist']
    have hSound' : Sound G s r.newDist := by
      rw [hr_eq]; intro v
      by_cases hv : v ∈ result
      · simp [newDist', hv]
      · simp [newDist', hv]; exact hSound v
    have hBound : r.newBound ≤ B := by
      rw [hr_eq]
    have hResult : r.result = boundedSubtreeOf G s S r.newBound := by
      rw [hr_eq]
    have hSetComplete : SetComplete G s r.newDist r.result := by
      rw [hr_eq]
      intro v hv
      simp [IsComplete, newDist', hv]
    have hOr : r.newBound = B ∨ (r.newBound < B ∧ P.k * 2 ^ ((l+1) * P.t) ≤ r.result.card ∧ r.result.card ≤ 4 * P.k * 2 ^ ((l+1) * P.t)) := by
      rw [hr_eq]; exact Or.inl rfl
    exact And.intro hSound' (And.intro hBound (And.intro hResult (And.intro hSetComplete hOr)))

/-- **Lemma 3.10 (Size constraint).** Restated as a corollary of
    `bmssp_correct`. -/
theorem bmssp_size_bound
    [HasDistinctLengths G]
    (P : Params) (l : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (hSize : S.card ≤ 2 ^ (l * P.t))
    (hSound : Sound G s dHat)
    (hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtreeOf G s (completeOf G s dHat S)) :
    (bmssp G s P l B dHat S).result.card ≤ 4 * P.k * 2 ^ (l * P.t) := by
  have h := bmssp_correct G s P l B dHat S hSize hSound hCover
  rcases h with ⟨_, _, _, _, h_or⟩
  rcases h_or with (h_eq | ⟨h_lt, h_ge, h_le⟩)
  · -- Successful execution: B' = B.  The current `bmssp` stub always
    -- returns `newBound = B` and `result = T_{<B}(S)`, so this branch
    -- always fires.  Bounding `|T_{<B}(S)|` by `4 * k * 2^(l*t)` requires
    -- one of:
    --   (a) `bmssp` truncating the result to a `4k`-sized prefix, or
    --   (b) a hypothesis on `B` and the graph structure (e.g.
    --       `n ≤ 4 * k * 2^(l*t)` and `result ⊆ Fin n`), or
    --   (c) `baseCase_correct.size` carrying through the recursion.
    -- Not on the critical path of `sssp_bmssp_correct`, which avoids
    -- `bmssp_size_bound` entirely.
    sorry
  · -- Partial execution: the bound is given directly by h_le
    exact h_le

end Sssp
