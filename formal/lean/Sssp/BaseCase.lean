/-
  Sssp.BaseCase

  **Status: SPECIFICATION ONLY — not the verified algorithm.**

  Algorithm 2 of the paper (`formal/paper/source/main_result.tex:133`,
  `BaseCase` Algorithm); reference implementation at `src/bmssp.rs:201`.

  Pre-conditions (paper):
    • `S = {x}` is a singleton, `x` is complete.
    • Every incomplete vertex `v` with `d(v) < B` has its shortest path
      visiting `x`.

  Returns `(B', U)` such that, **per Lemma 3.1 base case** (proof in
  `formal/paper/source/main_result.tex:380` ff.):
    • `U = T_{<B'}(S)`,
    • all of `U` is complete,
    • `|U| ≤ 4k * 2^{0·t} = 4k`,
    • if `B' < B` then `|U| ≥ k`.

  This file does **not** verify the bounded-Dijkstra algorithm.  Instead
  `baseCaseSpec` picks the truncation bound by `Classical.choose` on
  `exists_baseCase_witness` (an order-theoretic existence lemma proved in
  `Sssp.Distance.exists_truncation_witness`) and returns the bounded
  subtree below that cutoff.  All conclusions of `baseCaseSpec_correct`
  hold by construction; no algorithmic content is verified.

  The honest implementation (a real bounded mini-Dijkstra) will live in
  `Sssp.Algo.BaseCase`, reusing the verified Dijkstra of
  `Sssp.Algo.Dijkstra` (Phase 6 of the verification roadmap, see
  `formal/README.md`).
-/

import Sssp.Graph
import Sssp.Distance
import Sssp.Dijkstra
import Mathlib.Data.Finset.Sort

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- Output of `BaseCase`. -/
structure BaseCaseResult (n : ℕ) where
  newBound : WithTop NNReal     -- `B'`
  result : Finset (Fin n)        -- `U`
  newDist : DistEstimate n

/-- **Existence of the cutoff produced by mini-Dijkstra.**

    Specialisation of `exists_truncation_witness` to `M = 1` and
    `S = {x}`. -/
theorem exists_baseCase_witness
    [HasDistinctVertexDistances G s]
    (k : ℕ) (B : WithTop NNReal) (x : Fin n) :
    ∃ (newBound : WithTop NNReal),
      newBound ≤ B ∧
      (boundedSubtreeOf G s ({x} : Finset (Fin n)) newBound).card ≤ 4 * k ∧
      (newBound < B → k ≤ (boundedSubtreeOf G s ({x} : Finset (Fin n)) newBound).card) := by
  have h := exists_truncation_witness G s k 1 B ({x} : Finset (Fin n))
  obtain ⟨B', hB'_le, hSize, hLower⟩ := h
  refine ⟨B', hB'_le, ?_, ?_⟩
  · simpa [Nat.mul_one] using hSize
  · intro hlt; simpa [Nat.mul_one] using hLower hlt

/-- **Specification (oracle) of `BaseCase`.**  Picks the truncation bound by
    `Classical.choose` on `exists_baseCase_witness`, then returns the
    bounded subtree below that cutoff and the corresponding `newDist`
    that equals `trueDist` on the result.

    No mini-Dijkstra is executed — the algorithm is deferred to
    `Sssp.Algo.BaseCase`. -/
noncomputable def baseCaseSpec
    (G : Graph n) (s : Fin n)
    [HasDistinctVertexDistances G s]
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (x : Fin n) :
    BaseCaseResult n :=
  let newBound := Classical.choose (exists_baseCase_witness G s k B x)
  let result := boundedSubtreeOf G s ({x} : Finset (Fin n)) newBound
  { newBound := newBound
    result := result
    newDist := fun v => if v ∈ result then trueDist G s v else dHat v }

/-- **Lemma 3.1, base case (correctness of the spec).**  Vacuous corollary
    of the truncation witness; no algorithmic content is verified. -/
theorem baseCaseSpec_correct
    [HasDistinctLengths G]
    [HasDistinctVertexDistances G s]
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (x : Fin n)
    (hSound : Sound G s dHat)
    (_hxComplete : IsComplete G s dHat x)
    (_hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtree G s x) :
    let r := baseCaseSpec G s k B dHat x
    -- New estimate still sound:
    Sound G s r.newDist
    -- B' ≤ B:
    ∧ r.newBound ≤ B
    -- U = T_{<B'}({x}):
    ∧ r.result = boundedSubtreeOf G s ({x} : Finset (Fin n)) r.newBound
    -- U is complete (under the new estimate):
    ∧ SetComplete G s r.newDist r.result
    -- Size bound (Lemma 3.10 with l = 0): |U| ≤ 4k.
    ∧ r.result.card ≤ 4 * k
    -- Partial-execution lower bound: if `B' < B` then `|U| ≥ k`.
    ∧ (r.newBound < B → k ≤ r.result.card) := by
  intro r
  -- Unpack the witness produced by `Classical.choose`.
  have h_witness := Classical.choose_spec (exists_baseCase_witness G s k B x)
  obtain ⟨h_le, h_size, h_lower⟩ := h_witness
  -- Match the `let`-binders inside `baseCaseSpec` to the local names below.
  set newBound := Classical.choose (exists_baseCase_witness G s k B x) with h_nb
  set resultSet := boundedSubtreeOf G s ({x} : Finset (Fin n)) newBound with h_res
  set newDist' : DistEstimate n :=
    fun v => if v ∈ resultSet then trueDist G s v else dHat v with h_nd
  have h_r : r = { newBound := newBound, result := resultSet, newDist := newDist' } := rfl
  rw [h_r]
  refine ⟨?_, h_le, rfl, ?_, h_size, h_lower⟩
  · -- Sound G s newDist'
    intro v
    by_cases hv : v ∈ resultSet
    · simp [newDist', hv]
    · simp [newDist', hv]; exact hSound v
  · -- SetComplete G s newDist' resultSet
    intro v hv
    simp [IsComplete, newDist', hv]

end Sssp
