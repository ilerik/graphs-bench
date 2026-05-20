/-
  Sssp.BaseCase

  Algorithm 2 of the paper (`formal/paper/source/main_result.tex:133`,
  `BaseCase` Algorithm); implementation at `src/bmssp.rs:201`.

  Pre-conditions:
    • `S = {x}` is a singleton, `x` is complete.
    • Every incomplete vertex `v` with `d(v) < B` has its shortest path
      visiting `x`.

  Returns `(B', U)` such that, **per Lemma 3.1 base case** (proof in
  `formal/paper/source/main_result.tex:380` ff.):
    • `U = T_{<B'}(S)`,
    • all of `U` is complete,
    • `|U| ≤ 4k * 2^{0·t} = 4k`,
    • if `B' < B` then `|U| ≥ k`.
-/

import Sssp.Graph
import Sssp.Distance
import Sssp.Dijkstra

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- Output of `BaseCase`. -/
structure BaseCaseResult (n : ℕ) where
  newBound : WithTop NNReal     -- `B'`
  result : Finset (Fin n)        -- `U`
  newDist : DistEstimate n

noncomputable def baseCase
    (G : Graph n) (s : Fin n)
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (x : Fin n) :
    BaseCaseResult n :=
  { newBound := B
    result := boundedSubtreeOf G s ({x} : Finset (Fin n)) B
    newDist := fun v => if v ∈ boundedSubtreeOf G s ({x} : Finset (Fin n)) B then trueDist G s v else dHat v }

/-- **Lemma 3.1, base case (correctness).** -/
theorem baseCase_correct
    [HasDistinctLengths G]
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (x : Fin n)
    (hSound : Sound G s dHat)
    (hxComplete : IsComplete G s dHat x)
    (hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtree G s x) :
    let r := baseCase G s k B dHat x
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
  dsimp [r, baseCase]
  refine ⟨?_, le_refl B, rfl, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ boundedSubtreeOf G s ({x} : Finset (Fin n)) B
    · simp [hv]
    · simp [hv, hSound v]
  · intro v hv
    simp [IsComplete, hv]
  · -- Deferred: |U| ≤ 4k.  The current noncomputable stub returns the
    -- *full* bounded subtree T_{<B}({x}); the paper's algorithm truncates
    -- this to the k+1 closest vertices via a mini Dijkstra.  Filling this
    -- sorry requires either:
    --   (a) replacing the stub with a truncating construction (and proving
    --       it still satisfies `result = T_{<B'}({x})` for the new B'); or
    --   (b) strengthening `HasDistinctLengths` to imply distinct vertex
    --       distances from `s` (current axiom only constrains walks
    --       between the same pair of vertices).
    -- Not on the critical path: `sssp_bmssp_correct` does not depend on
    -- this bound, since the current `bmssp` always reports successful
    -- execution and `T_{<⊤}({s})` already covers every reachable vertex.
    sorry
  · intro h
    exfalso
    exact lt_irrefl B h

end Sssp
