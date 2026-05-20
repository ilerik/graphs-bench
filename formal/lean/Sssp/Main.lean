/-
  Sssp.Main

  **Status: SPECIFICATION ONLY — not the verified algorithm.**

  Top-level driver and equivalence-with-Dijkstra theorem, both stated for
  the *specifications* `bmsspSpec` (Sssp/BMSSP.lean) and `dijkstraSpec`
  (Sssp/Dijkstra.lean), neither of which is the verified algorithm.

  The theorem `sssp_bmsspSpec_correct` holds because the inductive step of
  `bmsspSpec` returns `boundedSubtreeOf G s {s} newBound` with
  `newBound = ⊤` (forced by the `n < k · 2^{Lt}` hypothesis), and that
  bounded subtree is exactly the reachable vertices.  No algorithmic
  argument is invoked.

  The honest top-level driver — running the real BMSSP recursion from
  `Sssp.Algo.BMSSP` and proving correctness *and* the
  `O(m · log^{2/3} n)` running time — will live in `Sssp.Algo.Main`
  (Phase 8 of the verification roadmap, see `formal/README.md`).

  This file mirrors `sssp_bmssp` in `src/bmssp.rs:12` and the closing
  remark on `formal/paper/source/main_result.tex:47`:

    "On the top level of divide and conquer, the main algorithm calls
     BMSSP with parameters l = ⌈(log n)/t⌉, S = {s}, B = ∞. Because
     |U| ≤ |V| = o(kn), it must be a successful execution, and the
     shortest paths to all vertices are found."
-/

import Sssp.Graph
import Sssp.Distance
import Sssp.BMSSP

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

open Classical

/-- The depth `L = ⌈(log₂ n) / t⌉` from §3, computed as a `Nat` so that the
    Lean function is total. The choice `n.log2 / t + 1` is the cleanest
    over-approximation (always strictly greater than the paper's `L`). -/
def topLevel (P : Params) : ℕ :=
  Nat.log2 n / P.t + 1

/-- **Top-level driver of the spec.**  Runs `bmsspSpec` from `s` (which
    does no recursion; see `Sssp.BMSSP`). -/
noncomputable def sssp_bmsspSpec [HasDistinctVertexDistances G s] (P : Params) :
    DistEstimate n :=
  (bmsspSpec G s P (topLevel (n := n) P) ⊤ (initEstimate s)
    ({s} : Finset (Fin n))).newDist

/-- **Main theorem (spec form).** `sssp_bmsspSpec` returns the true
    shortest distances.

    The hypothesis `hL : n < P.k * 2^{L·t}` (a strict inequality) ensures
    that the truncation in `bmsspSpec`'s inductive step never fires at the
    top level: the partial-execution lower bound `P.k * 2^{L·t} ≤ |U|`
    would contradict `|U| ≤ n < P.k * 2^{L·t}`.

    The proof is *not* algorithmic — it observes that the spec's
    `Classical.choose`-based bound must equal `⊤` and that
    `boundedSubtreeOf G s {s} ⊤` is the universe restricted to reachable
    vertices. -/
theorem sssp_bmsspSpec_correct
    [HasDistinctLengths G]
    [HasDistinctVertexDistances G s]
    (P : Params)
    (hL : n < P.k * 2 ^ (topLevel (n := n) P * P.t)) :
    ∀ v, sssp_bmsspSpec G s P v = trueDist G s v := by
  intro v
  -- Step 1: structural facts about `subtreeOf G s {s}`.
  have h_subtree_s : subtree G s s = (Finset.univ : Finset (Fin n)) := by
    ext u; simp [subtree, trueDist_self]
  have h_subtreeOf : subtreeOf G s ({s} : Finset (Fin n)) = (Finset.univ : Finset (Fin n)) := by
    simp [subtreeOf, h_subtree_s]
  -- Step 2: unfold the top-level call.
  unfold sssp_bmsspSpec
  set L := topLevel (n := n) P with hL_def
  -- The recursion depth is positive: `L = log2 n / t + 1 = succ ...`
  have hL_succ : L = (Nat.log2 n / P.t) + 1 := rfl
  rw [hL_succ]
  -- Step 3: reduce to the `succ` case of `bmsspSpec`.
  show (bmsspSpec G s P (Nat.log2 n / P.t + 1) ⊤ (initEstimate s)
        ({s} : Finset (Fin n))).newDist v = trueDist G s v
  -- Pull out the `Classical.choose`-based truncation bound.
  set M : ℕ := 2 ^ ((Nat.log2 n / P.t + 1) * P.t) with hM_def
  set newBound :=
    Classical.choose (exists_truncation_witness G s P.k M
      (⊤ : WithTop NNReal) ({s} : Finset (Fin n))) with hnb_def
  set resultSet :=
    boundedSubtreeOf G s ({s} : Finset (Fin n)) newBound with hres_def
  have h_witness_spec :=
    Classical.choose_spec (exists_truncation_witness G s P.k M
      (⊤ : WithTop NNReal) ({s} : Finset (Fin n)))
  obtain ⟨h_le_top, h_size, h_lower⟩ := h_witness_spec
  -- Step 4: `newBound = ⊤`.
  have h_nb_top : newBound = (⊤ : WithTop NNReal) := by
    rcases lt_or_eq_of_le h_le_top with h_lt | h_eq
    · -- Partial branch impossible: bound `|result| ≤ n` versus `P.k * M ≤ |result|`.
      exfalso
      have h_lb : P.k * M ≤ resultSet.card := h_lower h_lt
      have h_ub : resultSet.card ≤ n := by
        have : resultSet.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        simpa using this
      have : P.k * M ≤ n := h_lb.trans h_ub
      have : n < P.k * M := by simpa [hM_def, hL_def, hL_succ] using hL
      omega
    · exact h_eq
  -- Step 5: with `newBound = ⊤`, `resultSet` covers exactly the reachable vertices.
  have h_resultSet_eq : resultSet =
      (Finset.univ : Finset (Fin n)).filter (fun u => trueDist G s u < ⊤) := by
    rw [hres_def, h_nb_top, boundedSubtreeOf, h_subtreeOf]
  -- Step 6: discharge the goal.
  -- `bmsspSpec`'s succ branch returns `newDist v = if v ∈ resultSet then trueDist G s v else dHat v`.
  have h_bmssp_unfold :
      (bmsspSpec G s P (Nat.log2 n / P.t + 1) ⊤ (initEstimate s)
        ({s} : Finset (Fin n))).newDist v =
        (if v ∈ resultSet then trueDist G s v else (initEstimate s) v) := by
    show (bmsspSpec G s P (Nat.log2 n / P.t + 1) ⊤ (initEstimate s)
        ({s} : Finset (Fin n))).newDist v = _
    rfl
  rw [h_bmssp_unfold]
  by_cases hv : v ∈ resultSet
  · simp [hv]
  · -- `v ∉ resultSet` ⇒ `trueDist G s v = ⊤`; and `v ≠ s`.
    have hv_top : trueDist G s v = ⊤ := by
      rw [h_resultSet_eq, Finset.mem_filter] at hv
      simp at hv
      exact hv
    have hv_ne_s : v ≠ s := by
      intro h_eq
      rw [h_eq, trueDist_self] at hv_top
      exact WithTop.top_ne_zero hv_top.symm
    simp [hv, initEstimate, hv_ne_s, hv_top]

/-- **Equivalence of specifications.**  A direct corollary of
    `sssp_bmsspSpec_correct` and `dijkstraSpec_correct`: the two
    *specifications* agree on every vertex.  This is *not* an
    equivalence between the two real algorithms — both sides here are
    oracles that return `trueDist`. -/
theorem sssp_bmsspSpec_eq_dijkstraSpec
    [HasDistinctLengths G]
    [HasDistinctVertexDistances G s]
    (P : Params)
    (hL : n < P.k * 2 ^ (topLevel (n := n) P * P.t)) :
    ∀ v, sssp_bmsspSpec G s P v = dijkstraSpec G s v := by
  intro v
  rw [sssp_bmsspSpec_correct G s P hL v, dijkstraSpec_correct G s v]

end Sssp
