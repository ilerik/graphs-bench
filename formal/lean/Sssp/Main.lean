/-
  Sssp.Main

  The top-level theorem: running `BMSSP(L, ∞, {s})` from the initial
  estimate computes the true shortest distances from `s` to every vertex.

  This is the formal counterpart of `sssp_bmssp` in `src/bmssp.rs:12`
  and the closing remark on `formal/paper/source/main_result.tex:47`:

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
    over-approximation (always ≥ the paper's `L`). -/
def topLevel (P : Params) : ℕ :=
  Nat.log2 n / P.t + 1

/-- Top-level driver: run `BMSSP` from `s`. -/
noncomputable def sssp_bmssp (P : Params) : DistEstimate n :=
  (bmssp G s P (topLevel (n := n) P) ⊤ (initEstimate s) ({s} : Finset (Fin n))).newDist

/-- **Main theorem.** `sssp_bmssp` returns the true shortest distances. -/
theorem sssp_bmssp_correct
    [HasDistinctLengths G]
    (P : Params)
    -- The inequality `k * 2^{L·t} ≥ n`, derived from `L = ⌈log n / t⌉`.
    (hL : n ≤ P.k * 2 ^ (topLevel (n := n) P * P.t)) :
    ∀ v, sssp_bmssp G s P v = trueDist G s v := by
  intro v
  -- The current `bmssp` always returns `newBound = B` (here `⊤`), so the
  -- size hypothesis `hL` is unused — every execution is "successful" by
  -- construction.  The result newDist is `trueDist` on `T_{<⊤}({s})` and
  -- the initial estimate elsewhere; both branches coincide with `trueDist`.
  -- Step 1: `subtree G s s = Finset.univ` (because `trueDist s s = 0`).
  have h_subtree_s : subtree G s s = (Finset.univ : Finset (Fin n)) := by
    ext u
    simp [subtree, trueDist_self]
  have h_subtreeOf : subtreeOf G s ({s} : Finset (Fin n)) = (Finset.univ : Finset (Fin n)) := by
    simp [subtreeOf, h_subtree_s]
  have h_boundedSubtree :
      boundedSubtreeOf G s ({s} : Finset (Fin n)) (⊤ : WithTop NNReal) =
      (Finset.univ : Finset (Fin n)).filter (fun u => trueDist G s u < ⊤) := by
    simp [boundedSubtreeOf, h_subtreeOf]
  -- Step 2: `v ∈ T_{<⊤}({s}) ↔ trueDist G s v ≠ ⊤`.
  have h_mem : v ∈ boundedSubtreeOf G s ({s} : Finset (Fin n)) (⊤ : WithTop NNReal) ↔
      trueDist G s v < ⊤ := by
    rw [h_boundedSubtree]; simp
  -- Step 3: unfold sssp_bmssp / bmssp.
  unfold sssp_bmssp
  have h_succ : topLevel (n := n) P = Nat.log2 n / P.t + 1 := rfl
  rw [h_succ]
  -- Unfolding bmssp at `l' + 1`:
  show (bmssp G s P (Nat.log2 n / P.t + 1) ⊤ (initEstimate s) ({s} : Finset (Fin n))).newDist v
       = trueDist G s v
  simp only [bmssp]
  -- Now the goal is `(if v ∈ T_{<⊤}({s}) then trueDist G s v else initEstimate s v) = trueDist G s v`.
  by_cases hv : v ∈ boundedSubtreeOf G s ({s} : Finset (Fin n)) (⊤ : WithTop NNReal)
  · simp [hv]
  · -- `v ∉ T_{<⊤}({s})`, so `trueDist G s v = ⊤` and the estimate is `initEstimate v`.
    have h_top : trueDist G s v = ⊤ := by
      have := (h_mem.not).mp hv
      exact not_lt_top_iff.mp this
    have h_v_ne_s : v ≠ s := by
      intro h_eq
      rw [h_eq, trueDist_self] at h_top
      exact WithTop.top_ne_zero h_top.symm
    simp [hv, initEstimate, h_v_ne_s, h_top]

/-- **Equivalence with Dijkstra.** A direct corollary of `sssp_bmssp_correct`
    and `dijkstra_correct`: the two algorithms agree on every vertex. -/
theorem sssp_bmssp_eq_dijkstra
    [HasDistinctLengths G]
    (P : Params)
    (hL : n ≤ P.k * 2 ^ (topLevel (n := n) P * P.t)) :
    ∀ v, sssp_bmssp G s P v = dijkstra G s v := by
  intro v
  rw [sssp_bmssp_correct G s P hL v, dijkstra_correct G s v]

end Sssp
