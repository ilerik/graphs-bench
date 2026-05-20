/-
  Sssp.FindPivots

  **Status: SPECIFICATION ONLY — not the verified algorithm.**

  Algorithm 1 (FindPivots) of the paper does `k` rounds of Bellman–Ford
  from a frontier `S` and selects pivots from `S` whose tight-edge tree
  inside the visited set has ≥ `k` vertices.  See `find_pivots` at
  `src/bmssp.rs:81` for the reference implementation.

  This file does **not** verify that algorithm.  `findPivotsSpec` returns:
    * if `|Ũ| ≤ k|S| + |S|`: the entire `Ũ` as `visited` and an empty
      pivot set;
    * otherwise: the first `k|S| + |S|` elements of `Ũ.toList` as
      `visited` and `S^*` (the complete vertices of `S`) as pivots.
  In either branch `newDist` is set to `trueDist` on the visited set, so
  the spec lemma `findPivotsSpec_correct` holds without any pivot-tree
  reasoning.

  The honest implementation, with `k`-round Bellman–Ford and the
  forest-of-tight-edges argument, will live in `Sssp.Algo.FindPivots`
  (Phase 5 of the verification roadmap, see `formal/README.md`).
-/

import Sssp.Graph
import Sssp.Path
import Sssp.Distance
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Card

namespace Sssp

variable {n : ℕ} (G : Graph n) (s : Fin n)

/-- Output of `FindPivots`. -/
structure FindPivotsResult (n : ℕ) where
  pivots : Finset (Fin n)
  visited : Finset (Fin n)
  newDist : DistEstimate n

/-- **Specification (oracle) of `FindPivots`.**  Returns the abstract
    answer that satisfies Lemma 3.2 by construction.  No Bellman–Ford
    is performed. -/
noncomputable def findPivotsSpec
    (G : Graph n) (s : Fin n)
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n)) :
    FindPivotsResult n :=
  let eu := expectU G s dHat S B
  let total := k * S.card + S.card
  if h : eu.card ≤ total then
    { pivots := ∅, visited := eu, newDist := fun v => if v ∈ eu then trueDist G s v else dHat v }
  else
    let takenList := (eu.toList).take total
    have hListNodup : takenList.Nodup :=
      (Finset.nodup_toList eu).sublist (List.take_sublist total (eu.toList))
    have hMultisetNodup : (takenList : Multiset (Fin n)).Nodup := by
      simpa using hListNodup
    let visitedSubset : Finset (Fin n) :=
      Finset.mk (takenList : Multiset (Fin n)) hMultisetNodup
    { pivots := completeOf G s dHat S,
      visited := visitedSubset,
      newDist := fun v => if v ∈ visitedSubset then trueDist G s v else dHat v }

/-- **Lemma 3.2 (correctness of the spec).**  Vacuous: `findPivotsSpec`
    is built to satisfy this conjunction by definition.  See `Sssp.Algo`
    for the real implementation. -/
theorem findPivotsSpec_correct
    [HasDistinctLengths G]
    (k : ℕ) (B : WithTop NNReal)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (hSound : Sound G s dHat)
    (_hCover :
      ∀ v, ¬ IsComplete G s dHat v → trueDist G s v < B →
        v ∈ subtreeOf G s (completeOf G s dHat S)) :
    let r := findPivotsSpec G s k B dHat S
    Sound G s r.newDist ∧
    r.visited ⊆ S ∪ expectU G s dHat S B ∧
    r.visited.card ≤ k * S.card + S.card ∧
    k * r.pivots.card ≤ r.visited.card ∧
    (∀ x ∈ expectU G s dHat S B,
      (x ∈ r.visited ∧ IsComplete G s r.newDist x) ∨
      x ∈ subtreeOf G s (completeOf G s r.newDist r.pivots)) := by
  intro r
  let eu := expectU G s dHat S B
  let total := k * S.card + S.card
  by_cases heu_small : eu.card ≤ total
  · -- Case 1: |eu| ≤ total — visit all of eu, no pivots
    have hr : r = { pivots := ∅, visited := eu, newDist := fun v => if v ∈ eu then trueDist G s v else dHat v } := by
      dsimp [r, findPivotsSpec]
      simp [eu, total, heu_small]
    rw [hr]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v; by_cases hv : v ∈ eu <;> simp [hv, hSound v]
    · exact Finset.subset_union_right
    · exact heu_small
    · simp
    · intro x hx
      have hx_eu : x ∈ eu := by simpa [eu] using hx
      left; exact ⟨hx_eu, by
        dsimp [IsComplete]
        simp [hx_eu]⟩
  · -- Case 2: |eu| > total — visit `total` vertices, pivots = S^*
    have h_gt : total < eu.card := by omega
    have hn : ((eu.toList).take total).Nodup :=
      (Finset.nodup_toList eu).sublist (List.take_sublist total (eu.toList))
    let takenFinset : Finset (Fin n) := Finset.mk ((eu.toList).take total) (by simpa using hn)
    let newDist' : DistEstimate n := fun v => if v ∈ takenFinset then trueDist G s v else dHat v
    have hr : r = { pivots := completeOf G s dHat S, visited := takenFinset, newDist := newDist' } := by
      dsimp [r, findPivotsSpec, takenFinset, newDist']
      simp [eu, total, heu_small]
    rw [hr]
    have h_taken_card : takenFinset.card = total := by
      simp [takenFinset, Finset.card_mk, List.length_take, Finset.length_toList]
      omega
    have h_taken_sub_eu : ∀ v, v ∈ takenFinset → v ∈ eu := by
      intro v hv
      have hv_list : v ∈ (eu.toList).take total := by
        rw [Finset.mem_mk] at hv; simpa using hv
      have hv_eu_list : v ∈ eu.toList := List.mem_of_mem_take hv_list
      simpa using hv_eu_list
    have h_complete_eq : completeOf G s newDist' (completeOf G s dHat S) = completeOf G s dHat S := by
      ext v; constructor
      · intro hv
        rcases mem_completeOf_iff.mp hv with ⟨hv_pivot, hv_comp⟩
        exact hv_pivot
      · intro hv
        rcases mem_completeOf_iff.mp hv with ⟨hv_S, hv_comp⟩
        apply mem_completeOf_iff.mpr
        refine ⟨hv, ?_⟩
        dsimp [newDist', IsComplete]
        by_cases hv_taken : v ∈ takenFinset
        · simp [hv_taken]
        · simp [hv_taken]; exact hv_comp
    have h_comp_subset_card : (completeOf G s dHat S).card ≤ S.card :=
      Finset.card_le_card (completeOf_subset (G := G) (s := s) (dHat := dHat) (S := S))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Sound
      intro v; dsimp [newDist']
      by_cases hv : v ∈ takenFinset <;> simp [hv, hSound v]
    · -- visited ⊆ S ∪ eu
      intro v hv; apply Finset.mem_union_right; exact h_taken_sub_eu v hv
    · -- |visited| ≤ total
      rw [h_taken_card]
    · -- k * |pivots| ≤ |visited|
      rw [h_taken_card]
      calc
        k * (completeOf G s dHat S).card ≤ k * S.card :=
          Nat.mul_le_mul_left k h_comp_subset_card
        _ ≤ k * S.card + S.card := by omega
    · -- coverage
      intro x hx
      have hx_eu : x ∈ eu := by simpa [eu] using hx
      by_cases hx_taken : x ∈ takenFinset
      · left; refine ⟨hx_taken, ?_⟩
        dsimp [newDist', IsComplete]
        simp [hx_taken]
      · right
        rcases (mem_expectU_iff (G := G) (s := s) (dHat := dHat) (S := S) (B := B)).mp hx with ⟨hx_subtree, hx_lt⟩
        rw [h_complete_eq]
        exact hx_subtree

/-- **Lemma 3.2 (running time)** — not yet stated; running-time
    formalisation requires the cost monad of Phase 2. -/
theorem findPivotsSpec_time
    (_k : ℕ) (_B : WithTop NNReal)
    (_dHat : DistEstimate n) (_S : Finset (Fin n)) :
    True := by
  trivial

end Sssp
