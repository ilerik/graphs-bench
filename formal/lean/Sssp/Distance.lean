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

end Sssp
