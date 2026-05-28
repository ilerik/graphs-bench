/-
  Sssp.Path

  Walks and paths in a `Graph n`, the length of a walk, and the technical
  Assumption 2.1 from §2: all walks from the source have distinct lengths.

  We use `Walk` (a list of edges) rather than a strictly simple `Path`
  because the paper's invariants (e.g. "the shortest path to `v` visits
  some vertex of `S`") are most naturally stated about walks. The
  distinct-length assumption ensures a unique shortest walk to every
  vertex, which is what makes `Pred[v]` a tree.
-/

import Sssp.Graph
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Duplicate
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace Sssp

/-- Inductive predicate: `WalkValid G s t steps` holds iff `steps` describes
    a valid walk from `s` to `t` in `G` (each edge present in `G`). -/
inductive WalkValid {n : ℕ} (G : Graph n) : Fin n → Fin n → List (Fin n × NNReal) → Prop
  | nil (h : s = t) : WalkValid G s t []
  | cons (u v : Fin n) (w : NNReal) (steps : List (Fin n × NNReal))
         (h_edge : w ∈ G.edges u v)
         (h_tail : WalkValid G v t steps) :
         WalkValid G u t ((v, w) :: steps)

/-- A walk in `G` from `s` to `t`: list of `(intermediate vertex, weight)`
    pairs, plus the head `s`. We encode paths as
    `(s, [(v₁, w₁), …, (vₖ, wₖ)])` where each consecutive triple
    `(u, v, w)` must satisfy `w ∈ G.edges u v`. -/
structure Walk {n : ℕ} (G : Graph n) (s t : Fin n) where
  /-- Sequence of `(next-vertex, edge-weight)` steps, in order from `s`. -/
  steps : List (Fin n × NNReal)
  /-- Proof that `steps` is a valid walk from `s` to `t` in `G`. -/
  valid : WalkValid G s t steps

namespace Walk

variable {n : ℕ} {G : Graph n} {s t : Fin n}

@[simp] lemma ext {w₁ w₂ : Walk G s t} (h : w₁.steps = w₂.steps) : w₁ = w₂ := by
  cases w₁
  cases w₂
  subst h
  rfl

noncomputable instance decidableEqWalk : DecidableEq (Walk G s t) := Classical.decEq _

/-- Extend a walk from `v` to `t` by one edge `s → v`. -/
def consStep {s v t : Fin n} (w₀ : NNReal) (w' : Walk G v t) (h : w₀ ∈ G.edges s v) :
    Walk G s t :=
  ⟨(v, w₀) :: w'.steps, WalkValid.cons s v w₀ w'.steps h w'.valid⟩

/-- The total weight of a walk. -/
def length (w : Walk G s t) : NNReal :=
  (w.steps.map Prod.snd).sum

/-- Number of edges traversed by the walk. -/
def numEdges (w : Walk G s t) : ℕ := w.steps.length

/-- The list of intermediate vertices of `w`, including the source `s`
    and the endpoint `t`. -/
def vertices (w : Walk G s t) : List (Fin n) :=
  s :: w.steps.map Prod.fst

/-- A walk *visits* `v` iff `v` appears in its vertex list. -/
def visits (w : Walk G s t) (v : Fin n) : Prop :=
  v ∈ w.vertices

/-- If `h1` is a valid walk from `s` to `u`, and `h2` from `u` to `v`,
    then `h1 ++ h2` is a valid walk from `s` to `v`. -/
lemma WalkValid.append {w1_steps w2_steps : List (Fin n × NNReal)}
    (h1 : WalkValid G s u w1_steps) (h2 : WalkValid G u v w2_steps) :
    WalkValid G s v (w1_steps ++ w2_steps) := by
  induction h1 with
  | nil h =>
    subst h
    exact h2
  | cons u' v' w' steps' h_edge h_tail ih =>
    exact WalkValid.cons u' v' w' (steps' ++ w2_steps) h_edge (ih h2)

/-- Concatenate two walks: `w1` from `s` to `u` and `w2` from `u` to `v`. -/
def append (w1 : Walk G s u) (w2 : Walk G u v) : Walk G s v :=
  ⟨w1.steps ++ w2.steps, WalkValid.append w1.valid w2.valid⟩

/-- Length of an appended walk is the sum of lengths. -/
theorem length_append (w1 : Walk G s u) (w2 : Walk G u v) :
    (w1.append w2).length = w1.length + w2.length := by
  dsimp [append, Walk.length]
  simp [List.sum_append]

/-- A walk with a positive number of edges starts with an out-edge of the source. -/
lemma exists_first_step {u : Fin n} {w : Walk G s u} (h : 0 < w.numEdges) :
    ∃ v w0 rest, w.steps = (v, w0) :: rest ∧ w0 ∈ G.edges s v := by
  rcases w with ⟨steps, valid⟩
  cases steps with
  | nil => simp [Walk.numEdges] at h
  | cons p rest =>
    cases p with
    | mk v w0 =>
      cases valid with
      | cons _ _ _ _ h_edge h_tail =>
        exact ⟨v, w0, rest, rfl, h_edge⟩

lemma valid_tail_of_cons {s v u : Fin n} {w0 : NNReal} {rest : List (Fin n × NNReal)}
    (h : WalkValid G s u ((v, w0) :: rest)) : WalkValid G v u rest := by
  cases h with
  | cons _ _ _ _ _ h_tail => exact h_tail

/-- The tail walk after the first step. -/
lemma exists_first_step_tail {u : Fin n} {w : Walk G s u} (h : 0 < w.numEdges) :
    ∃ v w0, ∃ w' : Walk G v u, w.steps = (v, w0) :: w'.steps ∧ w0 ∈ G.edges s v := by
  rcases w with ⟨steps, valid⟩
  cases steps with
  | nil => simp [Walk.numEdges] at h
  | cons p rest =>
    cases p with
    | mk v w0 =>
      cases valid with
      | cons _ _ _ _ h_edge h_tail =>
        exact ⟨v, w0, ⟨rest, h_tail⟩, rfl, h_edge⟩

lemma exists_first_step_tail_src {src tgt : Fin n} {w : Walk G src tgt} (h : 0 < w.numEdges) :
    ∃ v w0, ∃ w' : Walk G v tgt, w.steps = (v, w0) :: w'.steps ∧ w0 ∈ G.edges src v := by
  rcases w with ⟨steps, valid⟩
  cases steps with
  | nil => simp [Walk.numEdges] at h
  | cons p rest =>
    cases p with
    | mk v w0 =>
      cases valid with
      | cons _ _ _ _ h_edge h_tail =>
        exact ⟨v, w0, ⟨rest, h_tail⟩, rfl, h_edge⟩

lemma vertices_length (w : Walk G s u) : w.vertices.length = w.numEdges + 1 := by
  simp [Walk.vertices, Walk.numEdges]

/-- Vertex visited after the first `k` edges of `w` (`k = 0` is the source). -/
def vertexAt (w : Walk G s t) (k : ℕ) (hk : k ≤ w.numEdges) : Fin n :=
  w.vertices.get ⟨k, by rw [Walk.vertices_length]; omega⟩

lemma vertexAt_zero (w : Walk G s t) :
    vertexAt w 0 (Nat.zero_le _) = s := by
  simp [vertexAt, Walk.vertices]

lemma vertexAt_succ {u : Fin n} {w : Walk G s u} (k : ℕ) (hk : k + 1 ≤ w.numEdges) :
    ∃ v w0 rest, ∃ h_tail : WalkValid G v u rest,
      w.steps = (v, w0) :: rest ∧
      ∃ hk', vertexAt w (k + 1) hk = vertexAt ⟨rest, h_tail⟩ k hk' := by
  rcases w with ⟨steps, valid⟩
  cases steps with
  | nil => simp [Walk.numEdges] at hk
  | cons p rest =>
    cases valid with
    | cons _ v w0 rest' h_edge h_tail =>
      refine ⟨v, w0, rest, h_tail, rfl, ?_⟩
      have hk' : k ≤ rest.length := by simp [Walk.numEdges] at hk; omega
      exact ⟨hk', by simp [vertexAt, Walk.vertices]⟩

lemma vertexAt_walk_succ {u : Fin n} {v w0 rest}
    {h_edge : w0 ∈ G.edges s v} {h_tail : WalkValid G v u rest}
    (k : ℕ) (hk : k + 1 ≤ ((v, w0) :: rest).length) (hk' : k ≤ rest.length) :
    vertexAt ⟨(v, w0) :: rest, WalkValid.cons s v w0 rest h_edge h_tail⟩ (k + 1) hk =
    vertexAt ⟨rest, h_tail⟩ k hk' := by
  simp [vertexAt, Walk.vertices, Walk.numEdges]

lemma cast_steps {u v : Fin n} (h : u = v) (w : Walk G u t) :
    (h ▸ w).steps = w.steps := by subst h; rfl

lemma takeSteps_valid (k : ℕ) (w : Walk G s t) (hk : k ≤ w.numEdges) :
    WalkValid G s (vertexAt w k hk) (w.steps.take k) := by
  induction k generalizing w s t with
  | zero =>
    simp [vertexAt_zero]
    exact WalkValid.nil rfl
  | succ k ih =>
    rcases w with ⟨steps, valid⟩
    cases valid with
    | nil h => simp [Walk.numEdges] at hk
    | cons u v w0 rest h_edge h_tail =>
      have hk' : k ≤ rest.length := by simp [Walk.numEdges] at hk; omega
      simp [vertexAt, Walk.vertices, List.take_succ_cons]
      exact WalkValid.cons s v w0 (rest.take k) h_edge (@ih v t ⟨rest, h_tail⟩ hk')

lemma dropSteps_valid (j : ℕ) (w : Walk G s t) (hj : j ≤ w.numEdges) :
    WalkValid G (vertexAt w j hj) t (w.steps.drop j) := by
  induction j generalizing w s t with
  | zero =>
    simp [vertexAt_zero]
    exact w.valid
  | succ j ih =>
    rcases w with ⟨steps, valid⟩
    cases valid with
    | nil h => simp [Walk.numEdges] at hj
    | cons u v w0 rest h_edge h_tail =>
      have hj' : j ≤ rest.length := by simp [Walk.numEdges] at hj; omega
      simp [vertexAt, Walk.vertices, List.drop_succ_cons]
      exact @ih v t ⟨rest, h_tail⟩ hj'

/-- First `k` edges of `w`. -/
def takeSteps (k : ℕ) (w : Walk G s t) (hk : k ≤ w.numEdges) : Walk G s (vertexAt w k hk) :=
  ⟨w.steps.take k, takeSteps_valid k w hk⟩

/-- Drop the first `j` edges of `w`. -/
def dropSteps (j : ℕ) (w : Walk G s t) (hj : j ≤ w.numEdges) : Walk G (vertexAt w j hj) t :=
  ⟨w.steps.drop j, dropSteps_valid j w hj⟩

lemma numEdges_takeSteps (k : ℕ) (w : Walk G s t) (hk : k ≤ w.numEdges) :
    (takeSteps k w hk).numEdges = k := by
  simp only [takeSteps, Walk.numEdges, List.length_take, Nat.min_eq_left (by simpa [Walk.numEdges] using hk)]

lemma numEdges_dropSteps (j : ℕ) (w : Walk G s t) (hj : j ≤ w.numEdges) :
    (dropSteps j w hj).numEdges = w.numEdges - j := by
  simp only [dropSteps, Walk.numEdges, List.length_drop, Nat.min_eq_left (by simpa [Walk.numEdges] using hj)]

lemma sum_take_add_sum_drop_le (l : List NNReal) {i j : ℕ} (hij : i ≤ j) :
    (l.take i).sum + (l.drop j).sum ≤ l.sum := by
  calc
    (l.take i).sum + (l.drop j).sum
        ≤ (l.take j).sum + (l.drop j).sum := by
      gcongr
      exact (List.monotone_sum_take l) hij
    _ = l.sum := by rw [← List.sum_take_add_sum_drop l j]

lemma takeSteps_steps (k : ℕ) (w : Walk G s t) (hk : k ≤ w.numEdges) :
    (takeSteps k w hk).steps = w.steps.take k := by simp [takeSteps]

lemma dropSteps_steps (j : ℕ) (w : Walk G s t) (hj : j ≤ w.numEdges) :
    (dropSteps j w hj).steps = w.steps.drop j := by simp [dropSteps]

/-- Walk length splits along `takeSteps` / `dropSteps`. -/
lemma length_takeSteps_add_dropSteps {u : Fin n} (w : Walk G s u) {j : ℕ} (hj : j ≤ w.numEdges) :
    w.length = (takeSteps j w hj).length + (dropSteps j w hj).length := by
  dsimp [Walk.length, takeSteps, dropSteps]
  have hjlen : j ≤ (w.steps.map Prod.snd).length := by simpa [Walk.numEdges] using hj
  calc
    w.length = (w.steps.map Prod.snd).sum := rfl
    _ = ((w.steps.map Prod.snd).take j).sum + ((w.steps.map Prod.snd).drop j).sum :=
      (List.sum_take_add_sum_drop (w.steps.map Prod.snd) j).symm
    _ = (List.map Prod.snd (w.steps.take j)).sum + (List.map Prod.snd (w.steps.drop j)).sum := by
      simp [List.map_take, List.map_drop]
    _ = (takeSteps j w hj).length + (dropSteps j w hj).length := rfl

/-- A one-edge suffix after `dropSteps` is a single edge into the target. -/
lemma dropSteps_one_edge {j : ℕ} {w : Walk G s u} (hj : j ≤ w.numEdges)
    (h : (dropSteps j w hj).numEdges = 1) :
    ∃ wt, wt ∈ G.edges (vertexAt w j hj) u ∧
      (dropSteps j w hj).length = wt ∧
      w.length = (takeSteps j w hj).length + wt := by
  set tail := dropSteps j w hj
  have hm : 0 < tail.numEdges := by rw [h]; omega
  obtain ⟨v, wt, w', hsteps, h_edge⟩ := exists_first_step_tail hm
  have hw'nil : w'.steps = [] := by
    have hn : w'.steps.length = 0 := by
      have hlen : w'.steps.length + 1 = tail.steps.length := by
        simpa [List.length_cons] using congrArg List.length hsteps.symm
      have htail : tail.steps.length = 1 := by simpa [Walk.numEdges] using h
      linarith
    exact List.eq_nil_of_length_eq_zero hn
  have hvu : v = u := by
    have hvalid := w'.valid
    rw [hw'nil] at hvalid
    cases hvalid with
    | nil hTU => exact hTU
  have hlen_tail : tail.length = wt := by
    have hsteps' : tail.steps = [(v, wt)] := by simpa [hw'nil] using hsteps
    rcases tail with ⟨steps, valid⟩
    subst hsteps'
    simp [Walk.length]
  refine ⟨wt, ?_, hlen_tail, ?_⟩
  · simpa [vertexAt_zero, dropSteps, hvu] using h_edge
  · rw [← hlen_tail]
    simpa [tail, dropSteps] using length_takeSteps_add_dropSteps (w := w) (j := j) hj

lemma cast_dropSteps_steps {u : Fin n} {i j : ℕ} (w : Walk G s u) (hi : i ≤ w.numEdges) (hj : j ≤ w.numEdges)
    (hdup : vertexAt w i hi = vertexAt w j hj) :
    (hdup ▸ dropSteps j w hj).steps = w.steps.drop j := by
  have h := cast_steps hdup.symm (dropSteps j w hj)
  rwa [dropSteps_steps] at h

lemma length_take_append_drop {u : Fin n} {i j : ℕ} (w : Walk G s u)
    (hi : i ≤ w.numEdges) (hj : j ≤ w.numEdges) (hij : i ≤ j)
    (hdup : vertexAt w i hi = vertexAt w j hj) :
    ((takeSteps i w hi).append (hdup ▸ dropSteps j w hj)).length ≤ w.length := by
  dsimp [Walk.length, Walk.append]
  rw [takeSteps_steps, cast_dropSteps_steps w hi hj hdup, List.map_append, List.map_take, List.map_drop,
    List.sum_append]
  exact sum_take_add_sum_drop_le (w.steps.map Prod.snd) hij

/-- Remove one loop between equal vertex positions; strictly fewer edges. -/
def removeLoop {u : Fin n} (w : Walk G s u) {i j : ℕ} (hi : i ≤ w.numEdges) (hj : j ≤ w.numEdges)
    (_hij : i < j) (hdup : vertexAt w i hi = vertexAt w j hj) : Walk G s u :=
  (takeSteps i w hi).append (hdup ▸ dropSteps j w hj)

theorem removeLoop_numEdges_lt {u : Fin n} (w : Walk G s u) {i j : ℕ}
    (hi : i ≤ w.numEdges) (hj : j ≤ w.numEdges) (hij : i < j)
    (hdup : vertexAt w i hi = vertexAt w j hj) :
    (removeLoop w hi hj hij hdup).numEdges < w.numEdges := by
  have hlen : (removeLoop w hi hj hij hdup).steps.length = i + (w.numEdges - j) := by
    have hi' : i ≤ w.steps.length := by simpa [Walk.numEdges] using hi
    have hj' : j ≤ w.steps.length := by simpa [Walk.numEdges] using hj
    simp [removeLoop, Walk.append, takeSteps_steps, cast_dropSteps_steps w hi hj hdup,
      List.length_append, List.length_take, List.length_drop, Walk.numEdges, min_eq_left hi', min_eq_left hj']
  rw [Walk.numEdges, hlen]
  omega

theorem removeLoop_length_le {u : Fin n} (w : Walk G s u) {i j : ℕ}
    (hi : i ≤ w.numEdges) (hj : j ≤ w.numEdges) (hij : i < j)
    (hdup : vertexAt w i hi = vertexAt w j hj) :
    (removeLoop w hi hj hij hdup).length ≤ w.length := by
  dsimp [removeLoop, Walk.length, Walk.append]
  rw [takeSteps_steps, cast_dropSteps_steps w hi hj hdup, List.map_append, List.map_take, List.map_drop,
    List.sum_append]
  exact sum_take_add_sum_drop_le (w.steps.map Prod.snd) (Nat.le_of_lt hij)

lemma duplicate_exists_lt_getElem {α} {l : List α} {x : α} (h : List.Duplicate x l) :
    ∃ (i j : Fin l.length), i.val < j.val ∧ l[i] = x ∧ l[j] = x := by
  induction h with
  | cons_mem hm =>
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨0, by simp⟩, ⟨i + 1, by simp [hi]⟩, Nat.succ_pos _, ?_, ?_⟩
    · simp
    · simp [List.getElem_cons_succ, hx]
  | cons_duplicate inner ih =>
    obtain ⟨i, j, hij, hxi, hxj⟩ := ih
    refine ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩,
      Nat.succ_lt_succ hij, ?_, ?_⟩
    · exact hxi
    · exact hxj

/-- Trim loops until at most `n` edges remain without increasing length. -/
theorem exists_trimmed_walk {u : Fin n} (w : Walk G s u) :
    ∃ w' : Walk G s u, w'.length ≤ w.length ∧ w'.numEdges ≤ n := by
  by_cases hn : w.numEdges ≤ n
  · exact ⟨w, le_rfl, hn⟩
  · have hlen : n + 1 ≤ w.vertices.length := by rw [Walk.vertices_length]; omega
    have hcard : Fintype.card (Fin n) < w.vertices.length := by
      simp [Fintype.card_fin]; omega
    have hnodup : ¬ w.vertices.Nodup := by
      intro H
      exact Nat.not_lt_of_ge (List.Nodup.length_le_card (α := Fin n) H) hcard
    obtain ⟨x, hx⟩ := (List.exists_duplicate_iff_not_nodup).2 hnodup
    obtain ⟨i, j, hij, hxi, hxj⟩ := duplicate_exists_lt_getElem hx
    have hi' : i.val ≤ w.numEdges := by
      have : i.val < w.numEdges + 1 := by simpa [Walk.vertices_length] using i.isLt
      exact Nat.lt_succ_iff.mp this
    have hj' : j.val ≤ w.numEdges := by
      have : j.val < w.numEdges + 1 := by simpa [Walk.vertices_length] using j.isLt
      exact Nat.lt_succ_iff.mp this
    have hdup : vertexAt w i.val hi' = vertexAt w j.val hj' := by
      simp only [vertexAt, Walk.vertices]
      exact hxi.trans hxj.symm
    let w' := removeLoop w hi' hj' hij hdup
    have hwlt : w'.numEdges < w.numEdges := removeLoop_numEdges_lt w hi' hj' hij hdup
    have hwle : w'.length ≤ w.length := removeLoop_length_le w hi' hj' hij hdup
    obtain ⟨w'', hlen', hedges'⟩ := exists_trimmed_walk w'
    exact ⟨w'', hlen'.trans hwle, hedges'⟩

end Walk

/-- Assumption 2.1: every walk has a unique total length.
    The paper ensures this by lexicographic tie-breaking; we model it here
    as a clean axiom on `G`. The implementation in `src/bmssp.rs` relies on
    continuous random weights to satisfy this with probability 1. -/
class HasDistinctLengths {n : ℕ} (G : Graph n) : Prop where
  distinct :
    ∀ {s t : Fin n} (w₁ w₂ : Walk G s t),
      w₁.length = w₂.length → w₁.steps = w₂.steps

end Sssp
