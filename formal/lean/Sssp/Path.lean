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
import Mathlib.Data.Multiset.Basic

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
  ⟨ w1.steps ++ w2.steps, WalkValid.append w1.valid w2.valid ⟩

/-- Length of an appended walk is the sum of lengths. -/
theorem length_append (w1 : Walk G s u) (w2 : Walk G u v) :
    (w1.append w2).length = w1.length + w2.length := by
  dsimp [append, Walk.length]
  simp [List.sum_append]

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
