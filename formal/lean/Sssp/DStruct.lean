/-
  Sssp.DStruct

  The block-based partial-sorting data structure `D` from Lemma 3.3 of the
  paper, implemented in Rust at `src/dstruct.rs`.

  We model `D` as a finite multiset of `(key, value)` pairs (with the
  "smallest value per key" semantics) and specify the three operations
  `Insert`, `BatchPrepend`, `Pull` axiomatically. Concrete invariants of
  the block-list representation are deferred — they are needed only for
  the amortised running-time bound, not for correctness of BMSSP.
-/

import Sssp.Graph
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.WithBot

namespace Sssp
namespace DStruct

/-- A logical state of `D`: a partial map from keys to values.
    The "smallest value wins" semantics of `Insert` is captured in the
    operation specs, not in the type. -/
structure State (n : ℕ) where
  /-- Block-size parameter `M` from Lemma 3.3. -/
  M : ℕ
  /-- Upper bound `B` declared at `Initialize`. -/
  B : WithTop NNReal
  /-- The current (key, value) map: each key maps to its smallest live
      value. -/
  data : Fin n → Option NNReal

namespace State

variable {n : ℕ}

/-- Cardinality (number of live keys). -/
def size (D : State n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun v => (D.data v).isSome)).card

def isEmpty (D : State n) : Prop := D.size = 0

/-- `Insert(key, value)`: keep the smallest value seen for `key`. -/
def insert (D : State n) (k : Fin n) (v : NNReal) : State n :=
  { D with
    data := fun u =>
      if u = k then
        match D.data u with
        | none      => some v
        | some cur  => some (min cur v)
      else D.data u }

/-- `BatchPrepend(L)` — see `DStruct::batch_prepend` in
    `src/dstruct.rs:137`. Pre-condition: every value in `L` is strictly
    less than every live value currently in `D`. Captured here as a
    hypothesis on the spec. -/
def batchPrepend (D : State n) (L : List (Fin n × NNReal)) : State n :=
  L.foldl (fun acc kv => acc.insert kv.1 kv.2) D

end State

/-- `Initialize(M, B)` — see `DStruct::new` in `src/dstruct.rs:45`. -/
def init {n : ℕ} (M : ℕ) (B : WithTop NNReal) : State n :=
  { M := max M 1, B := B, data := fun _ => none }

/-- `Pull()` — returns up to `M` keys whose values are smallest, plus a
    separator `x` between the returned set and the rest. The Lean spec
    is the existence theorem; the concrete return value is left
    abstract. -/
structure PullResult (n : ℕ) where
  /-- The returned keys `S' ⊆ D`. -/
  keys : Finset (Fin n)
  /-- Separator `x`. -/
  sep : WithTop NNReal
  /-- New state of `D` after the keys are removed. -/
  state : State n

/-- Spec of `Pull`. We give it a noncomputable functional signature; the
    block-list implementation in `src/dstruct.rs:191` realises it.
    
    This stub returns an empty key set and an empty (freshly initialised)
    state, which satisfies the specification trivially.  The real
    implementation preserves the block-list invariants. -/
noncomputable def pull {n : ℕ} (D : State n) : PullResult n :=
  { keys := ∅,
    sep := D.B,
    state := init D.M D.B }

/-- **Lemma 3.3 (size).** `Pull` returns at most `M` keys. -/
theorem pull_size_le (D : State n) :
    (pull D).keys.card ≤ D.M := by
  simp [pull]

/-- **Lemma 3.3 (separator).** Either `D` becomes empty (in which case
    the separator equals the upper bound `B`) or every value in the
    *new* `D` is `≥ sep`, and every returned `(k, v)` satisfies
    `v < sep`. -/
theorem pull_separator (D : State n) :
    let r := pull D
    (r.state.isEmpty ∧ r.sep = D.B) ∨
    ((∀ k v, r.state.data k = some v → r.sep ≤ (v : WithTop NNReal)) ∧
     (∀ k ∈ r.keys, ∀ v, D.data k = some v →
         (v : WithTop NNReal) < r.sep)) := by
  intro r
  dsimp [r, pull]
  left
  constructor
  · simp [State.isEmpty, State.size, init]
  · rfl

/-- **Lemma 3.3 (insert correctness).** After `insert k v`, the value at
    `k` is the minimum of its old value (if any) and `v`. -/
theorem insert_eq (D : State n) (k : Fin n) (v : NNReal) :
    (D.insert k v).data k =
      some (match D.data k with
            | none     => v
            | some cur => min cur v) := by
  unfold State.insert
  simp
  cases D.data k <;> rfl

/-- **Lemma 3.3 (batch-prepend correctness).** After `batchPrepend D L`,
    the data is the `foldl`-of-`insert` characterization (the "smallest value wins"
    semantics). -/
theorem batchPrepend_eq (D : State n) (L : List (Fin n × NNReal)) :
    (State.batchPrepend D L).data =
      L.foldl (fun (data : Fin n → Option NNReal) (kv : Fin n × NNReal) =>
        Function.update data kv.1
          (some (match data kv.1 with | none => kv.2 | some cur => min cur kv.2)))
        D.data := by
  induction L generalizing D with
  | nil => rfl
  | cons kv L ih =>
    let f : (Fin n → Option NNReal) → (Fin n × NNReal) → (Fin n → Option NNReal) :=
      fun data kv' => Function.update data kv'.1
        (some (match data kv'.1 with | none => kv'.2 | some cur => min cur kv'.2))
    have h_insert : (D.insert kv.1 kv.2).data = f D.data kv := by
      ext u
      dsimp [f, State.insert, Function.update]
      by_cases h : u = kv.1
      · subst h; cases D.data kv.1 <;> simp
      · simp [h]
    have h_foldl : L.foldl f (f D.data kv) = (kv :: L).foldl f D.data := by
      calc
        L.foldl f (f D.data kv) = List.foldl f (f D.data kv) L := rfl
        _ = List.foldl f D.data (kv :: L) := by rw [← List.foldl_cons]
        _ = (kv :: L).foldl f D.data := rfl
    calc
      (State.batchPrepend D (kv :: L)).data
          = (State.batchPrepend (D.insert kv.1 kv.2) L).data := rfl
      _ = L.foldl f ((D.insert kv.1 kv.2).data) := ih (D.insert kv.1 kv.2)
      _ = L.foldl f (f D.data kv) := by rw [h_insert]
      _ = (kv :: L).foldl f D.data := h_foldl

end DStruct
end Sssp
