/-
  Sssp.Refine.GraphBridge

  Phase 3b: general bridge from CSR `RustGraph` to verified `Graph n`.
  Integer-weighted graphs (`floatWeight w`) are the first supported class.
-/

import Mathlib
import Sssp.Refine.Dijkstra

namespace Sssp
namespace Refine

open Sssp

/-- CSR edge weights are natural numbers rendered as `Float`. -/
structure HasNatWeights (g : RustGraph) where
  edgeWeight : ∀ (u i : Nat), i < (g.outEdges u).length → Nat
  edgeWeight_spec :
    ∀ (u i : Nat) (hi : i < (g.outEdges u).length),
      floatWeight (edgeWeight u i hi) = ((g.outEdges u)[i]'hi).2

/-- Every CSR out-edge weight is the `Float` image of a natural number (legacy view). -/
structure HasNatWeights' (g : RustGraph) where
  weight : ∀ (u : Nat) (p : Nat × Float), p ∈ g.outEdges u → Nat
  weight_spec :
    ∀ (u : Nat) (p : Nat × Float) (hp : p ∈ g.outEdges u),
      floatWeight (weight u p hp) = p.2

def HasNatWeights'.toHasNatWeights {g : RustGraph} (h : HasNatWeights' g) :
    HasNatWeights g where
  edgeWeight u i hi := h.weight u ((g.outEdges u)[i]'hi) (List.getElem_mem hi)
  edgeWeight_spec u i hi := h.weight_spec u ((g.outEdges u)[i]'hi) (List.getElem_mem hi)

/-- Out-degree (with multiplicity) at each vertex is at most 2. -/
def outDegNatLe (g : RustGraph) (n : Nat) : Prop :=
  ∀ u : Fin n, (g.outEdges u.val).length ≤ 2

/-- Every out-edge target is a valid vertex index. -/
def targetsIn (g : RustGraph) (n : Nat) : Prop :=
  ∀ (u : Fin n) (p : Nat × Float), p ∈ g.outEdges u.val → p.1 < n

namespace RustGraph

/-- Extract `Graph n` edge weights at `(u,v)` from CSR out-edges. -/
def weightsToTarget (g : RustGraph) (hwt : HasNatWeights g) (u tgt : Nat) : List NNReal :=
  (List.range (g.outEdges u).length).flatMap fun i =>
    if h : i < (g.outEdges u).length then
      if ((g.outEdges u)[i]'h).1 == tgt then
        [nnrealWeight (hwt.edgeWeight u i h)]
      else []
    else []

/-- Build a verified `Graph n` from a CSR graph with natural `Float` weights.

    Requires `hout` showing the multiset partition matches CSR out-degree. -/
noncomputable def csrToGraph (g : RustGraph) (n : Nat) (_hn : g.n = n)
    (hwt : HasNatWeights g)
    (hout : ∀ (u : Fin n),
      ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = (g.outEdges u.val).length)
    (hdeg : outDegNatLe g n) : Graph n where
  edges := fun u v => Multiset.ofList (weightsToTarget g hwt u.val v.val)
  outDeg_le := by
    intro u
    calc
      ∑ v : Fin n, (Multiset.ofList (weightsToTarget g hwt u.val v.val)).card
          = ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length := by
            refine Finset.sum_congr rfl fun v _ => ?_
            exact (Multiset.coe_card _).symm
      _ = (g.outEdges u.val).length := hout u
      _ ≤ 2 := hdeg u

theorem mem_edges_csrToGraph {g : RustGraph} {n : Nat} (hn : g.n = n) {hwt : HasNatWeights g}
    {hout : ∀ (u : Fin n),
      ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = (g.outEdges u.val).length}
    {hdeg : outDegNatLe g n} {u v : Fin n} {w : NNReal} :
    w ∈ (csrToGraph g n hn hwt hout hdeg).edges u v ↔
      ∃ (i : Nat) (hi : i < (g.outEdges u.val).length),
        ((g.outEdges u.val)[i]'hi).1 = v.val ∧
          w = nnrealWeight (hwt.edgeWeight u.val i hi) := by
  simp only [csrToGraph, Multiset.mem_coe]
  constructor
  · intro hw
    dsimp [weightsToTarget] at hw
    rw [List.mem_flatMap] at hw
    obtain ⟨i, hi, hw'⟩ := hw
    rw [List.mem_range] at hi
    by_cases htgt : ((g.outEdges u.val)[i]'hi).1 = v.val
    · simp [htgt, hi] at hw'
      exact ⟨i, hi, htgt, hw'⟩
    · simp [htgt, hi] at hw'
  · intro ⟨i, hi, htgt, hw⟩
    dsimp [weightsToTarget]
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simp [hi, htgt, hw]

end RustGraph

end Refine
end Sssp
