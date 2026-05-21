/-
  Sssp.Fixtures.Graph

  Shared `(u, v, w)` edge lists for JSON fixture vectors.
  Verified `Graph n` instances are defined explicitly (out-degree proof by
  `fin_cases`); `RustGraph` instances are built from the same edge lists.
-/

import Mathlib
import Sssp.Algo.Dijkstra
import Sssp.Refine.Dijkstra
import Sssp.Refine.GraphBridge

namespace Sssp
namespace Fixtures

open Sssp Refine

def nnreal (w : Nat) : NNReal := w

def tinyChainEdges : List (Nat × Nat × Nat) := [(0, 1, 1), (1, 2, 2), (2, 3, 3)]
def diamondEdges : List (Nat × Nat × Nat) := [(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)]
def unreachableEdges : List (Nat × Nat × Nat) := [(0, 1, 1), (1, 2, 2), (3, 4, 1)]

/-- Build the Refine/Rust CSR graph from an integer-weight edge list. -/
def rustGraphFromNatEdges (n : Nat) (es : List (Nat × Nat × Nat)) : RustGraph :=
  RustGraph.fromEdgeList n (es.map fun e => (e.1, e.2.1, floatWeight e.2.2))

/-- Every graph built from an integer edge list carries a nat-weight witness. -/
noncomputable def hasNatWeights_rustGraphFromNatEdges (n : Nat) (es : List (Nat × Nat × Nat)) :
    HasNatWeights (rustGraphFromNatEdges n es) := by
  unfold rustGraphFromNatEdges
  exact hasNatWeights_fromEdgeList n es

def tinyChainGraph : Graph 4 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 1 ∧ v = 2 then {nnreal 2}
    else if u = 2 ∧ v = 3 then {nnreal 3}
    else {}
  outDeg_le := by
    intro u
    fin_cases u
    all_goals native_decide }

def diamondGraph : Graph 4 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 0 ∧ v = 2 then {nnreal 1}
    else if u = 1 ∧ v = 3 then {nnreal 1}
    else if u = 2 ∧ v = 3 then {nnreal 1}
    else {}
  outDeg_le := by
    intro u
    fin_cases u
    all_goals native_decide }

def unreachableGraph : Graph 5 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 1 ∧ v = 2 then {nnreal 2}
    else if u = 3 ∧ v = 4 then {nnreal 1}
    else {}
  outDeg_le := by
    intro u
    fin_cases u
    all_goals native_decide }

def singleVertexGraph : Graph 1 := {
  edges := fun _ _ => {}
  outDeg_le := by
    intro u
    fin_cases u
    all_goals native_decide }

def tinyChainRust : RustGraph := rustGraphFromNatEdges 4 tinyChainEdges
def diamondRust : RustGraph := rustGraphFromNatEdges 4 diamondEdges
def unreachableRust : RustGraph := rustGraphFromNatEdges 5 unreachableEdges
def singleVertexRust : RustGraph := rustGraphFromNatEdges 1 []

lemma rustGraphFromNatEdges_eq_edgeListGraph (n : Nat) (es : List (Nat × Nat × Nat)) :
    rustGraphFromNatEdges n es = edgeListGraph n es := rfl

/-- Integer edge lists yield valid `ValidRustGraph` bundles (fixture instances). -/
noncomputable def tinyChainValid : ValidRustGraph 4 tinyChainRust where
  hn := rfl
  hwt := hasNatWeights_rustGraphFromNatEdges 4 tinyChainEdges
  htgt := by intro u p hp; fin_cases u <;> native_decide +revert
  hdeg := by intro u; fin_cases u <;> native_decide

noncomputable def diamondValid : ValidRustGraph 4 diamondRust where
  hn := rfl
  hwt := hasNatWeights_rustGraphFromNatEdges 4 diamondEdges
  htgt := by intro u p hp; fin_cases u <;> native_decide +revert
  hdeg := by intro u; fin_cases u <;> native_decide

noncomputable def unreachableValid : ValidRustGraph 5 unreachableRust where
  hn := rfl
  hwt := hasNatWeights_rustGraphFromNatEdges 5 unreachableEdges
  htgt := by intro u p hp; fin_cases u <;> native_decide +revert
  hdeg := by intro u; fin_cases u <;> native_decide

noncomputable def singleVertexValid : ValidRustGraph 1 singleVertexRust where
  hn := rfl
  hwt := hasNatWeights_rustGraphFromNatEdges 1 []
  htgt := by intro u p hp; fin_cases u <;> native_decide +revert
  hdeg := by intro u; fin_cases u <;> native_decide

end Fixtures
end Sssp
