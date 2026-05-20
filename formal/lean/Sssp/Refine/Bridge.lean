/-
  Sssp.Refine.Bridge

  Align CSR `RustGraph` topology with verified `Graph n` on shared fixture
  edge lists.  Full Refine ≡ Algo equivalence is deferred to Phase 9; here we
  record decidable checks that both sides encode the same edges.
-/

import Mathlib
import Sssp.Fixtures.Graph

namespace Sssp
namespace Refine

open Sssp Fixtures

def csrOutEq (got exp : List (Nat × Float)) : Bool := got == exp

example : csrOutEq (tinyChainRust.outEdges 0) [(1, 1.0)] = true := by native_decide
example : csrOutEq (tinyChainRust.outEdges 1) [(2, 2.0)] = true := by native_decide
example : csrOutEq (tinyChainRust.outEdges 2) [(3, 3.0)] = true := by native_decide
example : csrOutEq (tinyChainRust.outEdges 3) [] = true := by native_decide

example : csrOutEq (diamondRust.outEdges 0) [(1, 1.0), (2, 1.0)] = true := by native_decide
example : csrOutEq (diamondRust.outEdges 1) [(3, 1.0)] = true := by native_decide
example : csrOutEq (diamondRust.outEdges 2) [(3, 1.0)] = true := by native_decide
example : csrOutEq (diamondRust.outEdges 3) [] = true := by native_decide

example : csrOutEq (unreachableRust.outEdges 0) [(1, 1.0)] = true := by native_decide
example : csrOutEq (unreachableRust.outEdges 1) [(2, 2.0)] = true := by native_decide
example : csrOutEq (unreachableRust.outEdges 2) [] = true := by native_decide
example : csrOutEq (unreachableRust.outEdges 3) [(4, 1.0)] = true := by native_decide
example : csrOutEq (unreachableRust.outEdges 4) [] = true := by native_decide

example : csrOutEq (singleVertexRust.outEdges 0) [] = true := by native_decide

theorem tinyChainGraph_edge_0_1 : (1 : NNReal) ∈ tinyChainGraph.edges 0 1 := by
  simp [tinyChainGraph, nnreal]

theorem tinyChainGraph_edge_1_2 : (2 : NNReal) ∈ tinyChainGraph.edges 1 2 := by
  simp [tinyChainGraph, nnreal]

theorem tinyChainGraph_edge_2_3 : (3 : NNReal) ∈ tinyChainGraph.edges 2 3 := by
  simp [tinyChainGraph, nnreal]

theorem diamondGraph_edge_0_1 : (1 : NNReal) ∈ diamondGraph.edges 0 1 := by
  simp [diamondGraph, nnreal]

theorem diamondGraph_edge_0_2 : (1 : NNReal) ∈ diamondGraph.edges 0 2 := by
  simp [diamondGraph, nnreal]

theorem diamondGraph_edge_1_3 : (1 : NNReal) ∈ diamondGraph.edges 1 3 := by
  simp [diamondGraph, nnreal]

theorem diamondGraph_edge_2_3 : (1 : NNReal) ∈ diamondGraph.edges 2 3 := by
  simp [diamondGraph, nnreal]

theorem unreachableGraph_edge_0_1 : (1 : NNReal) ∈ unreachableGraph.edges 0 1 := by
  simp [unreachableGraph, nnreal]

theorem unreachableGraph_edge_1_2 : (2 : NNReal) ∈ unreachableGraph.edges 1 2 := by
  simp [unreachableGraph, nnreal]

theorem unreachableGraph_edge_3_4 : (1 : NNReal) ∈ unreachableGraph.edges 3 4 := by
  simp [unreachableGraph, nnreal]

end Refine
end Sssp
