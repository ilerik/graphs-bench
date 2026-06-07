/-
  Sssp.Refine.HeapBridge

  Connect lazy-heap `dijkstraHeap` to `dijkstraRelax` (Phase 3b heap step).
  Full simulation is future work; correctness on `ValidRustGraph` is trusted
  here and regression-checked on fixtures via `native_decide`.
-/

import Sssp.Refine.Simulation

namespace Sssp
namespace Refine

open Sssp Fixtures

variable {n : ℕ} {g : RustGraph}

/-- Heap relaxation over an out-edge list preserves the distance-vector length. -/
private theorem foldl_heap_relax_dist_length (du : Float) (edges : List (Nat × Float))
    (dist : List Float) (heap : List HeapItem) :
    ((edges.foldl (fun (dh : List Float × List HeapItem) (edge : Nat × Float) =>
      let nd := du + edge.2
      if nd < dh.1[edge.1]! then
        (dh.1.set edge.1 nd, heapPush dh.2 ⟨nd, edge.1⟩)
      else
        dh) (dist, heap)).1).length = dist.length := by
  induction edges generalizing dist heap with
  | nil =>
      simp
  | cons edge edges ih =>
      simp only [List.foldl_cons]
      by_cases hlt : du + edge.2 < dist[edge.1]!
      · rw [if_pos hlt]
        have h := ih (dist.set edge.1 (du + edge.2))
          (heapPush heap { d := du + edge.2, v := edge.1 })
        simpa [List.length_set] using h
      · rw [if_neg hlt]
        exact ih dist heap

/-- One lazy-heap step preserves the distance-vector length. -/
theorem dijkstraStep_dist_length (g : RustGraph) (dist : List Float) (heap : List HeapItem) :
    (dijkstraStep g dist heap).1.length = dist.length := by
  unfold dijkstraStep
  cases hpop : heapPopMin heap with
  | none =>
      simp
  | some pair =>
      rcases pair with ⟨item, rest⟩
      cases hstale : distStale dist item
      · simp [hstale]
        simpa using foldl_heap_relax_dist_length item.d (g.outEdges item.v) dist rest
      · simp [hstale]

/-- The lazy-heap runner preserves the distance-vector length for any fuel. -/
theorem dijkstraRun_dist_length (fuel : Nat) (g : RustGraph)
    (dist : List Float) (heap : List HeapItem) :
    (dijkstraRun fuel g dist heap).1.length = dist.length := by
  induction fuel generalizing dist heap with
  | zero =>
      simp [dijkstraRun]
  | succ fuel ih =>
      simp only [dijkstraRun]
      cases hstep : dijkstraStep g dist heap with
      | mk dist' heap' =>
          have hlen_step : dist'.length = dist.length := by
            simpa [hstep] using dijkstraStep_dist_length g dist heap
          calc
            (dijkstraRun fuel g dist' heap').1.length = dist'.length := ih dist' heap'
            _ = dist.length := hlen_step

/-- Lazy-heap Dijkstra returns one distance slot per graph vertex. -/
theorem dijkstraHeap_length (g : RustGraph) (source : Nat) :
    (dijkstraHeap g source).length = g.n := by
  unfold dijkstraHeap
  simpa using dijkstraRun_dist_length (g.n * g.edgeTo.length + g.n + 1) g
    ((List.range g.n).map fun v => if v == source then 0.0 else distInf) [⟨0.0, source⟩]

/-- Lazy-heap Dijkstra agrees with the proof-relevant relaxation model on valid
    CSR graphs (nat weights, out-degree ≤ 2). Fixture vectors checked below. -/
axiom dijkstraHeap_eq_dijkstraRelax (vg : ValidRustGraph n g) (source : Nat) :
    dijkstraHeap g source = dijkstraRelax g source

theorem dijkstra_eq_dijkstraRelax (vg : ValidRustGraph n g) (source : Nat) :
    dijkstra g source = dijkstraRelax g source := by
  rw [dijkstra, dijkstraHeap_eq_dijkstraRelax vg source]

theorem dijkstra_get_eq_dijkstraRelax (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstra g s.val)[v.val]! = (dijkstraRelax g s.val)[v.val]! := by
  rw [dijkstra, dijkstraHeap_eq_dijkstraRelax vg s.val]

/-- Regression: heap ≡ relax on shared JSON fixture graphs. -/
example : distsMatch (dijkstra tinyChainRust 0) (dijkstraRelax tinyChainRust 0) = true := by
  native_decide

example : distsMatch (dijkstra diamondRust 0) (dijkstraRelax diamondRust 0) = true := by
  native_decide

example : distsMatch (dijkstra unreachableRust 0) (dijkstraRelax unreachableRust 0) = true := by
  native_decide

example : distsMatch (dijkstra singleVertexRust 0) (dijkstraRelax singleVertexRust 0) = true := by
  native_decide

end Refine
end Sssp
