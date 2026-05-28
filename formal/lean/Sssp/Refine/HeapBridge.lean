/-
  Sssp.Refine.HeapBridge

  Connect lazy-heap `dijkstraHeap` to `dijkstraRelax` (Phase 3b heap step).
  Per-step simulation is in `HeapSimulation`; the remaining obligation is
  `dijkstraHeap_eq_dijkstraRelax_of_schedule` (heap fuel schedule = `n` relax rounds).
-/

import Sssp.Refine.HeapSimulation

namespace Sssp
namespace Refine

open Sssp Fixtures Algo

variable {n : ℕ} {g : RustGraph}

/-- Lazy-heap Dijkstra agrees with the proof-relevant relaxation model on valid
    CSR graphs (nat weights, out-degree ≤ 2). Fixture vectors checked below.

    Proof route: `dijkstraHeap_eq_dijkstraRelax_of_schedule` + unconditional
    `dijkstraRun_dHat_schedule` once `dijkstraRun_dHat_all_complete_at_heapFuel` is proved. -/
axiom dijkstraHeap_eq_dijkstraRelax (vg : ValidRustGraph n g) (source : Nat) :
    dijkstraHeap g source = dijkstraRelax g source

/-- Same conclusion, assuming the upper-bound route to heap-side completeness. -/
theorem dijkstraHeap_eq_dijkstraRelax_of_upper {vg : ValidRustGraph n g} (s : Fin n)
    (hUpper :
      ∀ v : Fin n,
        dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) v ≤
          Algo.relaxRound vg.toGraph n (initEstimate s) v) :
    dijkstraHeap g s.val = dijkstraRelax g s.val := by
  have hSchedule :
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph g.n (initEstimate s) := by
    rw [vg.hn]
    exact dijkstraRun_dHat_schedule_of_upper (vg := vg) s hUpper
  exact dijkstraHeap_eq_dijkstraRelax_of_schedule (vg := vg) s hSchedule

/-- Same conclusion, assuming heap-side completeness at `dijkstraHeapFuel`. -/
theorem dijkstraHeap_eq_dijkstraRelax_of_complete {vg : ValidRustGraph n g} (s : Fin n)
    (hComplete :
      ∀ v : Fin n,
        IsComplete vg.toGraph s
          (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
            (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v) :
    dijkstraHeap g s.val = dijkstraRelax g s.val := by
  rw [dijkstraHeap_eq_dijkstraRun, dijkstraRelax]
  simpa [vg.hn] using
    dijkstraRun_eq_floatRelaxRound_of_heap_complete (vg := vg) s (dijkstraHeapFuel g) n rfl hComplete

/-- Same conclusion, assuming edge-upper bounds at `dijkstraHeapFuel`. -/
theorem dijkstraHeap_eq_dijkstraRelax_of_edgeUpper {vg : ValidRustGraph n g} (s : Fin n)
    (hEdge : EdgeUpper vg.toGraph s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))) :
    dijkstraHeap g s.val = dijkstraRelax g s.val := by
  have hComplete := dijkstraRun_dHat_all_complete_of_edgeUpper (vg := vg) s (dijkstraHeapFuel g) hEdge
  exact dijkstraHeap_eq_dijkstraRelax_of_complete (vg := vg) s hComplete

theorem dijkstra_eq_dijkstraRelax (vg : ValidRustGraph n g) (source : Nat) :
    dijkstra g source = dijkstraRelax g source := by
  rw [dijkstra, dijkstraHeap_eq_dijkstraRelax vg source]

theorem dijkstra_get_eq_dijkstraRelax (vg : ValidRustGraph n g) (s v : Fin n) :
    (dijkstra g s.val)[v.val]! = (dijkstraRelax g s.val)[v.val]! := by
  rw [dijkstra, dijkstraHeap_eq_dijkstraRelax vg s.val]

/-- Discharge the heap bridge once `HeapSettlement` holds (see `HeapSimulation`). -/
theorem dijkstraHeap_eq_dijkstraRelax_of_settlement {vg : ValidRustGraph n g} (s : Fin n)
    (hSettle : HeapSettlement vg s) :
    dijkstraHeap g s.val = dijkstraRelax g s.val := by
  have hSchedule :=
    dijkstraRun_dHat_schedule_of_settlement (vg := vg) s hSettle
  have hSchedule' :
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph g.n (initEstimate s) := by
    simpa [vg.hn] using hSchedule
  exact dijkstraHeap_eq_dijkstraRelax_of_schedule (vg := vg) s hSchedule'

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
