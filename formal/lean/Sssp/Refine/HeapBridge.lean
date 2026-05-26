/-
  Sssp.Refine.HeapBridge

  Connect lazy-heap `dijkstraHeap` to `dijkstraRelax` (Phase 3b heap step).
  Per-step simulation is in `HeapSimulation`; the remaining obligation is
  `dijkstraHeap_eq_dijkstraRelax_of_schedule` (heap fuel schedule = `n` relax rounds).
-/

import Sssp.Refine.HeapSimulation

namespace Sssp
namespace Refine

open Sssp Fixtures

variable {n : ℕ} {g : RustGraph}

/-- Lazy-heap Dijkstra agrees with the proof-relevant relaxation model on valid
    CSR graphs (nat weights, out-degree ≤ 2). Fixture vectors checked below.

    Proof route: `dijkstraHeap_eq_dijkstraRun` + `simInv_dist_eq` once heap fuel
    schedule matches `relaxRound g.n (initEstimate s)` (see `HeapSimulation`). -/
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
