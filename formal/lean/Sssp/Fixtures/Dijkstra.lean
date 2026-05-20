/-
  Sssp.Fixtures.Dijkstra

  `#eval` smoke checks for shared JSON fixture vectors under
  `formal/fixtures/dijkstra/`.  Rust cross-checks the same files via
  `cargo test shared_json_fixtures`.

  The verified `Sssp.Algo.dijkstra` is noncomputable (`DistEstimate`), so
  executable cross-checks use `Sssp.Refine.dijkstra` on `RustGraph`.
-/

import Sssp.Algo.Dijkstra
import Sssp.Refine.Dijkstra

namespace Sssp
namespace Fixtures

open Sssp Refine

/-- Fixture weights are small integers; use the same numeric value in `NNReal` and `Float`. -/
def nnreal (w : Nat) : NNReal := w
def float (w : Nat) : Float := Float.ofNat w

def tinyChainGraph : Graph 4 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 1 ∧ v = 2 then {nnreal 2}
    else if u = 2 ∧ v = 3 then {nnreal 3}
    else {}
  outDeg_le := by intro u; fin_cases u <;> native_decide }

def diamondGraph : Graph 4 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 0 ∧ v = 2 then {nnreal 1}
    else if u = 1 ∧ v = 3 then {nnreal 1}
    else if u = 2 ∧ v = 3 then {nnreal 1}
    else {}
  outDeg_le := by intro u; fin_cases u <;> native_decide }

def unreachableGraph : Graph 5 := {
  edges := fun u v =>
    if u = 0 ∧ v = 1 then {nnreal 1}
    else if u = 1 ∧ v = 2 then {nnreal 2}
    else if u = 3 ∧ v = 4 then {nnreal 1}
    else {}
  outDeg_le := by intro u; fin_cases u <;> native_decide }

def singleVertexGraph : Graph 1 := {
  edges := fun _ _ => {}
  outDeg_le := by intro u; fin_cases u <;> native_decide }

def tinyChainRust : RustGraph :=
  RustGraph.fromEdgeList 4
    [(0, 1, float 1), (1, 2, float 2), (2, 3, float 3)]

def diamondRust : RustGraph :=
  RustGraph.fromEdgeList 4
    [(0, 1, float 1), (0, 2, float 1), (1, 3, float 1), (2, 3, float 1)]

def unreachableRust : RustGraph :=
  RustGraph.fromEdgeList 5
    [(0, 1, float 1), (1, 2, float 2), (3, 4, float 1)]

def singleVertexRust : RustGraph :=
  RustGraph.fromEdgeList 1 []

section evalSmoke

#eval dijkstra tinyChainRust 0
#eval dijkstra diamondRust 0
#eval dijkstra unreachableRust 0
#eval dijkstra singleVertexRust 0

end evalSmoke

end Fixtures
end Sssp
