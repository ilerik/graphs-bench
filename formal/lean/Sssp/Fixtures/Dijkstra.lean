/-
  Sssp.Fixtures.Dijkstra

  Regression checks for shared JSON fixture vectors under
  `formal/fixtures/dijkstra/`.  Rust cross-checks the same files via
  `cargo test shared_json_fixtures`.

  The verified `Sssp.Algo.dijkstra` is noncomputable (`DistEstimate`), so
  executable checks use `Sssp.Refine.dijkstra` on `RustGraph`.
-/

import Mathlib
import Sssp.Fixtures.Graph
import Sssp.Algo.Dijkstra

namespace Sssp
namespace Fixtures

open Sssp Refine

def tinyChainExpected : List Float := [0.0, 1.0, 3.0, 6.0]
def diamondExpected : List Float := [0.0, 1.0, 1.0, 2.0]
def unreachableExpected : List Float := [0.0, 1.0, 3.0, distInf, distInf]
def singleVertexExpected : List Float := [0.0]

/-- Compare distances; treat matching `inf` sentinels as equal. -/
def floatEq (a b : Float) : Bool :=
  a == b || (a.isInf && b.isInf)

def distsMatch (got exp : List Float) : Bool :=
  got.length == exp.length &&
    (got.zip exp).all fun p => floatEq p.1 p.2

example : distsMatch (dijkstra tinyChainRust 0) tinyChainExpected = true := by native_decide
example : distsMatch (dijkstra diamondRust 0) diamondExpected = true := by native_decide
example : distsMatch (dijkstra unreachableRust 0) unreachableExpected = true := by native_decide
example : distsMatch (dijkstra singleVertexRust 0) singleVertexExpected = true := by native_decide

#guard distsMatch (dijkstra tinyChainRust 0) tinyChainExpected
#guard distsMatch (dijkstra diamondRust 0) diamondExpected
#guard distsMatch (dijkstra unreachableRust 0) unreachableExpected
#guard distsMatch (dijkstra singleVertexRust 0) singleVertexExpected

section evalSmoke

#eval dijkstra tinyChainRust 0
#eval dijkstra diamondRust 0
#eval dijkstra unreachableRust 0
#eval dijkstra singleVertexRust 0

end evalSmoke

end Fixtures
end Sssp
