/-
  Sssp.Graph

  Directed graphs with non-negative real edge weights, parameterised by the
  number of vertices `n`. Mirrors `src/graph.rs` (CSR-encoded `Graph`) but
  models everything as honest sets / functions instead of arrays.

  We work in the comparison-addition model on real numbers throughout, so
  weights live in `ℝ≥0` (encoded as `{w : ℝ // 0 ≤ w}` via `Mathlib`'s
  `NNReal`).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

namespace Sssp

/-- A finite directed graph on vertex set `Fin n` with non-negative real
    weights. Multiple edges with different weights are allowed (the algorithm
    only ever cares about the minimum-weight edge between two vertices when
    relaxing). -/
structure Graph (n : ℕ) where
  /-- `edges u v` is the (finite) multiset of weights of edges `u → v`. -/
  edges : Fin n → Fin n → Multiset NNReal
  /-- Constant-degree assumption (Frederickson reduction, §2 of the paper).
      The constant `2` matches the bound in the paper after the reduction. -/
  outDeg_le : ∀ u : Fin n, ((Finset.univ : Finset (Fin n)).sum
                  (fun v => (edges u v).card)) ≤ 2

namespace Graph

variable {n : ℕ} (G : Graph n)

/-- The flat set of out-edges from `u`: pairs `(v, w)` with `(u,v)` carrying
    weight `w` somewhere in `edges u v`. -/
def outEdges (u : Fin n) : Multiset (Fin n × NNReal) :=
  (Finset.univ : Finset (Fin n)).val.bind
    (fun v => (G.edges u v).map (Prod.mk v))

/-- Out-degree of `u` (with multiplicities). -/
def outDegree (u : Fin n) : ℕ :=
  (G.outEdges u).card

/-- `m`, the number of edges of `G`. -/
noncomputable def numEdges : ℕ :=
  ∑ u, G.outDegree u

end Graph
end Sssp
