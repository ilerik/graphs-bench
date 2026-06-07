# Trusted Lean Assumptions

This file is the canonical inventory of trusted Lean declarations in the
current verification stack. The project has no `sorry`/`admit` in `formal/lean`,
but the Dijkstra refinement theorem is not zero-trust yet because it depends on
the `axiom` declarations below.

## Current Claim Boundary

What is currently proved without `sorry`:

- `Sssp.Algo.Dijkstra.dijkstra_correct`: the verified `n`-round relaxation
  algorithm computes `trueDist`.
- `Sssp.Refine.refine_dijkstra_correct`: the operational CSR/Float/lazy-heap
  model matches the verified distance on every `ValidRustGraph`, **assuming**
  the bridge axioms below.
- Fixture regressions: shared JSON examples agree between the Lean operational
  model and Rust tests.

What is not currently proved:

- The Dijkstra refinement stack without trusted axioms.
- Rust `src/dijkstra.rs` as a formal refinement of `Sssp.Refine.dijkstra`.
- Verified implementations of the BMSSP paper primitives (`DStruct`,
  `FindPivots`, `BaseCase`, `BMSSP`, `Main`). Those modules are still mostly
  specs/oracles.

## Numeric Bridge

Module: `formal/lean/Sssp/Refine/NumericBridge.lean`

These axioms model the intended behavior of `Float` for natural-number weights
and the embedding from `WithTop NNReal` to `Float`.

| Declaration | Why it is trusted now | Replacement direction |
|-------------|-----------------------|-----------------------|
| `floatWeight_eq_ofNat` | Links Peano-style `floatWeight` to Lean's `Float.ofNat`. | Prove by induction or change definitions to use one representation. |
| `floatZero_add` | Basic `Float` arithmetic identity. | Replace with a restricted numeric model or prove from Lean `Float` facts. |
| `float_add_assoc` | Associativity is not generally true for IEEE floats. | Avoid by using nat/NNReal model for proof and cast only at the boundary. |
| `float_add_comm` | Commutativity for the restricted nat-weight fragment. | Same as above. |
| `floatWeight_add` | Additivity of nat-weight floats. | Prove for bounded exact naturals or avoid raw `Float` algebra. |
| `floatWeight_lt_iff` | Float order agrees with nat order. | Prove under exactness bounds or replace with integer weights in the model. |
| `floatWeight_le_iff` | Float order agrees with nat order. | Same as above. |
| `float_le_antisymm` | Order antisymmetry for the used float fragment. | Use a dedicated ordered distance type. |
| `float_le_refl` | Reflexivity for the used float fragment. | Use a dedicated ordered distance type. |
| `float_le_top` | `distInf` bounds finite distances. | Prove from the chosen distance model. |
| `nnrealToFloat_monotone` | Monotonicity of the embedding. | Prove after replacing or constraining the float embedding. |
| `nnrealToFloat_trueDist_add` | Triangle-style distance inequality after float embedding. | Derive from `trueDist` path lemmas and monotonicity. |
| `nnrealToFloat_add_weight` | Embedding commutes with adding a nat edge weight. | Extend the proved finite case to `⊤`. |
| `nnrealToFloat_min` | Embedding commutes with `min`. | Prove by case analysis on `WithTop` and order lemmas. |
| `float_min_eq_left_of_lt` | `min` behavior for floats. | Replace with ordered distance type or prove for the fragment. |
| `float_min_eq_left_of_le` | `min` behavior for floats. | Same as above. |
| `float_min_eq_right_of_le` | `min` behavior for floats. | Same as above. |
| `float_le_of_not_lt` | Linear-order behavior for floats. | Same as above. |
| `float_le_of_lt` | Strict-to-nonstrict order bridge. | Same as above. |

## Graph Bridge

Module: `formal/lean/Sssp/Refine/GraphBridge.lean`

| Declaration | Why it is trusted now | Replacement direction |
|-------------|-----------------------|-----------------------|
| `outEdge_floatWeight_preimage` | States that every CSR slot produced by `fromEdgeList` stores some `floatWeight w`. | Prove directly from `RustGraph.fromEdgeList`, `mergeSort`, and the mapped edge list. |

## Relax Bridge

Module: `formal/lean/Sssp/Refine/RelaxBridge.lean`

| Declaration | Why it is trusted now | Replacement direction |
|-------------|-----------------------|-----------------------|
| `relaxOutEdges_eq_relaxCsrOut` | Aligns CSR out-edge fold order with `Graph.outEdges`. | Prove that `relaxCsrOut` is permutation/order compatible with `relaxOutEdges`, or redefine one side to share the same order. |
| `foldl_range_floatRelaxAll_aligned` | Lifts per-vertex relax alignment across all vertices. | Prove by induction over `List.range g.n` using `floatRelaxOut_aligned`. |

## Heap Bridge

Module: `formal/lean/Sssp/Refine/HeapBridge.lean`

| Declaration | Why it is trusted now | Replacement direction |
|-------------|-----------------------|-----------------------|
| `dijkstraHeap_eq_dijkstraRelax` | Connects the lazy-heap operational model to the `n`-round relax model. | Prove loop invariants for `dijkstraRun`: stale-entry safety, heap completeness, and agreement with relaxation on valid nonnegative nat-weight graphs. |

## Specification Oracles

Several paper-level modules use `Classical.choose`-based specs. These are not
Lean `axiom` declarations, but they are still not algorithm implementations:

- `Sssp.DStruct`: `pullSpec` is an oracle-style spec.
- `Sssp.FindPivots`: spec only.
- `Sssp.BaseCase`: spec only.
- `Sssp.BMSSP`: spec only; no real recursive BMSSP proof yet.
- `Sssp.Main`: spec only.

These specs are useful as target contracts, but they should not be presented as
a verification of the BMSSP algorithm.

## How To Audit

Run:

```bash
rg -n "^axiom\\b|\\bsorry\\b|\\badmit\\b" formal/lean
```

Expected today: no `sorry`/`admit`; the `axiom` declarations listed above.
