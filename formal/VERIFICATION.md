# Dijkstra verification stack

This document maps the **full verification path** from Rust executable code to
the verified `Sssp.Algo` algorithm. Phase 3b closed the main functional theorem;
this is the roadmap to **zero trusted axioms** and a **Rust refinement proof**.

## Layer diagram

```mermaid
flowchart TB
  subgraph rust [Rust CI]
    RS["src/dijkstra.rs\ndijkstra()"]
    RG["src/graph.rs\nCSR Graph"]
  end
  subgraph refine [Operational Lean]
    RD["Sssp.Refine.Dijkstra\ndijkstra = dijkstraHeap"]
    RR["dijkstraRelax\nn-round float relax"]
  end
  subgraph proof [Proof chain]
    HB["HeapBridge\naxiom + 3 conditional routes"]
    RB["RelaxBridge\nproved"]
    SIM["Simulation\nSimInv + fuel"]
  end
  subgraph verified [Verified]
    AL["Sssp.Algo.Dijkstra\ndijkstra_correct"]
    TD["trueDist / trueDistNat"]
  end
  RS -. "intended refine" .-> RD
  RG -. "CSR layout" .-> RD
  RD --> HB --> RR --> RB --> SIM --> AL --> TD
```

## Theorems (current)

| Statement | Module | Status |
|-----------|--------|--------|
| `Algo.dijkstra G s v = trueDist G s v` | `Sssp.Algo.Dijkstra` | **Proved** |
| `dijkstraRelax … = nnrealToFloat (Algo.dijkstra …)` | `Simulation` | **Proved** (RelaxBridge axiom-free) |
| `refine_dijkstraRelax_correct` | `RefineCorrectness` | **Proved** |
| `refine_dijkstra_correct` (heap) | `RefineCorrectness` | **Proved** (via HeapBridge axiom) |
| `dijkstraHeap_eq_dijkstraRelax_of_upper` | `HeapBridge` | **Proved** (conditional) |
| `dijkstraHeap_eq_dijkstraRelax_of_complete` | `HeapBridge` | **Proved** (conditional) |
| `dijkstraHeap_eq_dijkstraRelax_of_edgeUpper` | `HeapBridge` | **Proved** (conditional) |
| `dijkstraHeap = dijkstraRelax` | `HeapBridge` | **Axiom** (:23) + fixture `native_decide` |
| Rust `dijkstra` refines `Refine.dijkstra` | — | **Not started** |

Main unconditional theorem:

```lean
theorem refine_dijkstra_correct (vg : ValidRustGraph n g) (s v : Fin n) :
  (dijkstra g s.val)[v.val]! = withTopNatToFloat (trueDistNat vg.toGraph s v)
```

## Trusted axioms (elimination order)

Work in this order — each step unlocks the next:

### 1. Numeric bridge (`Sssp.Refine.NumericBridge`)

21 axioms documenting IEEE-754 behaviour for nat-cast weights.

| Axiom group | Replacement strategy |
|-------------|---------------------|
| `floatWeight_add`, `floatWeight_lt_iff`, `floatWeight_le_iff` | Peano induction + IEEE lemmas, or restrict to `Float.ofNat` |
| `floatWeight_eq_ofNat` | Link Peano `floatWeight` to `Float.ofNat` |
| `nnrealToFloat_add_weight` | Prove for `.some` nat casts; `⊤` case separate |
| `nnrealToFloat_monotone`, `nnrealToFloat_trueDist_add` | From `Sound` + path lemmas |

**Proved:** `nnrealToFloat_add_weight_ofNat`.

### 2. CSR relax alignment (`Sssp.Refine.RelaxBridge`) — **DONE**

All former alignment axioms discharged. Per-edge and round-level simulation proofs
in `RelaxBridge` + `Simulation`.

### 3. Graph bridge (`Sssp.Refine.GraphBridge`) — **DONE**

`outEdge_floatWeight_preimage` proved. Fixture `ValidRustGraph` instances are **proved** (no axioms).

### 4. Heap simulation (`Sssp.Refine.HeapBridge`)

| Item | Status |
|------|--------|
| `dijkstraHeap_eq_dijkstraRelax_of_{upper,complete,edgeUpper}` | **Proved** |
| `dijkstraHeap_eq_dijkstraRelax` | **Axiom** — sole open obligation: prove `dijkstraRun_dHat_all_complete_at_heapFuel`, then discharge via `dijkstraHeap_eq_dijkstraRelax_of_complete` |

Model matches `src/dijkstra.rs`: lazy min-heap, stale-entry skip, same relax condition.

### 5. Rust refinement (`src/dijkstra.rs`)

Hand proof or (future) Lean export that:

- `Graph` CSR layout matches `RustGraph.fromEdgeList`
- Loop body matches `dijkstraStep` / `dijkstraRun`
- `f64::INFINITY` = `distInf`, integer weights = `floatWeight w`

## Regression harness

```bash
cd formal/lean && lake build
./formal/scripts/check-fixtures.sh   # Lean #guard + Rust JSON fixtures
cargo test shared_json_fixtures
```

Fixtures prove **operational agreement**; they do not replace proof obligations above.

## Next milestone

**Phase 3c.4:** prove `dijkstraRun_dHat_all_complete_at_heapFuel` to discharge the
last HeapBridge axiom. NumericBridge (21 axioms) remains the long pole.
Phase 4 (`DStruct`, …) stays blocked until Phase 3c axioms are gone or explicitly deferred.
