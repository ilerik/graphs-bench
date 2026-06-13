# Proof Dependency Graph

This document traces the theorem dependency chain from abstract `trueDist` to the Rust `dijkstra` implementation.

## Main Theorem Chain

```
trueDist G s v                    (Mathlib metric: infimum over walks)
    │
    ▼
dijkstraSpec G s v                (Oracle: Classically.choose)
    │    dijkstraSpec_correct     (trivial by construction)
    ▼
Algo.dijkstra G s v              (n-round relaxation)
    │    dijkstra_correct         (proved: Algo/Dijkstra.lean:479)
    ▼
relaxRound G n (initEstimate s)   (fuel-bounded relaxation)
    │    relaxRound_le_initWalk    (completeness)
    │    dijkstra_ge_trueDist     (soundness)
    ▼
══════════════════════════════════════════════════════════════
                    REFINEMENT LAYER
══════════════════════════════════════════════════════════════
    │
    ▼
dijkstraRelax g source            (CSR float relaxation)
    │    dijkstraRelax_dist_eq_nnreal   (Refine/Simulation.lean)
    │    ⚠️ depends on NumericBridge axioms
    ▼
dijkstraHeap g source             (Lazy min-heap implementation)
    │    dijkstraHeap_eq_dijkstraRelax (⚠️ AXIOM: HeapBridge.lean:23)
    │    └── Conditional routes:
    │        • of_upper      (requires schedule bound)
    │        • of_complete   (requires all vertices complete)
    │        • of_edgeUpper  (requires edge-upper bounds)
    │        • of_settlement (requires HeapSettlement)
    ▼
Refine.dijkstra g source          (Entry point: mirrors Rust)
    │    refine_dijkstra_correct
    ▼
══════════════════════════════════════════════════════════════
                    RUST BRIDGE
══════════════════════════════════════════════════════════════
    │
    ▼
src/dijkstra.rs: dijkstra(&g, source)
    │    (hand-checked correspondence)
    ▼
f64 distances in Vec<f64>
```

## Bridge Axiom Details

### NumericBridge (21 axioms)

| Axiom | Purpose | File:Line |
|-------|---------|-----------|
| `floatWeight_eq_ofNat` | `Float.ofNat` correspondence | NumericBridge.lean:80 |
| `floatZero_add` | Additive identity | :81 |
| `float_add_assoc` | Associativity | :82 |
| `float_add_comm` | Commutativity | :83 |
| `floatWeight_add` | Nat addition preserves cast | :84 |
| `floatWeight_lt_iff` | Order reflection | :85 |
| `floatWeight_le_iff` | Order reflection | :86 |
| `float_le_antisymm` | Antisymmetry | :87 |
| `float_le_refl` | Reflexivity | :88 |
| `float_le_top` | Infinity bound | :89 |
| `nnrealToFloat_monotone` | Monotonicity | :96 |
| `nnrealToFloat_trueDist_add` | Path addition | :98-100 |
| `nnrealToFloat_add_weight` | Weight addition | :109-110 |
| `nnrealToFloat_min` | Min commutes | :113-114 |
| `float_min_eq_left_of_lt` | Min selection | :116 |
| `float_min_eq_left_of_le` | Min selection | :117 |
| `float_min_eq_right_of_le` | Min selection | :118 |
| `float_le_of_not_lt` | Trichotomy | :119 |
| `float_le_of_lt` | Order implication | :120 |
| `float_le_trans` | Transitivity | :121 |
| `float_eq_of_beq` | Boolean equality | :122 |

### HeapBridge (1 axiom)

| Axiom | Purpose | File:Line |
|-------|---------|-----------|
| `dijkstraHeap_eq_dijkstraRelax` | Lazy heap = n-round relax | HeapBridge.lean:23 |

**Conditional discharge routes (proved):**
- `dijkstraHeap_eq_dijkstraRelax_of_upper` (:27)
- `dijkstraHeap_eq_dijkstraRelax_of_complete` (:43)
- `dijkstraHeap_eq_dijkstraRelax_of_edgeUpper` (:55)
- `dijkstraHeap_eq_dijkstraRelax_of_settlement` (:72)

## Proved Bridges (Axiom-Free)

### RelaxBridge
- `floatRelaxEdge_aligned` — single-edge alignment
- `floatRelaxOut_aligned` — out-edge alignment
- `floatRelaxAll_simInv` — round alignment
- `SimInv` invariant preservation

### GraphBridge
- `ValidRustGraph` — CSR validity predicate
- `csrToGraph` — graph construction
- `mem_edges_csrToGraph` — edge membership bridge
- `outEdges_card` — degree correspondence

## Key Invariants

### SimInv (Refine/RelaxBridge.lean:21)
```lean
structure SimInv (vg : ValidRustGraph n g) (s : Fin n)
    (dist : List Float) (dHat : DistEstimate n) : Prop where
  len : dist.length = n
  aligned : ∀ v : Fin n, dist[v.val]! = nnrealToFloat (dHat v)
  sound : Sound vg.toGraph s dHat
```

### HeapStateInv (Refine/HeapSimulation.lean)
- Heap entries sorted by distance
- Stale entries have `dist[v] < entry.d`
- Fresh entries match current distance

### HeapSettlement (Refine/HeapSimulation.lean:1556)
```lean
structure HeapSettlement (vg : ValidRustGraph n g) (s : Fin n) : Prop where
  freshCount_ge : n + 1 ≤ dijkstraRun_freshCount (dijkstraHeapFuel g) ...
  processed_univ : dijkstraRun_processed ... = Finset.univ
  setComplete_univ : SetComplete ... Finset.univ
  processedEdgeUpper : ProcessedEdgeUpper ...
```

## Proof Statistics

| Module | Theorems | Axioms | Lines |
|--------|----------|--------|-------|
| `Algo/Dijkstra.lean` | 19 | 0 | 498 |
| `Refine/RelaxBridge.lean` | ~15 | 0 | 533 |
| `Refine/GraphBridge.lean` | ~12 | 0 | 347 |
| `Refine/NumericBridge.lean` | 5 | 21 | 136 |
| `Refine/HeapBridge.lean` | 6 | 1 | 98 |
| `Refine/HeapSimulation.lean` | ~50 | 0 | 1610 |
| `Refine/Simulation.lean` | ~10 | 0 | ~300 |
| `Refine/RefineCorrectness.lean` | 9 | 0 | 62 |

## Verification Commands

```bash
# Lean proofs
cd formal/lean && lake build

# Rust fixtures
cargo test shared_json_fixtures

# Full CI
./formal/scripts/check-fixtures.sh
```
