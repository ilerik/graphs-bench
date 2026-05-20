# Formal verification of `graphs-bench`

This directory bundles everything needed to formally verify, in **Lean 4 +
Mathlib**, the algorithms implemented in `../src/`.  Target paper:

> Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> arXiv:[2504.17033v2](https://arxiv.org/abs/2504.17033) (July 2025).

## ⚠️ Honest verification status (as of Phase 0 of the roadmap)

The Lean code in `lean/` compiles without `sorry`, but **most of the
algorithmic content is not yet verified**.  The current architecture is a
**specification + algorithm** split:

* `Sssp.<X>`           — *specification* of operation `<X>`, given as an
  oracle definition (often `Classical.choose`-based) whose correctness
  lemma `<x>Spec_correct` is vacuously true by construction.  This is the
  paper's input/output contract, expressed in Lean.

* `Sssp.Algo.<X>`      — *real, computable, verified* implementation of
  `<X>`, proved to satisfy `<X>Spec_correct`.  This is where actual
  algorithmic content lives.

| Module             | Status                                          | Algorithmic content       |
|--------------------|-------------------------------------------------|---------------------------|
| `Sssp.Graph`       | Honest data definitions                          | n/a                       |
| `Sssp.Path`        | Honest, finished proofs (`Walk`, `length_append`)| n/a                       |
| `Sssp.Distance`    | Honest, finished proofs                          | `trueDist_triangle`, `exists_truncation_witness` |
| `Sssp.Dijkstra`    | Spec + shared lemmas (`relax_sound`, …)           | none (spec oracle)        |
| `Sssp.DStruct`     | **`pullSpec` is an oracle** returning ∅           | `insert_eq`, `batchPrepend_eq` |
| `Sssp.FindPivots`  | **Spec only.** No Bellman-Ford performed          | none                      |
| `Sssp.BaseCase`    | **Spec only.** No mini-Dijkstra performed         | none                      |
| `Sssp.BMSSP`       | **Spec only.** Inductive step does not recurse    | none                      |
| `Sssp.Main`        | **Spec only.** Vacuous "successful execution"     | none                      |
| `Sssp.Algo.Dijkstra` | **Verified (Phase 3).** `dijkstra_correct`       | `n`-round relaxation      |
| `Sssp.Refine.Dijkstra` | Operational Float/CSR/lazy-heap model           | mirrors `src/dijkstra.rs` |
| `Sssp.Fixtures.Dijkstra` | `#eval` smoke on shared fixture graphs          | —                        |
| `Sssp.Algo.DStruct`  | TBD (Phase 4).                                  | block-list with amortised costs |
| `Sssp.Algo.FindPivots` | TBD (Phase 5).                                | k-round Bellman-Ford      |
| `Sssp.Algo.BaseCase`   | TBD (Phase 6).                                | bounded mini-Dijkstra     |
| `Sssp.Algo.BMSSP`      | TBD (Phase 7).                                | well-founded recursion + `D` |
| `Sssp.Algo.Main`       | TBD (Phase 8).                                | top-level driver + Lemma 3.12 |

Where the table says "Algorithmic content: none", the `<x>Spec` definition
and its `<x>Spec_correct` proof do not constitute a verification of the
paper's algorithm — they only assert that an answer satisfying the
algorithm's input/output contract exists.

The roadmap in `formal/README.md` (this file) plans the migration of each
operation from `Sssp.<X>` (oracle) to `Sssp.Algo.<X>` (real).

## Layout

```
formal/
├── README.md                  ← this file: verification plan
├── paper/
│   ├── 2504.17033v2.pdf       ← the article (17 pp. PDF)
│   ├── 2504.17033.tar.gz      ← arXiv TeX source archive
│   └── source/                ← extracted TeX sources
└── lean/
    ├── lean-toolchain         ← pins `leanprover/lean4:v4.29.1`
    ├── lakefile.toml          ← Lake config; depends on Mathlib v4.29.1
    ├── Sssp.lean              ← root module, re-exports everything
    └── Sssp/
        ├── Graph.lean
        ├── Path.lean          ← walks, distinct-lengths assumption
        ├── Distance.lean      ← d(v), d̂[v], completeness, T(S), T(S^*),
        │                        truncation-witness existence theorem
        ├── Dijkstra.lean      ← spec: dijkstraSpec, dijkstraSpec_correct,
        │                        relax_sound  (real Dijkstra in Algo/)
        ├── DStruct.lean       ← spec for Pull/Insert/BatchPrepend
        ├── FindPivots.lean    ← spec only
        ├── BaseCase.lean      ← spec only
        ├── BMSSP.lean         ← spec only
        ├── Main.lean          ← spec only
        └── Algo/
            └── Dijkstra.lean  ← real verified Dijkstra (computable)
```

## Building

The project uses Lake (Lean's build system) and Mathlib.  First-time setup:

```bash
# 0. Install elan (Lean's toolchain manager) — once per machine.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 1. Pull Mathlib's pre-built artifacts (fast — avoids rebuilding from source).
cd formal/lean
lake exe cache get

# 2. Build the project.
lake build
```

`lake build` should succeed without warnings.  Spec-side modules elaborate
because their definitions are designed to satisfy their own theorems
trivially; the `Sssp.Algo.<X>` modules contain the genuine proofs.

## Verification roadmap

The blueprint is structured by paper section.  Phases are ordered by
dependency, so the natural order of attack is bottom-up:

| Phase | Goal                                                                  | Estimate    |
|------:|-----------------------------------------------------------------------|-------------|
| 0     | Honest reset: rename oracles to `<x>Spec`, document status            | done        |
| 1     | Foundation hardening (`Walk`, `Distance`, log conventions)            | 1 week      |
| 2     | Cost-counting monad `CostM`                                           | 2 weeks     |
| 3     | `Sssp.Algo.Dijkstra`: verified relaxation + Refine model + fixtures   | done        |
| 4     | `Sssp.Algo.DStruct`: block-list, amortised costs                       | 3–4 weeks   |
| 5     | `Sssp.Algo.FindPivots`: Bellman-Ford + Lemma 3.2                       | 3 weeks     |
| 6     | `Sssp.Algo.BaseCase`: bounded mini-Dijkstra + Lemma 3.1 base           | 1–2 weeks   |
| 7     | `Sssp.Algo.BMSSP`: well-founded recursion, Lemmas 3.1, 3.10, 3.12       | 4–6 weeks   |
| 8     | `Sssp.Algo.Main`: top-level + equivalence theorem                      | 1 week      |
| 9     | Rust↔Lean refinement (extraction or hand-translated refinement proof)  | 4–8 weeks   |
| 10    | Rust polish: LICENSE, Cargo metadata, CI, criterion benchmarks          | 1 week      |
| 11    | Paper writing + submission (FV venue + SWE venue)                      | 4–8 weeks   |

The `O(m log^{2/3} n)` bound (Lemma 3.12 in
`paper/source/main_result.tex`) is unlocked by Phase 2 (cost monad) and
discharged in Phase 7.

## How the Lean modules track the paper

| Lean file                  | Paper artefact                                           | Rust source              |
|----------------------------|----------------------------------------------------------|--------------------------|
| `Sssp.Graph`               | §2 *Preliminaries*, constant-degree assumption            | `src/graph.rs`           |
| `Sssp.Path`                | §2 Assumption 2.1                                         | (implicit, unique paths) |
| `Sssp.Distance`            | §3.5 *T(S), T(S^\*), T_{<B}(S)*, completeness            | `Context.d` in `bmssp.rs`|
| `Sssp.Dijkstra`            | §1 baseline (spec)                                        | `src/dijkstra.rs`        |
| `Sssp.Algo.Dijkstra`       | §1 baseline (real)                                        | `src/dijkstra.rs`        |
| `Sssp.DStruct`             | Lemma 3.3 (`data_structure.tex`) — spec for Pull          | `src/dstruct.rs`         |
| `Sssp.FindPivots`          | Algorithm 1 + Lemma 3.2 (`rebundle.tex`) — spec only      | `find_pivots` (bmssp.rs) |
| `Sssp.BaseCase`            | Algorithm 2 (`main_result.tex` ll. 133–167) — spec only   | `base_case` (bmssp.rs)   |
| `Sssp.BMSSP`               | Algorithm 3 + Lemmas 3.1, 3.10 — spec only; Lemma 3.12 absent | `bmssp` (bmssp.rs)   |
| `Sssp.Main`                | "Top-level call" (`main_result.tex` line 47) — spec only  | `sssp_bmssp` (bmssp.rs)  |

## Phase 3 fixtures (Dijkstra cross-check)

Shared JSON vectors live under `formal/fixtures/dijkstra/` (`tiny_chain.json`,
`diamond_with_ties.json`, `unreachable_vertices.json`, `single_vertex.json`).
Rust validates them via `cargo test shared_json_fixtures` in `src/dijkstra.rs`
(1e-9 tolerance).  The verified Lean algorithm is `Sssp.Algo.dijkstra`; the
lazy heap operational model is `Sssp.Refine.dijkstra` on `RustGraph`.
Lean `#eval` smoke checks live in `Sssp.Fixtures.Dijkstra` (Refine side only;
`Algo.dijkstra` is noncomputable).  Post–Phase 3 tasks are listed in
`formal/FUTURE_WORK.md`.

## Re-fetching the paper

The PDF and TeX archive in `paper/` were downloaded from arXiv with

```bash
curl -sSL -o formal/paper/2504.17033v2.pdf  https://arxiv.org/pdf/2504.17033v2.pdf
curl -sSL -o formal/paper/2504.17033.tar.gz https://arxiv.org/e-print/2504.17033v2
tar -xzf formal/paper/2504.17033.tar.gz -C formal/paper/source
```

The article is distributed under arXiv's non-exclusive license; please
cite the original authors when redistributing.
