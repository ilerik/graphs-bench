# Formal Verification of `graphs-bench`

This directory bundles everything needed to formally verify, in **Lean 4 +
Mathlib**, the underlying algorithms implemented in `../src/`:

* the partial-sorting data structure `D` (`src/dstruct.rs` ↔ `Sssp.DStruct`),
* `FindPivots` (`src/bmssp.rs:81` ↔ `Sssp.FindPivots`),
* `BaseCase` (`src/bmssp.rs:201` ↔ `Sssp.BaseCase`),
* `BMSSP` (`src/bmssp.rs:265` ↔ `Sssp.BMSSP`),
* the top-level entry point `sssp_bmssp` (`src/bmssp.rs:12` ↔ `Sssp.Main`),
* and, as a baseline, textbook Dijkstra (`src/dijkstra.rs` ↔ `Sssp.Dijkstra`).

against the algorithm of

> Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> arXiv:[2504.17033v2](https://arxiv.org/abs/2504.17033) (July 2025).

## Layout

```
formal/
├── README.md                  ← this file: verification plan
├── paper/
│   ├── 2504.17033v2.pdf       ← the article (17 pp. PDF)
│   ├── 2504.17033.tar.gz      ← arXiv TeX source archive
│   └── source/                ← extracted TeX sources
│       ├── main.tex           ← root document
│       ├── preliminary.tex    ← §2 (notation, comparison-addition model,
│       │                        Assumption 2.1 distinct path lengths)
│       ├── rebundle.tex       ← Algorithm 1 (FindPivots) + Lemma 3.2
│       ├── data_structure.tex ← Lemma 3.3 (the partial-sorting D)
│       ├── main_result.tex    ← Algorithms 2 & 3 (BaseCase, BMSSP),
│       │                        Lemmas 3.1, 3.5–3.12 (correctness +
│       │                        running time)
│       ├── introduction.tex   ← §1
│       ├── discussion.tex     ← §4
│       └── header.tex         ← LaTeX macros and command shortcuts
└── lean/
    ├── lean-toolchain         ← pins `leanprover/lean4:v4.13.0`
    ├── lakefile.toml          ← Lake config; depends on Mathlib v4.13.0
    ├── Sssp.lean              ← root module, re-exports everything
    └── Sssp/
        ├── Graph.lean
        ├── Path.lean          ← walks, distinct-lengths assumption
        ├── Distance.lean      ← d(v), d̂[v], completeness, T(S), T(S^*),
        │                        Ũ-style "expectU" set
        ├── Dijkstra.lean      ← spec & correctness theorem of Dijkstra
        ├── DStruct.lean       ← Lemma 3.3 (Insert / BatchPrepend / Pull)
        ├── FindPivots.lean    ← Algorithm 1 + Lemma 3.2
        ├── BaseCase.lean      ← Algorithm 2
        ├── BMSSP.lean         ← Algorithm 3 + Lemmas 3.1, 3.10, 3.12
        └── Main.lean          ← `sssp_bmssp_correct`, equivalence with
                                  Dijkstra
```

Every theorem is **stated** in Lean. Proofs are currently `sorry`; the file
naming and lemma names are chosen so that each `sorry` corresponds 1-to-1 to
a numbered lemma in the paper (TeX file in `paper/source/`).

## Building

The project uses Lake (Lean's build system) and Mathlib. First-time setup:

```bash
# 0. Install elan (Lean's toolchain manager) — once per machine.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 1. Pull Mathlib's pre-built artifacts (fast — avoids rebuilding from source).
cd formal/lean
lake exe cache get

# 2. Build the project (will type-check every Lean file).
lake build
```

Because every proof is `sorry`, `lake build` will succeed but emit
`declaration uses 'sorry'` warnings — that is the intended state of a
verification *blueprint*. Filling in the proofs is what discharges those
warnings one by one.

## Verification roadmap

The blueprint is structured by paper section, so the natural order of attack
is bottom-up:

1. **`Sssp.Graph`, `Sssp.Path`** — finish the `Walk` predicate
   (`steps_valid`, `endsAt`); supply a constructor lemma for concatenation.
2. **`Sssp.Distance`** — define `trueDist` as the infimum of walk lengths;
   prove the standard triangle inequality and that `trueDist` is preserved
   by edge relaxation. Define `subtree`, `subtreeOf`, `expectU` precisely.
3. **`Sssp.Dijkstra`** — prove `dijkstra_correct`. Standard proof: the
   popped vertex is always complete; relaxation preserves `Sound`. This is
   the easiest theorem in the project and is a good warm-up.
4. **`Sssp.DStruct`** — discharge `pull_size_le`, `pull_separator`,
   `insert_eq`, `batchPrepend_eq` against the abstract `State` model. The
   *amortised running time* claims of Lemma 3.3 are deferred until a cost
   semantics is introduced (see "Future work" below).
5. **`Sssp.FindPivots`** — prove `findPivots_correct` (Lemma 3.2). The
   forest-of-tight-edges argument requires `HasDistinctLengths`. The Rust
   implementation at `src/bmssp.rs:81` mirrors the algorithm exactly and is
   the de-facto reference.
6. **`Sssp.BaseCase`** — prove `baseCase_correct` (Lemma 3.1, base case).
   Reduces to a bounded Dijkstra; reuses lemmas from step 3.
7. **`Sssp.BMSSP`** — prove `bmssp_correct` by induction on `l`. This is
   the main theorem and follows §3.5 *Correctness Analysis* of the paper
   (`paper/source/main_result.tex`, `lemma:main-algo-correctness`). The
   four propositions (a)–(b) of the inductive invariant are stated in
   the proof comments.
8. **`Sssp.BMSSP` (size bound)** — prove `bmssp_size_bound` (Lemma 3.10);
   straightforward induction once `bmssp_correct` is in place.
9. **`Sssp.Main`** — prove `sssp_bmssp_correct` and the corollary
   `sssp_bmssp_eq_dijkstra`. The crucial argument is that the top-level
   call is *always successful* because `|U| ≤ n ≤ k · 2^{L·t}` (this is the
   `hL` hypothesis on the theorem).

### Out-of-scope until "running time" is formalised

The `O(m log^{2/3} n)` bound (Lemma 3.12 in `paper/source/main_result.tex`,
`lemma:main-algo-time`) is a statement *about a cost model*, not about an
extensional input/output relation. Two possible approaches:

* a *step-counting monad* à la Mathlib's `MonadCounter`, where every primitive
  operation increments a counter; or
* an axiomatic `cost : Op → ℕ` plus an inductive bound on the recursion tree
  (cleanest, follows the paper's amortised analysis verbatim).

Either way, the running-time theorem can be added as `Sssp.Time` once the
correctness blueprint is fully discharged.

## How the Lean modules track the paper

| Lean file                  | Paper artefact                                           | Rust source              |
|----------------------------|----------------------------------------------------------|--------------------------|
| `Sssp.Graph`               | §2 *Preliminaries*, constant-degree assumption           | `src/graph.rs`           |
| `Sssp.Path`                | §2 Assumption 2.1                                        | (implicit, unique paths) |
| `Sssp.Distance`            | §3.5 *T(S), T(S^*), T_{<B}(S)*, completeness             | `Context.d` in `bmssp.rs`|
| `Sssp.Dijkstra`            | §1 baseline                                              | `src/dijkstra.rs`        |
| `Sssp.DStruct`             | Lemma 3.3 (`data_structure.tex`)                          | `src/dstruct.rs`         |
| `Sssp.FindPivots`          | Algorithm 1 + Lemma 3.2 (`rebundle.tex`)                  | `find_pivots` (bmssp.rs) |
| `Sssp.BaseCase`            | Algorithm 2 (`main_result.tex` ll. 133–167)               | `base_case` (bmssp.rs)   |
| `Sssp.BMSSP`               | Algorithm 3 + Lemmas 3.1, 3.10, 3.12                     | `bmssp` (bmssp.rs)       |
| `Sssp.Main`                | "Top-level call" (`main_result.tex` line 47)              | `sssp_bmssp` (bmssp.rs)  |

## Re-fetching the paper

The PDF and TeX archive in `paper/` were downloaded from arXiv with

```bash
curl -sSL -o formal/paper/2504.17033v2.pdf  https://arxiv.org/pdf/2504.17033v2.pdf
curl -sSL -o formal/paper/2504.17033.tar.gz https://arxiv.org/e-print/2504.17033v2
tar -xzf formal/paper/2504.17033.tar.gz -C formal/paper/source
```

The article is distributed under arXiv's non-exclusive license; please cite
the original authors when redistributing.
