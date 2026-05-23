# `paper/` --- arXiv preprint draft

This directory contains the LaTeX source of the article

> *A Verified Floating-Point Dijkstra in Lean 4 + Rust:
>  with a Bridge-Axiom Inventory toward Zero-Trust Refinement*

accompanying the `graphs-bench` repository.  The companion vendored copy of
Duan et al. (arXiv:2504.17033) is at `formal/paper/`; this directory is
strictly *our* paper.

## Layout

```
paper/
├── paper.tex   ← single-file source (article class, A4, 11pt)
├── refs.bib    ← bibliography (~50 entries; \todo{} flags items
│                 that should be cross-checked before submission)
├── Makefile    ← convenience targets
└── README.md   ← this file
```

## Build

LaTeX is **not** installed in the development container by default.  To
typeset locally:

```bash
# Debian/Ubuntu (recommended set):
sudo apt-get install texlive-latex-recommended texlive-fonts-recommended \
                     texlive-latex-extra latexmk

# macOS (MacTeX):
brew install --cask mactex

# Then:
make           # latexmk if available, else 3-pass pdflatex+bibtex
make clean     # remove aux/log/bbl/blg/...
make check     # lint TODO/cite/unused-refs
```

The Makefile auto-detects `latexmk`; without it, it runs the standard
`pdflatex / bibtex / pdflatex / pdflatex` pipeline.

The source is **resilient to a minimal TeX install** (just `texlive-base`
plus `texlive-latex-base`): `microtype`, `mathtools`, `xcolor`, `hyperref`,
`cleveref`, `enumitem`, `listings`, and `booktabs` are all loaded
conditionally with `\IfFileExists` and graceful fallbacks. The current
draft has been verified to compile cleanly in this minimal environment to
a 15-page, ~457 KB PDF (0 errors, 0 undefined references; one cosmetic
font-shape warning for bold-smallcaps; two mild overfull boxes inside
non-goal bullet items where unbreakable math like
`$(n-1)\cdot\mathrm{ulp}$-style` resists wrapping).

For a full installation with `latexmk`, `microtype`, etc., the file simply
loads those packages and uses the colour-aware variants automatically.

## Status

* **Sections drafted in full**:
  * §1 Introduction (with explicit contribution list keyed to Lean files)
  * §2 Related work (six paragraphs, ~50 citations)
* **Section stubs** (skeleton + `\todo{}` outline only):
  * §3 Preliminaries
  * §4 Architecture
  * §5 Verified abstract Dijkstra
  * §6 Refinement to Rust
  * §7 Fixture harness
  * §8 Benchmark
  * §9 Discussion
* `\todo{verify: ...}` markers in `refs.bib` flag a handful of secondary
  citations whose exact bibliographic details should be confirmed before
  submission (Mange & Kuhn 2007 EPFL TR; Kani 2022 ASE author list;
  VCFloat 2 vs LAProof attribution).

## Citation density

The two drafted sections cite, end-to-end:

* **Mechanized Dijkstra**: Chen 2003, Moore--Zhang 2005, Mange--Kuhn 2007,
  Klasen 2010, Liu--Nagel--Taghdiri 2012, Filliâtre Toccata 2011,
  Nordhoff--Lammich AFP 2012, Lammich--Nipkow ITP 2019,
  Wimmer--Lammich AFP 2017, Leino *Program Proofs* 2023,
  Mohan--Leow--Hobor CAV 2021, Wang et al.\ OOPSLA 2019, Wang PhD 2019,
  Charguéraud ICFP 2011.
* **Lean / Mathlib**: de Moura--Ullrich CADE 2021, the Mathlib paper CPP 2020,
  `SimpleGraph` and `Quiver` documentation, Doczkal--Pous JAR 2020,
  Noschinski 2015 graph library, Lammich--Sefidgar ITP 2016 Edmonds--Karp.
* **Rust verification**: Verus OOPSLA 2023 + SOSP 2024,
  Creusot ICFEM 2022, Aeneas ICFP 2022 + ICFP 2024,
  Prusti OOPSLA 2019 + NFM 2022, Kani ASE 2022, RustHorn TOPLAS 2021,
  RustHornBelt PLDI 2022, hax/hacspec project, RustBelt POPL 2018.
* **Floating-point**: Flocq ARITH 2011, Boldo--Melquiond book 2017,
  CompCert FP JAR 2015, Boldo--Filliâtre--Melquiond 2009 Gappa,
  VCFloat 2 / LAProof CPP 2024, Ramananandro et al.\ CPP 2016,
  Higham 2002, IEEE 754-2019.
* **Cost / extraction / refinement**:
  Charguéraud--Pottier ITP 2015 + JAR 2019,
  Guéneau--Charguéraud--Pottier ESOP 2018,
  Lammich JAR 2019 + ITP 2019 (Imperative HOL → LLVM),
  Letouzey TYPES 2002, MetaCoq JAR 2020, CertiCoq 2017,
  Hoffmann--Das--Weng POPL 2017, Carbonneaux et al.\ CAV 2017.

## Conventions

* **Cross-references** between paper text and Lean proof use
  `formal/lean/Sssp/Algo/Dijkstra.lean:318` paths in the same form the
  README uses, so a reader can `git grep` directly.
* **Algorithm name**: `\BMSSP` is the macro for the new
  $\mathcal{O}(m \log^{2/3} n)$ algorithm of
  Duan, Mao, Mao, Shu, Yin (arXiv:2504.17033, STOC 2025).
* **Honesty**: every claim about the formal development is accompanied by
  an explicit Lean file path; nothing is asserted that is not in the repo.
