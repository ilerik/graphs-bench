# Artifact Notes

This repository is a research artifact for experimenting with and documenting
the directed single-source shortest path algorithm from:

> Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin.
> *Breaking the Sorting Barrier for Directed Single-Source Shortest Paths.*
> arXiv:2504.17033v2.

## What This Artifact Contains

- Rust implementations and benchmarks in `src/`.
- Shared JSON fixtures in `formal/fixtures/`.
- Lean 4 formalization in `formal/lean/`.
- Verification status and trusted assumptions in `formal/README.md`,
  `formal/VERIFICATION.md`, `formal/AXIOMS.md`, and `formal/FUTURE_WORK.md`.
- A vendored copy of the arXiv paper PDF and TeX source in `formal/paper/`.

## Current Claim Boundary

The strongest current theorem is the Dijkstra refinement API documented in
`formal/VERIFICATION.md`. It connects the operational CSR/Float/lazy-heap Lean
model to the verified Lean Dijkstra algorithm on every `ValidRustGraph`, while
still depending on the trusted numeric and heap bridge axioms listed in
`formal/AXIOMS.md`.

The BMSSP paper-level Lean modules are currently specifications/oracles, not
verified implementations of the full paper algorithm.

## Reproduction Checks

Recommended checks before publishing or archiving:

```bash
cd formal/lean
lake build Sssp.Refine.Verification

cd ../..
./formal/scripts/check-fixtures.sh
cargo test --release
```

Expected result: all commands complete successfully. Lean may emit existing
linter warnings about unused simp arguments; those warnings are not proof gaps.

## Suggested Archive Contents

Include:

- source files tracked by Git
- `Cargo.lock`
- `formal/lean/lake-manifest.json`
- `formal/paper/2504.17033v2.pdf`
- `formal/paper/2504.17033.tar.gz`
- `formal/paper/source/`

Exclude generated build outputs:

- `target/`
- `formal/lean/.lake/`
- `formal/paper/source/*.aux`, `*.bbl`, `*.blg`, `*.log`, `*.out`, `*.synctex.gz`

## Licensing Note

No project license has been selected in this repository yet. Do not infer a
reuse license from the presence of source code or vendored paper files. The
vendored paper files retain their original arXiv distribution terms and should
be cited to the original authors.
