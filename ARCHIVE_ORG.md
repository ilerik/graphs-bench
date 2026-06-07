# Archive.org Metadata Draft

This is a draft metadata sheet for publishing the repository artifact on
Archive.org.

## Suggested Identifier

`graphs-bench-sssp-lean-rust-2026`

## Suggested Title

`graphs-bench: Rust benchmarks and Lean artifacts for directed SSSP`

## Suggested Description

Research artifact for experimenting with the directed single-source shortest
path algorithm from Duan, Mao, Mao, Shu, and Yin, *Breaking the Sorting Barrier
for Directed Single-Source Shortest Paths* (arXiv:2504.17033v2).

The artifact contains Rust implementations and benchmarks, shared JSON fixtures,
a Lean 4 formalization, a Dijkstra refinement theorem for a CSR/Float/lazy-heap
model, explicit documentation of remaining trusted Lean assumptions, and a
vendored copy of the arXiv PDF and TeX source.

Important claim boundary: the BMSSP paper-level Lean modules are currently
specifications/oracles, not verified implementations of the full paper
algorithm. The Dijkstra refinement theorem is not zero-trust yet because it
depends on trusted numeric and heap bridge axioms documented in
`formal/AXIOMS.md`.

## Suggested Subjects

- graph algorithms
- single-source shortest paths
- formal verification
- Lean 4
- Rust
- benchmarking
- arXiv:2504.17033

## Suggested Files To Upload

- `dist/graphs-bench-<short-sha>.tar.gz`
- `dist/graphs-bench-<short-sha>.tar.gz.sha256`
- optionally, `formal/paper/2504.17033v2.pdf` as a separate convenience file

## Suggested Creator

`ilerik`; `sergantche`

## License Field

Leave unset until the repository owner chooses a project license. The vendored
paper files retain their original arXiv distribution terms.
