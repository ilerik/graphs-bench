/-
  Sssp.lean — root module of the formal verification of the
  Duan–Mao–Mao–Shu–Yin SSSP algorithm (arXiv:2504.17033).

  This file simply re-exports the per-section modules so that consumers can
  `import Sssp` and have access to the entire verification.

  Layout (matches the paper's section numbering):

  * `Sssp.Graph`        — directed graphs, edges, weights (constant-degree
                          assumption is captured but not enforced).
  * `Sssp.Path`         — paths from `s`, length of a path, Assumption 2.1
                          (distinct path lengths) as a typeclass-like hypothesis.
  * `Sssp.Distance`     — true distance `d(v)`, the upper-bound estimate
                          `d̂[v]`, completeness, the `T(S)` and `T(S^*)`
                          notations from §3.5 of the paper.
  * `Sssp.Dijkstra`     — textbook Dijkstra (`src/dijkstra.rs`); used as a
                          reference implementation and for the equivalence
                          theorem `dijkstra_eq_bmssp`.
  * `Sssp.DStruct`      — partial-sorting block-list data structure `D`
                          (Lemma 3.3 / `src/dstruct.rs`).
  * `Sssp.FindPivots`   — Algorithm 1 + Lemma 3.2.
  * `Sssp.BaseCase`     — Algorithm 2 (level-0 of BMSSP).
  * `Sssp.BMSSP`        — Algorithm 3, Lemma 3.1 (correctness),
                          Lemma 3.10 (size bound), Lemma 3.12 (running time).
  * `Sssp.Main`         — top-level theorem `sssp_bmssp_correct` and the
                          time-complexity corollary.

  Every theorem statement is filled in; proofs are `sorry` placeholders so the
  module elaborates as a "blueprint" that the user can attack lemma-by-lemma.
-/

import Sssp.Graph
import Sssp.Path
import Sssp.Distance
import Sssp.Dijkstra
import Sssp.DStruct
import Sssp.FindPivots
import Sssp.BaseCase
import Sssp.BMSSP
import Sssp.Main
