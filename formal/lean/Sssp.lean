/-
  Sssp.lean — root module of the formal-verification project for the
  Duan–Mao–Mao–Shu–Yin SSSP algorithm (arXiv:2504.17033).

  ## Verification status

  This is a **specification + algorithm** layout.  The `Sssp.<X>` modules
  *specify* the input/output relation of the paper's primitives by
  oracle definitions whose correctness lemmas are vacuous (the function
  is *defined* to be its answer).  Real, computable, verified
  implementations are introduced as `Sssp.Algo.<X>` and proved to satisfy
  the corresponding spec.

  Honest summary as of Phase 0:

  ┌─────────────────┬──────────────────────────┬──────────────────────────┐
  │ Module          │ Status                   │ Real algorithm lives in  │
  ├─────────────────┼──────────────────────────┼──────────────────────────┤
  │ Sssp.Graph      │ Honest data definitions   │ —                        │
  │ Sssp.Path       │ Honest, finished proofs   │ —                        │
  │ Sssp.Distance   │ Honest, finished proofs   │ —                        │
  │ Sssp.Dijkstra   │ Spec + shared relax lemmas    │ Sssp.Algo.Dijkstra       │
  │ Sssp.Algo.Dijkstra │ Verified (`dijkstra_correct`) — Phase 3 complete │ —                     │
  │ Sssp.Refine.Dijkstra │ Float/CSR heap model + step lemmas      │ —                        │
  │ Sssp.Refine.Bridge │ CSR ↔ graph alignment (fixtures)        │ —                        │
  │ Sssp.Fixtures.*  │ Regression guards + completeness summary  │ —                        │
  │ Sssp.DStruct    │ Spec for Pull is oracle   │ Sssp.Algo.DStruct (TBD)  │
  │ Sssp.FindPivots │ Spec only (oracle)        │ Sssp.Algo.FindPivots (TBD)│
  │ Sssp.BaseCase   │ Spec only (oracle)        │ Sssp.Algo.BaseCase (TBD) │
  │ Sssp.BMSSP      │ Spec only (oracle)        │ Sssp.Algo.BMSSP (TBD)    │
  │ Sssp.Main       │ Spec only (oracle)        │ Sssp.Algo.Main (TBD)     │
  └─────────────────┴──────────────────────────┴──────────────────────────┘

  See `formal/README.md` for the full verification roadmap.

  ## Layout

  * `Sssp.Graph`        — directed graphs, edges, weights.
  * `Sssp.Path`         — paths, walks, lengths, Assumption 2.1.
  * `Sssp.Distance`     — `trueDist`, `Sound`, `IsComplete`,
                          `subtree`/`expectU`, the order-theoretic
                          truncation witness.
  * `Sssp.Dijkstra`     — *spec only.*
  * `Sssp.DStruct`      — partial-sorting data structure model;
                          `pullSpec` is an oracle.
  * `Sssp.FindPivots`   — *spec only.*
  * `Sssp.BaseCase`     — *spec only.*
  * `Sssp.BMSSP`        — *spec only.* No actual recursion.
  * `Sssp.Main`         — *spec only.*
  * `Sssp.Algo.Dijkstra` — real, computable, verified Dijkstra.

  Every theorem in `Sssp.Algo.<X>` is proven against `<X>Spec`.
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
import Sssp.Algo.Dijkstra
import Sssp.Refine.Dijkstra
