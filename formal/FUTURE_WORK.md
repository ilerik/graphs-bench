# Future work (post–Phase 3)

Phase **3 (Dijkstra)** is complete.  See `Sssp.Fixtures.Correctness` for the
joint statement tying together `Algo.dijkstra_correct`, Refine fixture guards,
`Sssp.Refine.Bridge`, and Rust JSON tests.

## Phase 3 summary (done)

| Layer | Module | Status |
|-------|--------|--------|
| Spec + relax lemmas | `Sssp.Dijkstra` | done |
| Verified algorithm | `Sssp.Algo.Dijkstra` (`dijkstra_correct`) | done |
| Operational model | `Sssp.Refine.Dijkstra` (heap + step lemmas) | done |
| CSR ↔ graph bridge | `Sssp.Refine.Bridge` | done (fixtures) |
| Regression | `Sssp.Fixtures.*`, CI, `check-fixtures.sh` | done |
| Rust cross-check | `cargo test shared_json_fixtures` | done |

**Deferred to Phase 9:** general Refine ≡ Algo refinement proof (all inputs,
not just fixtures); Lean JSON fixture parsing.

---

## Roadmap phases 4–11

See `formal/README.md` for the full table.  Next up:

| Phase | Deliverable | Estimate |
|------:|-------------|----------|
| 4 | `Sssp.Algo.DStruct` — block-list, amortised `Pull` | 3–4 weeks |
| 5 | `Sssp.Algo.FindPivots` — k-round Bellman-Ford, Lemma 3.2 | 3 weeks |
| 6 | `Sssp.Algo.BaseCase` — bounded mini-Dijkstra | 1–2 weeks |
| 7 | `Sssp.Algo.BMSSP` — well-founded recursion, Lemmas 3.1/3.10/3.12 | 4–6 weeks |
| 8 | `Sssp.Algo.Main` — top-level driver | 1 week |
| 9 | Rust↔Lean refinement (extraction or hand proof) | 4–8 weeks |
| 10 | Rust polish: LICENSE, CI, criterion benches | 1 week |
| 11 | Paper + submission | 4–8 weeks |

### Phase 2 reminder: `CostM`

The paper’s `O(m log^{2/3} n)` bound (Lemma 3.12) needs a cost-counting monad.
Can be deferred for functional correctness but not for the complexity theorem.

---

## Suggested order of attack

1. **Phase 4 DStruct** — unlocks pivot finding (Phase 5).
2. **Cost monad** — parallel track once DStruct API stabilises.
3. **BMSSP well-founded recursion** — highest proof risk.

---

## Regression commands

```bash
cd formal/lean && lake build
./formal/scripts/check-fixtures.sh
cargo test shared_json_fixtures
```
