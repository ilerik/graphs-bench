/-
  Sssp.Refine.Dijkstra

  Operational model of the lazy min-heap Dijkstra in `src/dijkstra.rs`, using
  `Float` distances and a list-based CSR graph.
-/

import Sssp.Algo.Dijkstra

namespace Sssp
namespace Refine

/-- Sentinel for unreachable distances, matching `f64::INFINITY` in Rust. -/
def distInf : Float := 1.0 / 0.0

/-- Map a natural weight into `Float` (Peano-style; agrees with `Float.ofNat` on fixtures). -/
def floatWeight : Nat → Float
| 0 => 0.0
| w + 1 => floatWeight w + 1.0

theorem floatWeight_zero : floatWeight 0 = 0.0 := rfl
theorem floatWeight_succ (w : Nat) : floatWeight (w + 1) = floatWeight w + 1.0 := rfl

/-- CSR graph mirroring `src/graph.rs`. -/
structure RustGraph where
  n : Nat
  head : List Nat
  edgeTo : List Nat
  edgeW : List Float
  deriving Repr

namespace RustGraph

def outEdgeIndices (g : RustGraph) (u : Nat) : List Nat :=
  if h : u + 1 < g.head.length then
    let s := g.head[u]!
    let e := g.head[u + 1]!
    (List.range (e - s)).map (fun i => s + i)
  else []

def outEdges (g : RustGraph) (u : Nat) : List (Nat × Float) :=
  (outEdgeIndices g u).map fun i => (g.edgeTo[i]!, g.edgeW[i]!)

/-- Build a CSR graph from `(u, v, w)` triples (sorted by source). -/
def fromEdgeList (n : Nat) (edges : List (Nat × Nat × Float)) : RustGraph :=
  let counts := (List.range n).map fun u =>
    edges.filter (fun e => e.1 == u) |>.length
  let head := counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0]
  let sorted := edges.mergeSort (fun a b => decide (a.1 ≤ b.1))
  { n := n
    head := head
    edgeTo := sorted.map Prod.snd |>.map Prod.fst
    edgeW := sorted.map Prod.snd |>.map Prod.snd }

/-! ### CSR list lemmas (for `GraphBridge` nat-weight extraction) -/

@[simp] theorem fromEdgeList_edgeW (n : Nat) (edges : List (Nat × Nat × Float)) :
    (fromEdgeList n edges).edgeW =
      ((edges.mergeSort (fun a b => decide (a.1 ≤ b.1))).map Prod.snd).map Prod.snd := by
  simp [fromEdgeList]

-- TODO: finish CSR index bound lemmas and derive `outEdge_floatWeight_preimage`.

theorem outEdgeIndices_length (g : RustGraph) (u : Nat) :
    (g.outEdgeIndices u).length = (g.outEdges u).length := by
  dsimp [outEdges, outEdgeIndices]
  split_ifs with h
  · simp [List.length_map]
  · simp

theorem outEdges_nonempty_head {g : RustGraph} {u i : Nat}
    (hi : i < (g.outEdges u).length) : u + 1 < g.head.length := by
  by_contra h
  have hempty : g.outEdges u = [] := by
    dsimp [outEdges, outEdgeIndices]
    simp [h]
  rw [hempty] at hi
  exact Nat.not_lt_zero _ hi

theorem outEdgeIndices_range (g : RustGraph) (u : Nat) (hu : u + 1 < g.head.length) :
    g.outEdgeIndices u =
      (List.range (g.head[u + 1]! - g.head[u]!)).map fun i => g.head[u]! + i := by
  unfold outEdgeIndices
  simp only [hu, ↓reduceDIte]

theorem outEdgeIndices_getElem (g : RustGraph) (u i : Nat)
    (hu : u + 1 < g.head.length) (hi : i < (g.outEdgeIndices u).length) :
    (g.outEdgeIndices u)[i]'hi = g.head[u]! + i := by
  simp only [outEdgeIndices_range g u hu, List.getElem_map, List.getElem_range]

theorem outEdges_length_head (g : RustGraph) (u : Nat) (hu : u + 1 < g.head.length) :
    (g.outEdges u).length = g.head[u + 1]! - g.head[u]! := by
  have hlen := (outEdgeIndices_length g u).symm
  calc (g.outEdges u).length
      = (g.outEdgeIndices u).length := hlen
    _ = ((List.range (g.head[u + 1]! - g.head[u]!)).map fun i => g.head[u]! + i).length :=
        by rw [outEdgeIndices_range g u hu]
    _ = g.head[u + 1]! - g.head[u]! := by simp [List.length_map, List.length_range]

theorem csr_index_lt_head_end (g : RustGraph) (u i : Nat) (hu : u + 1 < g.head.length)
    (hi : i < (g.outEdges u).length) :
    g.head[u]! + i < g.head[u + 1]! := by
  have hlen := outEdges_length_head g u hu
  rw [hlen] at hi
  omega

end RustGraph

def natEdgeMap (es : List (Nat × Nat × Nat)) : List (Nat × Nat × Float) :=
  es.map fun e => (e.1, e.2.1, floatWeight e.2.2)

private lemma mem_natEdgeMap {es : List (Nat × Nat × Nat)} {p : Nat × Nat × Float}
    (hp : p ∈ natEdgeMap es) :
    ∃ e ∈ es, p = (e.1, e.2.1, floatWeight e.2.2) := by
  unfold natEdgeMap at hp
  rw [List.mem_map] at hp
  obtain ⟨e, he, hp⟩ := hp
  exact ⟨e, he, hp.symm⟩

private lemma mem_natEdgeMap_snd {es : List (Nat × Nat × Nat)} {p : Nat × Nat × Float}
    (hp : p ∈ natEdgeMap es) : ∃ w, floatWeight w = p.2.2 := by
  obtain ⟨e, _, hp⟩ := mem_natEdgeMap hp
  exact ⟨e.2.2, by rw [hp]⟩

private lemma mem_mergeSort_of_getElem {α} (le : α → α → Bool) (l : List α) (k : Nat)
    (hk : k < (l.mergeSort le).length) :
    (l.mergeSort le)[k]'hk ∈ l := by
  have hmem := List.getElem_mem hk
  exact (List.Perm.mem_iff (List.mergeSort_perm l le)).1 hmem

theorem fromEdgeList_edgeW_floatWeight (n : Nat) (es : List (Nat × Nat × Nat)) (k : Nat)
    (hk : k < (RustGraph.fromEdgeList n (natEdgeMap es)).edgeW.length) :
    ∃ w : Nat, floatWeight w = (RustGraph.fromEdgeList n (natEdgeMap es)).edgeW[k]'hk := by
  let mapped := natEdgeMap es
  let le := fun a b : Nat × Nat × Float => decide (a.1 ≤ b.1)
  have hk' : k < (mapped.mergeSort le).length := by
    rw [RustGraph.fromEdgeList_edgeW, List.length_map, List.length_map] at hk
    exact hk
  have hmem := mem_mergeSort_of_getElem le mapped k hk'
  have hw :
      (RustGraph.fromEdgeList n mapped).edgeW[k]'hk =
        ((mapped.mergeSort le)[k]'hk').2.2 := by
    dsimp [RustGraph.fromEdgeList, le]
    simp only [List.getElem_map, List.getElem_map]
  rw [hw]
  exact mem_natEdgeMap_snd hmem

structure HeapItem where
  d : Float
  v : Nat
  deriving Repr

def heapSame (a b : HeapItem) : Bool :=
  a.d == b.d && a.v == b.v

def heapPush (h : List HeapItem) (it : HeapItem) : List HeapItem :=
  it :: h

def heapPopMin : List HeapItem → Option (HeapItem × List HeapItem)
  | [] => none
  | x :: xs =>
    let best := (x :: xs).foldl (fun acc it =>
      if it.d < acc.d || (it.d == acc.d && it.v < acc.v) then it else acc) x
    some (best, (x :: xs).filter (fun it => !heapSame it best))

/-- Stale heap entry: distance already superseded in `dist`. -/
def distStale (dist : List Float) (item : HeapItem) : Bool :=
  item.d > dist[item.v]!

def dijkstraStep (g : RustGraph) (dist : List Float) (heap : List HeapItem) :
    List Float × List HeapItem :=
  match heapPopMin heap with
  | none => (dist, heap)
  | some (item, rest) =>
    match distStale dist item with
    | true => (dist, rest)
    | false =>
      (g.outEdges item.v).foldl (fun (d, h) (tgt, w) =>
        let nd := item.d + w
        if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h)) (dist, rest)

theorem dijkstraStep_stale (g : RustGraph) (dist : List Float) (heap : List HeapItem)
    (item : HeapItem) (rest : List HeapItem)
    (hpop : heapPopMin heap = some (item, rest))
    (hstale : distStale dist item = true) :
    dijkstraStep g dist heap = (dist, rest) := by
  unfold dijkstraStep
  simp only [hpop, hstale]

theorem dijkstraStep_fresh (g : RustGraph) (dist : List Float) (heap : List HeapItem)
    (item : HeapItem) (rest : List HeapItem)
    (hpop : heapPopMin heap = some (item, rest))
    (hfresh : distStale dist item = false) :
    dijkstraStep g dist heap =
      (g.outEdges item.v).foldl (fun (d, h) (tgt, w) =>
        let nd := item.d + w
        if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h)) (dist, rest) := by
  unfold dijkstraStep
  simp only [hpop, hfresh]

def dijkstraRun (fuel : Nat) (g : RustGraph) (dist : List Float) (heap : List HeapItem) :
    List Float × List HeapItem :=
  match fuel with
  | 0 => (dist, heap)
  | fuel + 1 =>
    let (d, h) := dijkstraStep g dist heap
    dijkstraRun fuel g d h

/-- Lazy min-heap Dijkstra (mirrors `src/dijkstra.rs`). -/
def dijkstraHeap (g : RustGraph) (source : Nat) : List Float :=
  let dist := (List.range g.n).map fun v => if v == source then 0.0 else distInf
  let fuel := g.n * g.edgeTo.length + g.n + 1
  (dijkstraRun fuel g dist [⟨0.0, source⟩]).1

def initDist (g : RustGraph) (source : Nat) : List Float :=
  (List.range g.n).map fun v => if v == source then 0.0 else distInf

def floatRelaxEdge (dist : List Float) (u tgt : Nat) (w : Float) : List Float :=
  let nd := dist[u]! + w
  if nd < dist[tgt]! then dist.set tgt nd else dist

def floatRelaxOut (g : RustGraph) (dist : List Float) (u : Nat) : List Float :=
  (g.outEdges u).foldl (fun d p => floatRelaxEdge d u p.1 p.2) dist

def floatRelaxAll (g : RustGraph) (dist : List Float) : List Float :=
  (List.range g.n).foldl (fun d u => floatRelaxOut g d u) dist

def floatRelaxRound : Nat → RustGraph → List Float → List Float
| 0, _, d => d
| fuel + 1, g, d => floatRelaxRound fuel g (floatRelaxAll g d)

/-- Proof-relevant `n`-round float relaxation (matches verified `Algo.dijkstra`). -/
def dijkstraRelax (g : RustGraph) (source : Nat) : List Float :=
  floatRelaxRound g.n g (initDist g source)

/-- Executable shortest-path distances (lazy heap; mirrors `src/dijkstra.rs`). -/
def dijkstra (g : RustGraph) (source : Nat) : List Float :=
  dijkstraHeap g source

/-- Map the same weight into `NNReal` (Algo side). -/
def nnrealWeight (w : Nat) : NNReal := w

end Refine
end Sssp
