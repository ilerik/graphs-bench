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

/-- CSR graph mirroring `src/graph.rs`. -/
structure RustGraph where
  n : Nat
  head : List Nat
  edgeTo : List Nat
  edgeW : List Float
  deriving Repr

namespace RustGraph

def outEdgeIndices (g : RustGraph) (u : Nat) : List Nat :=
  if _h : u + 1 < g.head.length then
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
  let sorted := edges.mergeSort (fun a b => a.1 ≤ b.1)
  { n := n
    head := head
    edgeTo := sorted.map Prod.snd |>.map Prod.fst
    edgeW := sorted.map Prod.snd |>.map Prod.snd }

end RustGraph

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

/-! ### NNReal ↔ Float bridge (integer weights)

Natural-number weights are accumulated by successor (`+ 1.0`) so Phase 3b can
relate `Float` relaxations to verified `WithTop NNReal` / `WithTop Nat` sums. -/

/-- Map a natural weight into `Float` (Peano-style; agrees with `Float.ofNat` on fixtures). -/
def floatWeight : Nat → Float
| 0 => 0.0
| w + 1 => floatWeight w + 1.0

/-- Map the same weight into `NNReal` (Algo side). -/
def nnrealWeight (w : Nat) : NNReal := w

theorem floatWeight_zero : floatWeight 0 = 0.0 := rfl
theorem floatWeight_succ (w : Nat) : floatWeight (w + 1) = floatWeight w + 1.0 := rfl

end Refine
end Sssp
