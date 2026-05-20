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

def dijkstraStep (g : RustGraph) (dist : List Float) (heap : List HeapItem) :
    List Float × List HeapItem :=
  match heapPopMin heap with
  | none => (dist, heap)
  | some (item, rest) =>
    if item.d > dist[item.v]! then
      (dist, rest)
    else
      (g.outEdges item.v).foldl (fun (d, h) (tgt, w) =>
        let nd := item.d + w
        if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h)) (dist, rest)

def dijkstraRun (fuel : Nat) (g : RustGraph) (dist : List Float) (heap : List HeapItem) :
    List Float × List HeapItem :=
  match fuel with
  | 0 => (dist, heap)
  | fuel + 1 =>
    let (d, h) := dijkstraStep g dist heap
    dijkstraRun fuel g d h

def dijkstra (g : RustGraph) (source : Nat) : List Float :=
  let dist := (List.range g.n).map fun v => if v == source then 0.0 else distInf
  let fuel := g.n * g.edgeTo.length + g.n + 1
  (dijkstraRun fuel g dist [⟨0.0, source⟩]).1

end Refine
end Sssp
