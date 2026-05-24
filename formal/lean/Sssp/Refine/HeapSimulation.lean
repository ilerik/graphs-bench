/-
  Sssp.Refine.HeapSimulation

  Heap-step simulation for lazy Dijkstra: relate `dijkstraStep` / `dijkstraRun` to
  CSR float relaxation (`floatRelaxOut`) and the existing `SimInv` pipeline.
-/

import Sssp.Refine.Simulation

namespace Sssp
namespace Refine

open Sssp Algo FloatNat

variable {n : ℕ} {g : RustGraph}

/-! ### Initialization -/

theorem dijkstraHeap_initDist (source : Nat) :
    dijkstraHeap g source =
      let fuel := g.n * g.edgeTo.length + g.n + 1
      (dijkstraRun fuel g (initDist g source) [⟨0.0, source⟩]).1 := by
  unfold dijkstraHeap
  congr 1

theorem initDist_eq_dijkstraHeap_dist (source : Nat) :
    (List.range g.n).map (fun v => if v == source then 0.0 else distInf) = initDist g source := by
  simp [initDist]

/-! ### Step lemmas -/

theorem dijkstraStep_none (dist : List Float) (heap : List HeapItem)
    (h : heapPopMin heap = none) :
    dijkstraStep g dist heap = (dist, heap) := by
  unfold dijkstraStep
  simp [h]

theorem dijkstraStep_stale_dist (dist : List Float) (heap : List HeapItem)
    (item : HeapItem) (rest : List HeapItem)
    (hpop : heapPopMin heap = some (item, rest))
    (hstale : distStale dist item = true) :
    (dijkstraStep g dist heap).1 = dist :=
  (dijkstraStep_stale g dist heap item rest hpop hstale).symm ▸ rfl

theorem dijkstraRun_zero (dist : List Float) (heap : List HeapItem) :
    dijkstraRun 0 g dist heap = (dist, heap) := rfl

theorem dijkstraRun_succ (fuel : Nat) (dist : List Float) (heap : List HeapItem) :
    dijkstraRun (fuel + 1) g dist heap =
      let (d, h) := dijkstraStep g dist heap
      dijkstraRun fuel g d h := rfl

/-! ### Fresh pop aligns with `floatRelaxOut` on distances -/

private theorem heapRelaxFoldl_eq (item : HeapItem) :
    (fun (d, h) (tgt, w) =>
      let nd := item.d + w
      if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h)) =
    fun (x : List Float × List HeapItem) (p : Nat × Float) =>
      if item.d + p.2 < x.1[p.1]! then
        (x.1.set p.1 (item.d + p.2), heapPush x.2 ⟨item.d + p.2, p.1⟩)
      else x := by
  funext x p
  rcases x with ⟨d, h⟩
  rcases p with ⟨tgt, w⟩
  simp

private theorem foldl_fst_outEdges (dist : List Float) (item : HeapItem)
    (es : List (Nat × Float)) (rest : List HeapItem) (hitem : item.d = dist[item.v]!)
    (hns : ∀ p ∈ es, p.1 ≠ item.v) :
    (es.foldl
          (fun (d, h) (tgt, w) =>
            let nd := item.d + w
            if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h))
          (dist, rest)).1 =
      es.foldl (fun d p => floatRelaxEdge d item.v p.1 p.2) dist := by
  induction es generalizing dist rest with
  | nil => rfl
  | cons p ps ih =>
    have hp : p ∈ p :: ps := List.mem_cons_self
    have hns' : p.1 ≠ item.v := hns p hp
    simp only [List.foldl_cons]
    by_cases hlt : item.d + p.2 < dist[p.1]!
    · have hlt' : dist[item.v]! + p.2 < dist[p.1]! := by rwa [← hitem]
      simp only [floatRelaxEdge, hlt', hlt, ↓reduceIte]
      have hkeep : dist[item.v]! = (dist.set p.1 (item.d + p.2))[item.v]! := by
        rw [List.getElem!_eq_getElem?_getD (l := dist), List.getElem!_eq_getElem?_getD
          (l := dist.set p.1 (item.d + p.2)), List.getElem?_set]
        simp [if_neg hns']
      have hitem' : item.d = (dist.set p.1 (item.d + p.2))[item.v]! := hitem.trans hkeep
      have hRHS : List.foldl (fun d q => if d[item.v]! + q.2 < d[q.1]! then d.set q.1 (d[item.v]! + q.2) else d)
            (dist.set p.1 (dist[item.v]! + p.2)) ps =
          List.foldl (fun d q => floatRelaxEdge d item.v q.1 q.2) (dist.set p.1 (item.d + p.2)) ps := by
        rw [hitem]
        congr 1 <;> (intros; dsimp [floatRelaxEdge])
      rw [hRHS]
      congr 1
      rw [heapRelaxFoldl_eq]
      apply ih (dist := dist.set p.1 (item.d + p.2))
        (rest := heapPush rest ⟨item.d + p.2, p.1⟩)
      · exact hitem'
      · intro q hq
        exact hns q (List.mem_cons_of_mem p hq)
    · have hlt' : ¬ dist[item.v]! + p.2 < dist[p.1]! := by rwa [← hitem]
      simp only [floatRelaxEdge, hlt, hlt', ↓reduceIte]
      have hRHS : List.foldl (fun d q => if d[item.v]! + q.2 < d[q.1]! then d.set q.1 (d[item.v]! + q.2) else d) dist ps =
          List.foldl (fun d q => floatRelaxEdge d item.v q.1 q.2) dist ps := by
        congr 1 <;> (intros; dsimp [floatRelaxEdge])
      rw [hRHS]
      congr 1
      rw [heapRelaxFoldl_eq]
      apply ih
      · exact hitem
      · intro q hq
        exact hns q (List.mem_cons_of_mem p hq)

private theorem outEdges_foldl_fst_eq_floatRelaxOut {vg : ValidRustGraph n g} (dist : List Float)
    (item : HeapItem) (rest : List HeapItem) (u : Fin n) (hitemv : item.v = u.val)
    (hitem : item.d = dist[item.v]!) :
    ((g.outEdges item.v).foldl
          (fun (d, h) (tgt, w) =>
            let nd := item.d + w
            if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h))
          (dist, rest)).1 =
      floatRelaxOut g dist item.v := by
  have hout : g.outEdges u.val = g.outEdges item.v := by rw [hitemv]
  have hns : ∀ p ∈ g.outEdges item.v, p.1 ≠ item.v := by
    intro p hp
    have hmem : p ∈ g.outEdges u.val := by rw [hout]; exact hp
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    have hne := vg.hns u i hi
    apply Ne.symm
    intro hp'
    apply hne
    exact (congrArg Prod.fst heq).trans ((Eq.symm hp').trans hitemv)
  dsimp [floatRelaxOut]
  exact foldl_fst_outEdges dist item (g.outEdges item.v) rest hitem hns

theorem dijkstraStep_fresh_dist {vg : ValidRustGraph n g} (dist : List Float) (heap : List HeapItem)
    (item : HeapItem) (rest : List HeapItem) (u : Fin n) (hitemv : item.v = u.val)
    (hpop : heapPopMin heap = some (item, rest))
    (hfresh : distStale dist item = false)
    (hitem : item.d = dist[item.v]!) :
    (dijkstraStep g dist heap).1 = floatRelaxOut g dist item.v := by
  rw [dijkstraStep_fresh (g := g) dist heap item rest hpop hfresh]
  exact outEdges_foldl_fst_eq_floatRelaxOut (vg := vg) dist item rest u hitemv hitem

/-! ### `SimInv` through one fresh heap step -/

theorem floatRelaxOut_simInv {vg : ValidRustGraph n g} (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (u : Fin n) (h : SimInv vg s dist dHat) :
    SimInv vg s (floatRelaxOut g dist u.val) (relaxOutEdges vg.toGraph dHat u) where
  len := (floatRelaxOut_length dist u.val (h.len.trans vg.hn.symm)).trans vg.hn
  aligned := fun v => floatRelaxOut_aligned vg dHat dist u h.len h.aligned v
  sound := relaxOutEdges_sound (G := vg.toGraph) (s := s) dHat h.sound u

theorem dijkstraStep_simInv_fresh {vg : ValidRustGraph n g} (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (item : HeapItem) (rest : List HeapItem)
    (u : Fin n) (hpop : heapPopMin heap = some (item, rest))
    (hfresh : distStale dist item = false) (_hitemv : item.v = u.val)
    (hitemd : item.d = dist[u.val]!) (h : SimInv vg s dist dHat) :
    SimInv vg s (dijkstraStep g dist heap).1 (relaxOutEdges vg.toGraph dHat u) := by
  have hitem := show item.d = dist[item.v]! from by rw [_hitemv]; exact hitemd
  rw [dijkstraStep_fresh_dist (vg := vg) dist heap item rest u _hitemv hpop hfresh hitem]
  suffices hsim : SimInv vg s (floatRelaxOut g dist u.val) (relaxOutEdges vg.toGraph dHat u) from
    show SimInv vg s (floatRelaxOut g dist item.v) (relaxOutEdges vg.toGraph dHat u) from
      by rw [_hitemv]; exact hsim
  exact floatRelaxOut_simInv (vg := vg) s dist dHat u h

theorem dijkstraStep_simInv_stale {vg : ValidRustGraph n g} (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (item : HeapItem) (rest : List HeapItem)
    (hpop : heapPopMin heap = some (item, rest)) (hstale : distStale dist item = true)
    (h : SimInv vg s dist dHat) :
    SimInv vg s (dijkstraStep g dist heap).1 dHat := by
  rw [dijkstraStep_stale_dist dist heap item rest hpop hstale]
  exact h

end Refine
end Sssp
