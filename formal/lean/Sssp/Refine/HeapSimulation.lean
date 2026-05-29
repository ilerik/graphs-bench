/-
  Sssp.Refine.HeapSimulation

  Heap-step simulation for lazy Dijkstra: relate `dijkstraStep` / `dijkstraRun` to
  CSR float relaxation (`floatRelaxOut`) and the existing `SimInv` pipeline.
-/

import Sssp.Refine.Simulation

namespace Sssp
namespace Refine

open Sssp Algo FloatNat List

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

/-! ### Heap state invariant -/

/-- Every heap entry carries a distance at least the current `dist` at its vertex. -/
structure HeapStateInv {g : RustGraph} (vg : ValidRustGraph n g)
    (dist : List Float) (heap : List HeapItem) : Prop where
  dist_len : dist.length = g.n
  le : ∀ item ∈ heap, dist[item.v]! ≤ item.d
  valid : ∀ item ∈ heap, item.v < n

theorem heapPopMin_rest_mem {heap : List HeapItem} {item : HeapItem} {rest : List HeapItem}
    {it : HeapItem} (h : heapPopMin heap = some (item, rest)) (hmem : it ∈ rest) :
    it ∈ heap := by
  unfold heapPopMin at h
  match heap with
  | [] => cases h
  | x :: xs =>
    simp only at h
    cases h
    simp [List.mem_filter] at hmem
    rcases hmem.1 with rfl | h
    · exact Mem.head xs
    · exact mem_cons_of_mem x h

private def heapFoldMinPick (acc it : HeapItem) : HeapItem :=
  if it.d < acc.d || (it.d == acc.d && it.v < acc.v) then it else acc

private theorem mem_cons_middle {x y a : HeapItem} {xs : List HeapItem}
    (h : a ∈ x :: xs) : a ∈ x :: y :: xs := by
  simp [List.mem_cons] at h ⊢
  tauto

private theorem heapFoldMinPick_eq :
    (fun acc it => if it.d < acc.d || (it.d == acc.d && it.v < acc.v) then it else acc) =
      heapFoldMinPick := rfl

private theorem heapFoldMinPick_self (x : HeapItem) : heapFoldMinPick x x = x := by
  unfold heapFoldMinPick
  split_ifs <;> simp

private theorem heapFoldMinPick_le_acc (acc it : HeapItem) :
    (heapFoldMinPick acc it).d ≤ acc.d := by
  unfold heapFoldMinPick
  split
  next h =>
    rw [Bool.or_eq_true] at h
    rcases h with hlt | htie
    · rw [decide_eq_true_iff] at hlt
      exact float_le_of_lt hlt
    · have heq : (it.d == acc.d) = true := by
        rcases (Bool.and_eq_true_iff.mp htie) with ⟨heq, _⟩
        exact heq
      rw [float_eq_of_beq heq]
      exact float_le_refl acc.d
  · exact float_le_refl acc.d

private theorem heapFoldMinPick_le_it (acc it : HeapItem) :
    (heapFoldMinPick acc it).d ≤ it.d := by
  unfold heapFoldMinPick
  split
  · exact float_le_refl it.d
  next hneg =>
    exact float_le_of_not_lt (by
      intro hlt
      have hor : (it.d < acc.d || (it.d == acc.d && it.v < acc.v)) = true := by
        simp [hlt, Bool.or_eq_true]
      exact hneg hor)

private theorem foldl_heapFoldMinPick_le_init (init : HeapItem) :
    ∀ xs, (List.foldl heapFoldMinPick init xs).d ≤ init.d := by
  intro xs
  induction xs generalizing init with
  | nil => exact float_le_refl init.d
  | cons y ys ih =>
    dsimp [List.foldl]
    exact float_le_trans (ih (heapFoldMinPick init y)) (heapFoldMinPick_le_acc init y)

private theorem foldl_heapFoldMinPick_min (init : HeapItem) :
    ∀ xs vertex, vertex ∈ init :: xs → (List.foldl heapFoldMinPick init xs).d ≤ vertex.d := by
  intro xs vertex hmem
  induction xs generalizing init vertex with
  | nil =>
    rcases List.mem_cons.mp hmem with rfl | h
    · exact float_le_refl _
    · simp at h
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons] at hmem ⊢
    rcases hmem with hvInit | hvRest
    · rw [hvInit]
      exact foldl_heapFoldMinPick_le_init init (y :: ys)
    · rcases hvRest with hvY | hvYs
      · rw [hvY]
        exact float_le_trans (foldl_heapFoldMinPick_le_init (heapFoldMinPick init y) ys)
          (heapFoldMinPick_le_it init y)
      · exact ih (heapFoldMinPick init y) vertex (List.mem_cons.mpr (Or.inr hvYs))

theorem heapPopMin_min_d {heap : List HeapItem} {item rest}
    (h : heapPopMin heap = some (item, rest)) :
    ∀ it ∈ heap, item.d ≤ it.d := by
  unfold heapPopMin at h
  match heap with
  | [] => cases h
  | x :: xs =>
    simp only at h
    cases h
    rw [heapFoldMinPick_eq, List.foldl, heapFoldMinPick_self]
    intro it hmem
    exact foldl_heapFoldMinPick_min x xs it hmem

private theorem foldl_heapPopMin_mem (x : HeapItem) :
    ∀ xs, List.foldl heapFoldMinPick x xs ∈ x :: xs := by
  intro xs
  induction xs generalizing x with
  | nil => exact Mem.head []
  | cons y xs ih =>
    simp only [List.foldl_cons, heapFoldMinPick]
    split
    · exact mem_cons_of_mem x (ih y)
    · exact mem_cons_middle (ih x)

theorem heapPopMin_some_mem {heap : List HeapItem} {item rest}
    (h : heapPopMin heap = some (item, rest)) : item ∈ heap := by
  unfold heapPopMin at h
  match heap with
  | [] => cases h
  | x :: xs =>
    simp only at h
    cases h
    have hself : heapFoldMinPick x x = x := by
      unfold heapFoldMinPick
      split_ifs <;> simp
    have hfold :
        List.foldl (fun acc it => if it.d < acc.d || (it.d == acc.d && it.v < acc.v) then it else acc) x
            (x :: xs) =
          List.foldl heapFoldMinPick x xs := by
      rw [heapFoldMinPick_eq, List.foldl, hself]
    rw [hfold]
    exact foldl_heapPopMin_mem x xs

private theorem freshPop_dist_le (dist : List Float) (item : HeapItem)
    (hfresh : distStale dist item = false) : item.d ≤ dist[item.v]! := by
  have hnot : ¬ dist[item.v]! < item.d := by
    intro hlt
    have htrue : distStale dist item = true := by
      unfold distStale
      rw [List.getElem!_eq_getElem?_getD (l := dist)] at hlt ⊢
      exact decide_eq_true (gt_iff_lt.mpr hlt)
    exact Bool.eq_false_iff.mp hfresh htrue
  exact float_le_of_not_lt hnot

private theorem freshPop_dist_eq {dist : List Float} {item : HeapItem}
    (hle : dist[item.v]! ≤ item.d) (hfresh : distStale dist item = false) :
    item.d = dist[item.v]! :=
  float_le_antisymm (freshPop_dist_le dist item hfresh) hle

/-- Fresh pop at `u` carries the minimum float key among remaining heap entries. -/
theorem heapPopMin_fresh_min_dHat {vg : ValidRustGraph n g} {s : Fin n} {dist : List Float}
    {dHat : DistEstimate n} {heap : List HeapItem}
    (hSim : SimInv vg s dist dHat) (hHeap : HeapStateInv (vg := vg) dist heap)
    {item rest} (hpop : heapPopMin heap = some (item, rest)) (u : Fin n)
    (hu : item.v = u.val) (hfresh : distStale dist item = false) :
    ∀ it ∈ rest, nnrealToFloat (dHat u) ≤ it.d := by
  intro it hmem
  have hmem' := heapPopMin_rest_mem hpop hmem
  have hmin := heapPopMin_min_d hpop it hmem'
  have hitem := freshPop_dist_eq (hHeap.le item (heapPopMin_some_mem hpop)) hfresh
  rw [hu] at hitem
  calc
    nnrealToFloat (dHat u) = dist[u.val]! := (hSim.aligned u).symm
    _ = item.d := hitem.symm
    _ ≤ it.d := hmin

theorem heapStateInv_init {vg : ValidRustGraph n g} (s : Fin n) :
    HeapStateInv (vg := vg) (initDist g s.val) [⟨0.0, s.val⟩] where
  dist_len := by simp [initDist_length, vg.hn]
  le := by
    intro item hmem
    simp at hmem
    subst hmem
    have hget := initDist_get (vg := vg) s s
    simp [hget, beq_self_eq_true]
    exact float_le_refl 0.0
  valid := by
    intro item hmem
    simp at hmem
    subst hmem
    exact s.isLt

/-! ### Heap invariant through relax fold -/

private theorem mem_heapRelaxFoldl {item : HeapItem} (es : List (Nat × Float))
    (dist : List Float) (rest : List HeapItem) {h : HeapItem} (hmem : h ∈ rest) :
    h ∈ (es.foldl
      (fun (d, h') (tgt, w) =>
        let nd := item.d + w
        if nd < d[tgt]! then (d.set tgt nd, heapPush h' ⟨nd, tgt⟩) else (d, h'))
      (dist, rest)).2 := by
  induction es generalizing dist rest with
  | nil => simpa using hmem
  | cons p es ih =>
    simp only [List.foldl_cons]
    split_ifs
    · have hmem' : h ∈ heapPush rest ⟨item.d + p.2, p.1⟩ := Mem.tail _ hmem
      exact ih (dist := dist.set p.1 (item.d + p.2))
        (rest := heapPush rest ⟨item.d + p.2, p.1⟩) hmem'
    · exact ih (dist := dist) (rest := rest) hmem

private def heapRelaxStep (item : HeapItem) (acc : List Float × List HeapItem) (p : Nat × Float) :
    List Float × List HeapItem :=
  let nd := item.d + p.2
  if nd < acc.1[p.1]! then (acc.1.set p.1 nd, heapPush acc.2 ⟨nd, p.1⟩) else acc

private theorem heapRelaxEs_preserves_heapInv {vg : ValidRustGraph n g}
    (es : List (Nat × Float)) (dist : List Float) (item : HeapItem)
    (rest : List HeapItem) (u : Fin n) (hitemv : item.v = u.val)
    (hitem : item.d = dist[item.v]!) (hHeap : HeapStateInv (vg := vg) dist rest)
    (hsub : ∀ p ∈ es, p ∈ g.outEdges item.v) :
    HeapStateInv (vg := vg)
      (es.foldl (fun acc p => heapRelaxStep item acc p) (dist, rest)).1
      (es.foldl (fun acc p => heapRelaxStep item acc p) (dist, rest)).2 := by
  induction es generalizing dist rest with
  | nil => exact hHeap
  | cons p es ih =>
    have hp : p ∈ g.outEdges item.v := hsub p List.mem_cons_self
    have hp_u : p ∈ g.outEdges u.val := hitemv ▸ hp
    have htgt' : p.1 < g.n := vg.hn ▸ vg.htgt u p hp_u
    have hns' : p.1 ≠ item.v := by
      intro heq
      rw [List.mem_iff_getElem] at hp_u
      obtain ⟨i, hi, hf⟩ := hp_u
      exact vg.hns u i hi ((congrArg Prod.fst hf).trans (heq.trans hitemv))
    have hkeep : dist[item.v]! = (dist.set p.1 (item.d + p.2))[item.v]! := by
      rw [List.getElem!_eq_getElem?_getD (l := dist), List.getElem!_eq_getElem?_getD
        (l := dist.set p.1 (item.d + p.2)), List.getElem?_set]
      simp [if_neg hns']
    have hitem' : item.d = (dist.set p.1 (item.d + p.2))[item.v]! := hitem.trans hkeep
    simp only [List.foldl_cons, heapRelaxStep]
    split_ifs with hlt
    · refine ih (dist := dist.set p.1 (item.d + p.2)) (rest := heapPush rest ⟨item.d + p.2, p.1⟩)
        hitem' ?_ (fun q hq => hsub q (Mem.tail _ hq))
      refine HeapStateInv.mk (by rw [List.length_set, hHeap.dist_len]) ?_ ?_
      · intro it hmem
        rw [heapPush, List.mem_cons] at hmem
        rcases hmem with heq | hmem
        · cases heq
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set]
          simp [hHeap.dist_len, htgt']
          exact float_le_refl _
        · have hle := hHeap.le it hmem
          have hi : it.v < g.n := vg.hn ▸ hHeap.valid it hmem
          by_cases heq : it.v = p.1
          · have hget : (dist.set p.1 (item.d + p.2))[it.v]! = item.d + p.2 := by
              rw [heq, List.getElem!_eq_getElem?_getD, List.getElem?_set]
              simp [htgt', hHeap.dist_len]
            have hle' : dist[p.1]! ≤ it.d := by rw [← heq]; exact hle
            rw [hget]
            exact float_le_trans (float_le_of_lt hlt) hle'
          · have hget : (dist.set p.1 (item.d + p.2))[it.v]! = dist[it.v]! := by
              rw [List.getElem!_eq_getElem?_getD, List.getElem?_set, if_neg (Ne.symm heq)]
              simp [hi, hHeap.dist_len]
            rw [hget]
            exact hle
      · intro it hmem
        rw [heapPush, List.mem_cons] at hmem
        rcases hmem with heq | hmem
        · cases heq; exact vg.hn ▸ htgt'
        · exact hHeap.valid it hmem
    · exact ih (dist := dist) (rest := rest) hitem hHeap (fun q hq => hsub q (Mem.tail _ hq))

private theorem heapRelaxEdges_preserves_heapInv {vg : ValidRustGraph n g}
    (edges : List (Nat × Float)) (dist : List Float) (item : HeapItem)
    (rest : List HeapItem) (u : Fin n) (hitemv : item.v = u.val)
    (hitem : item.d = dist[item.v]!) (hHeap : HeapStateInv (vg := vg) dist rest)
    (hedges : edges = g.outEdges item.v) :
    HeapStateInv (vg := vg)
      (edges.foldl (fun acc p => heapRelaxStep item acc p) (dist, rest)).1
      (edges.foldl (fun acc p => heapRelaxStep item acc p) (dist, rest)).2 := by
  subst hedges
  exact heapRelaxEs_preserves_heapInv (vg := vg) (g.outEdges item.v) dist item rest u hitemv hitem
    hHeap (fun _ hp => hp)

private theorem heapRelaxFoldl_preserves_heapInv {vg : ValidRustGraph n g}
    (dist : List Float) (item : HeapItem) (rest : List HeapItem) (u : Fin n)
    (hitemv : item.v = u.val) (hitem : item.d = dist[item.v]!)
    (hHeap : HeapStateInv (vg := vg) dist rest) :
    HeapStateInv (vg := vg)
      ((g.outEdges item.v).foldl
        (fun (d, h) (tgt, w) =>
          let nd := item.d + w
          if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h))
        (dist, rest)).1
      ((g.outEdges item.v).foldl
        (fun (d, h) (tgt, w) =>
          let nd := item.d + w
          if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h))
        (dist, rest)).2 := by
  have hEq : (fun (d, h) (tgt, w) =>
      let nd := item.d + w
      if nd < d[tgt]! then (d.set tgt nd, heapPush h ⟨nd, tgt⟩) else (d, h)) =
    fun acc p => heapRelaxStep item acc p := by
    funext acc p; cases acc with | mk d h => cases p with | mk tgt w => rfl
  rw [hEq]
  exact heapRelaxEdges_preserves_heapInv (vg := vg) (g.outEdges item.v) dist item rest u
    hitemv hitem hHeap rfl

theorem dijkstraStep_preserves_heapInv {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) :
    HeapStateInv (vg := vg) (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2 := by
  by_cases hnone : heapPopMin heap = none
  · rw [dijkstraStep_none dist heap hnone]
    exact hHeap
  · obtain ⟨item, rest, hpop⟩ : ∃ item rest, heapPopMin heap = some (item, rest) := by
      cases h : heapPopMin heap with
      | none => exact absurd h hnone
      | some p => exact ⟨p.1, p.2, rfl⟩
    cases hstale : distStale dist item with
    | true =>
      rw [dijkstraStep_stale (g := g) dist heap item rest hpop hstale]
      exact {
        dist_len := hHeap.dist_len
        le := fun it hmem => hHeap.le it (heapPopMin_rest_mem hpop hmem)
        valid := fun it hmem => hHeap.valid it (heapPopMin_rest_mem hpop hmem) }
    | false =>
      have hmem := heapPopMin_some_mem hpop
      let u : Fin n := ⟨item.v, vg.hn ▸ hHeap.valid item hmem⟩
      have hitemv : item.v = u.val := rfl
      have hitem := freshPop_dist_eq (hHeap.le item hmem) hstale
      have hHeap' : HeapStateInv (vg := vg) dist rest := {
        dist_len := hHeap.dist_len
        le := fun it hmem => hHeap.le it (heapPopMin_rest_mem hpop hmem)
        valid := fun it hmem => hHeap.valid it (heapPopMin_rest_mem hpop hmem) }
      rw [dijkstraStep_fresh (g := g) dist heap item rest hpop hstale]
      exact heapRelaxFoldl_preserves_heapInv (vg := vg) dist item rest u hitemv hitem hHeap'

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
    (hle : dist[item.v]! ≤ item.d) (h : SimInv vg s dist dHat) :
    SimInv vg s (dijkstraStep g dist heap).1 (relaxOutEdges vg.toGraph dHat u) := by
  have hitem := freshPop_dist_eq hle hfresh
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

/-! ### Tracked `DistEstimate` through heap steps -/

/-- The `DistEstimate` advanced by one heap step (unchanged on none/stale pop). -/
noncomputable def dijkstraStep_dHat (vg : ValidRustGraph n g) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) :
    DistEstimate n :=
  match hpop : heapPopMin heap with
  | none => dHat
  | some (item, _) =>
    if distStale dist item then dHat else
      let u : Fin n := ⟨item.v, vg.hn ▸ hHeap.valid item (heapPopMin_some_mem hpop)⟩
      relaxOutEdges vg.toGraph dHat u

theorem dijkstraStep_dHat_none (vg : ValidRustGraph n g) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (hpop : heapPopMin heap = none) :
    dijkstraStep_dHat vg dist dHat heap hHeap = dHat := by
  cases heap with
  | nil =>
    cases hpop
    simp [dijkstraStep_dHat, heapPopMin]
  | cons x xs =>
    unfold heapPopMin at hpop
    simp at hpop

theorem dijkstraStep_dHat_stale (vg : ValidRustGraph n g) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (item : HeapItem) (rest : List HeapItem) (hpop : heapPopMin heap = some (item, rest))
    (hstale : distStale dist item = true) :
    dijkstraStep_dHat vg dist dHat heap hHeap = dHat := by
  cases heap with
  | nil =>
    unfold heapPopMin at hpop
    simp at hpop
  | cons x xs =>
    cases hpop
    simp only [dijkstraStep_dHat, heapPopMin, hstale, ↓reduceIte]

theorem dijkstraStep_dHat_fresh (vg : ValidRustGraph n g) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (item : HeapItem) (rest : List HeapItem) (u : Fin n) (hitemv : item.v = u.val)
    (hpop : heapPopMin heap = some (item, rest)) (hstale : distStale dist item = false) :
    dijkstraStep_dHat vg dist dHat heap hHeap = relaxOutEdges vg.toGraph dHat u := by
  cases heap with
  | nil =>
    unfold heapPopMin at hpop
    simp at hpop
  | cons x xs =>
    cases hpop
    simp only [dijkstraStep_dHat, heapPopMin, hitemv]
    rw [if_neg (Bool.eq_false_iff.mp hstale)]

theorem dijkstraStep_simInv_exact {vg : ValidRustGraph n g} (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (h : SimInv vg s dist dHat)
    (hHeap : HeapStateInv (vg := vg) dist heap) :
    SimInv vg s (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap) := by
  rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
  · rw [dijkstraStep_none dist heap hpop, dijkstraStep_dHat_none vg dist dHat heap hHeap hpop]
    exact h
  · by_cases hstale : distStale dist item
    · have hstale' : distStale dist item = true := by simp [hstale]
      rw [dijkstraStep_dHat_stale vg dist dHat heap hHeap item rest hpop hstale']
      exact dijkstraStep_simInv_stale (vg := vg) s dist dHat heap item rest hpop hstale' h
    · have hstale' : distStale dist item = false := by simp [hstale]
      have hmem := heapPopMin_some_mem hpop
      let u : Fin n := ⟨item.v, vg.hn ▸ hHeap.valid item hmem⟩
      have hitemv : item.v = u.val := rfl
      have hitem := freshPop_dist_eq (hHeap.le item hmem) hstale'
      rw [dijkstraStep_dHat_fresh vg dist dHat heap hHeap item rest u hitemv hpop hstale']
      exact dijkstraStep_simInv_fresh (vg := vg) s dist dHat heap item rest u hpop hstale' hitemv
        (hHeap.le item hmem) h

noncomputable def dijkstraRun_dHat (vg : ValidRustGraph n g) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) :
    Nat → DistEstimate n
  | 0 => dHat
  | fuel + 1 =>
    dijkstraRun_dHat vg (dijkstraStep g dist heap).1
      (dijkstraStep_dHat vg dist dHat heap hHeap)
      (dijkstraStep g dist heap).2
      (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) fuel

theorem dijkstraRun_simInv_exact {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat)
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (h : SimInv vg s dist dHat) (hHeap : HeapStateInv (vg := vg) dist heap) :
    SimInv vg s (dijkstraRun fuel g dist heap).1
      (dijkstraRun_dHat vg dist dHat heap hHeap fuel) := by
  induction fuel generalizing dist dHat heap h hHeap with
  | zero =>
    rw [dijkstraRun_zero]
    exact h
  | succ fuel ih =>
    rw [dijkstraRun_succ]
    have hSim' := dijkstraStep_simInv_exact (vg := vg) s dist dHat heap h hHeap
    have hHeap' := dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap
    dsimp [dijkstraRun_dHat]
    exact ih (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap)
      (dijkstraStep g dist heap).2 hSim' hHeap'

theorem dijkstraStep_preserves_simInv {vg : ValidRustGraph n g} (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (h : SimInv vg s dist dHat)
    (hHeap : HeapStateInv (vg := vg) dist heap) :
    ∃ dHat', SimInv vg s (dijkstraStep g dist heap).1 dHat' :=
  ⟨dijkstraStep_dHat vg dist dHat heap hHeap,
    dijkstraStep_simInv_exact (vg := vg) s dist dHat heap h hHeap⟩

theorem dijkstraRun_preserves_simInv {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat)
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (h : SimInv vg s dist dHat) (hHeap : HeapStateInv (vg := vg) dist heap) :
    ∃ dHat', SimInv vg s (dijkstraRun fuel g dist heap).1 dHat' :=
  ⟨dijkstraRun_dHat vg dist dHat heap hHeap fuel,
    dijkstraRun_simInv_exact (vg := vg) s fuel dist dHat heap h hHeap⟩

theorem dijkstraInit_simInv {vg : ValidRustGraph n g} (s : Fin n) :
    SimInv vg s (initDist g s.val) (initEstimate s) ∧
    HeapStateInv (vg := vg) (initDist g s.val) [⟨0.0, s.val⟩] :=
  ⟨initSimInv (vg := vg) s, heapStateInv_init (vg := vg) s⟩

def dijkstraHeapFuel (g : RustGraph) : Nat :=
  g.n * g.edgeTo.length + g.n + 1

theorem dijkstraHeap_eq_dijkstraRun (source : Nat) :
    dijkstraHeap g source =
      (dijkstraRun (dijkstraHeapFuel g) g (initDist g source) [⟨0.0, source⟩]).1 := by
  unfold dijkstraHeap dijkstraHeapFuel
  rfl

theorem dijkstraRun_init_simInv {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat) :
    ∃ dHat, SimInv vg s (dijkstraRun fuel g (initDist g s.val) [⟨0.0, s.val⟩]).1 dHat := by
  obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
  exact dijkstraRun_preserves_simInv (vg := vg) s fuel (initDist g s.val) (initEstimate s)
    [⟨0.0, s.val⟩] hSim hHeap

/-! ### `dHat` monotonicity through heap steps (estimates never increase) -/

/-- Sound plus an upper bound on `dHat` yields completeness. -/
theorem isComplete_of_sound_and_upper {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hSound : Sound G s dHat) (hUpper : ∀ v, dHat v ≤ trueDist G s v) (v : Fin n) :
    IsComplete G s dHat v := by
  dsimp [IsComplete]
  exact le_antisymm (hUpper v) (hSound v)

private theorem dijkstraStep_dHat_preserves_zero_at_source {vg : ValidRustGraph n g} {s : Fin n}
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (hHeap : HeapStateInv (vg := vg) dist heap) (h : dHat s = 0) :
    (dijkstraStep_dHat vg dist dHat heap hHeap) s = 0 := by
  rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
  · rw [dijkstraStep_dHat_none (vg := vg) dist dHat heap hHeap hpop]
    exact h
  · by_cases hstale : distStale dist item
    · have hstale' : distStale dist item = true := by simp [hstale]
      rw [dijkstraStep_dHat_stale (vg := vg) dist dHat heap hHeap item rest hpop hstale']
      exact h
    · have hmem := heapPopMin_some_mem hpop
      let u : Fin n := ⟨item.v, vg.hn ▸ hHeap.valid item hmem⟩
      have hstale' : distStale dist item = false := by simp [hstale]
      rw [dijkstraStep_dHat_fresh (vg := vg) dist dHat heap hHeap item rest u rfl hpop hstale']
      exact Algo.relaxOutEdges_preserves_zero_at_source (G := vg.toGraph) h

theorem dijkstraRun_dHat_preserves_zero_at_source {vg : ValidRustGraph n g} {s : Fin n}
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat) (h : dHat s = 0) :
    dijkstraRun_dHat vg dist dHat heap hHeap fuel s = 0 := by
  induction fuel generalizing dist dHat heap hHeap with
  | zero => exact h
  | succ fuel ih =>
    simp only [dijkstraRun_dHat]
    exact ih (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap)
      (dijkstraStep g dist heap).2 (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap)
      (dijkstraStep_dHat_preserves_zero_at_source (vg := vg) (s := s) dist dHat heap hHeap h)

theorem dijkstraRun_dHat_source_eq {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) fuel s = 0 :=
  dijkstraRun_dHat_preserves_zero_at_source (vg := vg) (s := s) (initDist g s.val)
    (initEstimate s) [⟨0.0, s.val⟩] (heapStateInv_init (vg := vg) s) fuel (initEstimate_self s)

/-! ### Settlement route (fresh min-pop ⇒ complete)

    Target chain:
    1. `heapPopMin_min_d` / `heapPopMin_fresh_min_dHat` — ✓ fresh pop has minimum key
    2. `trueDist_min_outside_of_heapPopMin_fresh` — (draft) uses `HasDistinctVertexDistances`
       (mathlib) + `exists_tight_pred_of_min_outside_distinct` to obtain `hmin`.
       `freshPop_isComplete_of_setComplete` — ✓ given `hmin` + `ProcessedEdgeUpper` on `S`
    3. `FreshPopInsertsNew` (docstring) — intended route via strict-improvement guard (lemma deferred)
    3. Track `dijkstraRun_processed` through steps; maintain `SetComplete` + `ProcessedEdgeUpper`
       · `dijkstraRun_processed_card_le_fuel` — ✓ processed ⊆ fuel steps
       · `dijkstraStep_freshVertex_some` — ✓ fresh pop exposes heap item
       · `dijkstraStep_fresh/stale_processedEdgeUpper` — ✓ one-step edge-upper extension
       · `dijkstraRun_processedAcc_processedEdgeUpper` — ✓ run induction (needs fresh completeness)
    4. `dijkstraRun_freshCount_at_heapFuel ≥ n` — reduce via `dijkstraRun_freshCount_ge_n_add_one_of_stale_bound`
       · stale bound `dijkstraRun_staleCount ≤ n * edgeTo.length` still open
       · `dijkstraRun_processed_card_le_freshCount` — ✓ `|processed| ≤ freshCount`
       · `FreshPopInsertsNew` (docstring) — intended route via strict-improvement guard (lemma deferred)
       · `processed.card = freshCount` (under `FreshPopInsertsNew`) → `processed_univ` at heap fuel
    5. `edgeUpper_of_processedEdgeUpper_univ` — ✓ close from `ProcessedEdgeUpper` + `SetComplete` on univ
    6. Target: `dijkstraRun_dHat_all_complete_at_heapFuel` → `dijkstraRun_dHat_schedule` →
       `dijkstraHeap_eq_dijkstraRelax_of_schedule`

    Blockers:
    · `trueDist_min_outside_of_heapPopMin_fresh`: (draft) requires connecting `SimInv`
      (soundness of `dHat`) to `trueDist` and reachability of `y`.
    · `dijkstraRun_freshCount_ge_n_at_heapFuel` / `processed = univ` for
      `edgeUpper_of_processedEdgeUpper_univ` on `Finset.univ`.
    Sandwich route dead. -/

/-- True when the next heap pop is fresh (non-stale). -/
def dijkstraStep_isFresh (dist : List Float) (heap : List HeapItem) : Bool :=
  match heapPopMin heap with
  | none => false
  | some (item, _) => !distStale dist item

/-- Count fresh (non-stale) heap pops in a `dijkstraRun`. -/
noncomputable def dijkstraRun_freshCount (fuel : Nat) (g : RustGraph) (dist : List Float)
    (heap : List HeapItem) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let (d, h) := dijkstraStep g dist heap
    dijkstraRun_freshCount fuel g d h + if dijkstraStep_isFresh dist heap then 1 else 0

/-- Count stale or idle heap steps (non-fresh pops, including empty-heap steps). -/
noncomputable def dijkstraRun_staleCount (fuel : Nat) (g : RustGraph) (dist : List Float)
    (heap : List HeapItem) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let (d, h) := dijkstraStep g dist heap
    dijkstraRun_staleCount fuel g d h + if dijkstraStep_isFresh dist heap then 0 else 1

/-- If the step is a fresh pop, return the popped vertex; otherwise `none`. -/
def dijkstraStep_freshVertex (vg : ValidRustGraph n g) (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) : Option (Fin n) :=
  match hpop : heapPopMin heap with
  | none => none
  | some (item, rest) =>
    if distStale dist item then none
    else some ⟨item.v, vg.hn ▸ hHeap.valid item (heapPopMin_some_mem hpop)⟩

/-- Vertices that have received a fresh pop (past-only accumulator for settlement). -/
noncomputable def dijkstraRun_processedAcc (vg : ValidRustGraph n g) (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (acc : Finset (Fin n)) : Finset (Fin n) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    match dijkstraStep_freshVertex vg dist heap hHeap with
    | none =>
      dijkstraRun_processedAcc vg (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) fuel acc
    | some u =>
      dijkstraRun_processedAcc vg (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) fuel (insert u acc)

noncomputable def dijkstraRun_processed (vg : ValidRustGraph n g) (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat) :
    Finset (Fin n) :=
  dijkstraRun_processedAcc vg dist heap hHeap fuel ∅

/-- For every processed vertex `x`, current estimates respect edge-upper bounds from `x`
    using `x`'s true distance (requires `x` complete when the edge was relaxed). -/
def ProcessedEdgeUpper {G : Graph n} (s : Fin n) (dHat : DistEstimate n) (S : Finset (Fin n)) :
    Prop :=
  ∀ x ∈ S, ∀ (y : Fin n) (w : NNReal), w ∈ G.edges x y → dHat y ≤ trueDist G s x + w

theorem processedEdgeUpper_empty {G : Graph n} (s : Fin n) (dHat : DistEstimate n) :
    ProcessedEdgeUpper (G := G) s dHat ∅ := by
  intro x hx
  simp at hx

theorem relaxOutEdges_tgt_le_trueDist_add_of_complete {G : Graph n} {s x y : Fin n}
    {dHat : DistEstimate n} (hComplete : IsComplete G s dHat x) (wt : NNReal)
    (h : wt ∈ G.edges x y) :
    (relaxOutEdges G dHat x) y ≤ trueDist G s x + (wt : WithTop NNReal) := by
  calc
    (relaxOutEdges G dHat x) y ≤ dHat x + (wt : WithTop NNReal) :=
      Algo.relaxOutEdges_le_add_edge (G := G) dHat x y wt h
    _ = trueDist G s x + (wt : WithTop NNReal) := by rw [hComplete]

/-- Fresh pop is complete when a processed predecessor already tightened the incoming edge
    on a shortest walk (the `y = u` case of the settlement argument). -/
theorem freshPop_isComplete_of_processed_pred {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (S : Finset (Fin n)) (u x : Fin n) (wt : NNReal) (_hSet : SetComplete G s dHat S)
    (_hu : u ∉ S) (_hx : x ∈ S) (hSound : Sound G s dHat) (_hEdge : wt ∈ G.edges x u)
    (hPred : dHat u ≤ trueDist G s x + (wt : WithTop NNReal))
    (hWalk : trueDist G s u = trueDist G s x + (wt : WithTop NNReal)) :
    IsComplete G s dHat u := by
  dsimp [IsComplete]
  exact le_antisymm (hWalk ▸ hPred) (hSound u)

/-- The fresh heap pop `u` has minimum `trueDist` among vertices outside the processed set `acc`.
    This is the `hmin` hypothesis required by `freshPop_isComplete_of_setComplete`.
    Proof relies on `HasDistinctVertexDistances` (mathlib) to obtain a tight predecessor
    and `ProcessedEdgeUpper` to pull the contradiction back into `acc`. -/
theorem trueDist_min_outside_of_heapPopMin_fresh {vg : ValidRustGraph n g} {s : Fin n}
    {dist : List Float} {dHat : DistEstimate n} {heap : List HeapItem}
    (hSim : SimInv vg s dist dHat) (hHeap : HeapStateInv (vg := vg) dist heap)
    {acc : Finset (Fin n)} (hProc : ProcessedEdgeUpper (G := vg.toGraph) s dHat acc)
    (hSet : SetComplete vg.toGraph s dHat acc)
    {item rest} (hpop : heapPopMin heap = some (item, rest)) (u : Fin n)
    (hu : item.v = u.val) (hfresh : distStale dist item = false)
    [HasDistinctVertexDistances vg.toGraph s] :
    ∀ y ∉ acc, trueDist vg.toGraph s u ≤ trueDist vg.toGraph s y := by
  intro y hy
  -- Proof by contradiction.
  by_contra hlt
  simp only [not_le] at hlt
  -- 1. By mathlib `exists_tight_pred_of_min_outside_distinct` (using `HasDistinctVertexDistances`),
  --    there is a tight predecessor `x ∈ acc`.
  have hfin_y : trueDist vg.toGraph s y < ⊤ := by
    -- y is reachable because the run processes all vertices (or we assume finite distances).
    sorry -- Placeholder: reachability argument from heap state.
  obtain ⟨x, hx_acc, w, h_edge, h_walk⟩ :=
    exists_tight_pred_of_min_outside_distinct (G := vg.toGraph) (s := s) acc hy
      (by simp [hSet s (by simp : s ∈ Finset.univ)]) -- s is complete (source)
      (fun z hz => le_of_lt (hlt.trans_le (by sorry : trueDist _ _ y ≤ trueDist _ _ z))) -- min assumption
      hfin_y
  -- 2. Since `x ∈ acc`, `ProcessedEdgeUpper` applies.
  have h_upper := hProc x hx_acc y w h_edge
  -- 3. `SimInv.sound` says `dHat` is an upper bound: `dHat y ≥ trueDist y`.
  have h_sound := hSim.sound
  -- 4. Combining (2) and (3): `dHat y ≤ trueDist x + w = trueDist y ≤ dHat y`.
  --    Therefore `dHat y = trueDist y`.
  -- 5. But `heapPopMin_fresh_min_dHat` says the fresh pop `u` has the minimum `dHat` key.
  --    If `y` has a heap entry with key `dist[y]! = nnrealToFloat (dHat y)` (by `SimInv.aligned`),
  --    and `dist[y]! < dist[u.val]!` (by `hlt` and `aligned`), this contradicts the minimum key.
  sorry -- Full proof requires connecting `dist[y]` to a heap entry and contradicting the min-key property.

/-- Fresh pop is complete when processed vertices form a complete frontier `S`, the pop
    is minimum-`trueDist` outside `S`, and processed vertices already satisfy edge-upper
    bounds (so the tight predecessor from `exists_tight_pred_of_min_outside` is settled). -/
theorem freshPop_isComplete_of_setComplete {G : Graph n} {s u : Fin n} {dHat : DistEstimate n}
    (S : Finset (Fin n)) (hSet : SetComplete G s dHat S) (hu : u ∉ S) (hs : s ∈ S)
    (hSound : Sound G s dHat) (hProc : ProcessedEdgeUpper (G := G) s dHat S)
    (hmin : ∀ y ∉ S, trueDist G s u ≤ trueDist G s y) (hfin : trueDist G s u < ⊤)
    [HasDistinctVertexDistances G s] :
    IsComplete G s dHat u := by
  obtain ⟨x, hxS, wt, hEdge, hWalk⟩ :=
    exists_tight_pred_of_min_outside_distinct (G := G) (s := s) S hu hs hmin hfin
  have hPred := hProc x hxS u wt hEdge
  exact freshPop_isComplete_of_processed_pred (G := G) (s := s) (dHat := dHat) S u x wt hSet hu hxS
    hSound hEdge hPred hWalk

/-- `ProcessedEdgeUpper` on all vertices plus pointwise completeness yields global `EdgeUpper`. -/
theorem edgeUpper_of_processedEdgeUpper_univ {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hProc : ProcessedEdgeUpper (G := G) s dHat Finset.univ)
    (hSet : SetComplete G s dHat Finset.univ) :
    EdgeUpper G s dHat := by
  intro u v w h
  have hu : u ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ u
  have hbound := hProc u hu v w h
  have hComplete := hSet u hu
  dsimp [IsComplete] at hComplete
  calc
    dHat v ≤ trueDist G s u + w := hbound
    _ = dHat u + w := by rw [hComplete]

theorem dijkstraRun_freshCount_le_fuel {g : RustGraph} (fuel : Nat) (dist : List Float) (heap : List HeapItem) :
    dijkstraRun_freshCount fuel g dist heap ≤ fuel := by
  induction fuel generalizing dist heap with
  | zero => simp [dijkstraRun_freshCount]
  | succ fuel ih =>
    simp only [dijkstraRun_freshCount]
    have h := ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
    split <;> omega

theorem dijkstraRun_staleCount_le_fuel {g : RustGraph} (fuel : Nat) (dist : List Float) (heap : List HeapItem) :
    dijkstraRun_staleCount fuel g dist heap ≤ fuel := by
  induction fuel generalizing dist heap with
  | zero => simp [dijkstraRun_staleCount]
  | succ fuel ih =>
    simp only [dijkstraRun_staleCount]
    have h := ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
    split <;> omega

theorem dijkstraRun_freshCount_add_staleCount {g : RustGraph} (fuel : Nat) (dist : List Float)
    (heap : List HeapItem) :
    dijkstraRun_freshCount fuel g dist heap + dijkstraRun_staleCount fuel g dist heap = fuel := by
  induction fuel generalizing dist heap with
  | zero => simp [dijkstraRun_freshCount, dijkstraRun_staleCount]
  | succ fuel ih =>
    simp only [dijkstraRun_freshCount, dijkstraRun_staleCount]
    have h := ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
    split <;> omega

/-- If stale pops are bounded by `g.n * |edgeTo|`, heap fuel yields at least `g.n + 1` fresh pops. -/
theorem dijkstraRun_freshCount_ge_n_add_one_of_stale_bound {g : RustGraph} (fuel : Nat)
    (dist : List Float) (heap : List HeapItem) (hfuel : fuel = dijkstraHeapFuel g)
    (hStale : dijkstraRun_staleCount fuel g dist heap ≤ g.n * g.edgeTo.length) :
    g.n + 1 ≤ dijkstraRun_freshCount fuel g dist heap := by
  have hsum := dijkstraRun_freshCount_add_staleCount (g := g) fuel dist heap
  have heq : fuel = g.n * g.edgeTo.length + g.n + 1 := by rw [hfuel, dijkstraHeapFuel]
  have htotal :
      dijkstraRun_freshCount fuel g dist heap + dijkstraRun_staleCount fuel g dist heap =
        g.n * g.edgeTo.length + g.n + 1 :=
    hsum.trans heq
  have hadd : g.n + 1 + dijkstraRun_staleCount fuel g dist heap ≤
      g.n * g.edgeTo.length + g.n + 1 := by
    have h := Nat.add_le_add_left hStale (g.n + 1)
    omega
  exact Nat.le_of_add_le_add_right (hadd.trans_eq htotal.symm)

theorem dijkstraRun_freshCount_ge_n_add_one_at_heapFuel {vg : ValidRustGraph n g} (s : Fin n)
    (dist : List Float) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (hStale :
      dijkstraRun_staleCount (dijkstraHeapFuel g) g dist heap ≤ n * g.edgeTo.length) :
    n + 1 ≤
      dijkstraRun_freshCount (dijkstraHeapFuel g) g dist heap := by
  have h := dijkstraRun_freshCount_ge_n_add_one_of_stale_bound (dijkstraHeapFuel g) dist heap rfl
    (by simpa [vg.hn] using hStale)
  rw [← vg.hn]
  exact h

theorem dijkstraRun_processedAcc_card_le_acc_add_fuel {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (acc : Finset (Fin n)) :
    (dijkstraRun_processedAcc vg dist heap hHeap fuel acc).card ≤ acc.card + fuel := by
  induction fuel generalizing dist heap hHeap acc with
  | zero => simp [dijkstraRun_processedAcc]
  | succ fuel ih =>
    cases hf : dijkstraStep_freshVertex vg dist heap hHeap with
    | none =>
      simp only [dijkstraRun_processedAcc, hf]
      exact Nat.le_trans (ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) acc) (Nat.le_add_right _ 1)
    | some u =>
      simp only [dijkstraRun_processedAcc, hf]
      refine Nat.le_trans (ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) (insert u acc)) ?_
      have hcard := Finset.card_insert_le u acc
      omega

theorem dijkstraRun_processed_card_le_fuel {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat) :
    (dijkstraRun_processed vg dist heap hHeap fuel).card ≤ fuel := by
  simpa [dijkstraRun_processed] using
    dijkstraRun_processedAcc_card_le_acc_add_fuel (vg := vg) dist heap hHeap fuel ∅

/-- Reduce heap-side completeness to edge-upper bounds once `dHat s = 0`. -/
theorem dijkstraStep_freshVertex_some {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (u : Fin n)
    (h : dijkstraStep_freshVertex vg dist heap hHeap = some u) :
    ∃ item rest, heapPopMin heap = some (item, rest) ∧ distStale dist item = false ∧ u.val = item.v := by
  rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
  · have hn : dijkstraStep_freshVertex vg dist heap hHeap = none := by
      cases heap with
      | nil => simp [dijkstraStep_freshVertex, heapPopMin, hpop]
      | cons x xs => simp [heapPopMin] at hpop
    exact absurd (h.symm.trans hn) (Option.some_ne_none u)
  · by_cases hstale : distStale dist item
    · have hn : dijkstraStep_freshVertex vg dist heap hHeap = none := by
        cases heap with
        | nil =>
          unfold heapPopMin at hpop
          simp at hpop
        | cons x xs =>
          cases hpop
          simp only [dijkstraStep_freshVertex, heapPopMin, hstale, ↓reduceIte]
      exact absurd (h.symm.trans hn) (Option.some_ne_none u)
    · have hstale' : distStale dist item = false := by simp [hstale]
      have hfresh : dijkstraStep_freshVertex vg dist heap hHeap =
          some ⟨item.v, vg.hn ▸ hHeap.valid item (heapPopMin_some_mem hpop)⟩ := by
        cases heap with
        | nil =>
          unfold heapPopMin at hpop
          simp at hpop
        | cons x xs =>
          cases hpop
          simp only [dijkstraStep_freshVertex, heapPopMin, ↓reduceIte]
          rw [if_neg (Bool.eq_false_iff.mp hstale')]
      have hu : u = ⟨item.v, vg.hn ▸ hHeap.valid item (heapPopMin_some_mem hpop)⟩ :=
        Option.some_inj.mp (h.symm.trans hfresh)
      refine ⟨item, rest, ?_, hstale', congrArg Fin.val hu⟩
      exact rfl

theorem dijkstraStep_isFresh_eq_iff_freshVertex {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) :
    dijkstraStep_isFresh dist heap = true ↔
      ∃ u, dijkstraStep_freshVertex vg dist heap hHeap = some u := by
  constructor
  · intro h
    rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
    · unfold dijkstraStep_isFresh at h
      simp [hpop] at h
    · unfold dijkstraStep_isFresh at h
      by_cases hstale : distStale dist item
      · simp [hpop, hstale] at h
      · refine ⟨⟨item.v, vg.hn ▸ hHeap.valid item (heapPopMin_some_mem hpop)⟩, ?_⟩
        unfold dijkstraStep_freshVertex
        cases heap with
        | nil =>
          unfold heapPopMin at hpop
          simp at hpop
        | cons x xs =>
          cases hpop
          simp only [dijkstraStep_freshVertex, heapPopMin, ↓reduceIte]
          rw [if_neg hstale]
  · rintro ⟨u, h⟩
    obtain ⟨_, _, hpop, hstale, _⟩ := dijkstraStep_freshVertex_some (vg := vg) dist heap hHeap u h
    unfold dijkstraStep_isFresh
    rw [hpop]
    simp [hstale]

theorem dijkstraStep_isFresh_eq_true_of_freshVertex_some {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (u : Fin n)
    (h : dijkstraStep_freshVertex vg dist heap hHeap = some u) :
    dijkstraStep_isFresh dist heap = true :=
  (dijkstraStep_isFresh_eq_iff_freshVertex (vg := vg) dist heap hHeap).2 ⟨u, h⟩

theorem dijkstraStep_freshVertex_some_of_isFresh_true {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (h : dijkstraStep_isFresh dist heap = true) :
    ∃ u, dijkstraStep_freshVertex vg dist heap hHeap = some u :=
  (dijkstraStep_isFresh_eq_iff_freshVertex (vg := vg) dist heap hHeap).1 h

theorem dijkstraStep_freshVertex_none_of_isFresh_false {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (h : dijkstraStep_isFresh dist heap = false) :
    dijkstraStep_freshVertex vg dist heap hHeap = none := by
  rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
  · rcases heap with ⟨⟩ | ⟨x, xs⟩
    · simp [dijkstraStep_freshVertex, dijkstraStep_isFresh, heapPopMin, hpop]
    · simp [heapPopMin] at hpop
  · by_cases hstale : distStale dist item
    · cases heap with
      | nil =>
        unfold heapPopMin at hpop
        simp at hpop
      | cons x xs =>
        cases hpop
        simp only [dijkstraStep_freshVertex, dijkstraStep_isFresh, heapPopMin, ↓reduceIte]
        rw [if_pos hstale]
    · have hfresh : dijkstraStep_isFresh dist heap = true := by
        unfold dijkstraStep_isFresh
        simp [hpop, hstale]
      simpa [hfresh] using h

theorem dijkstraRun_processedAcc_card_le_acc_add_freshCount {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (acc : Finset (Fin n)) :
    (dijkstraRun_processedAcc vg dist heap hHeap fuel acc).card ≤
      acc.card + dijkstraRun_freshCount fuel g dist heap := by
  induction fuel generalizing dist heap hHeap acc with
  | zero => simp [dijkstraRun_processedAcc, dijkstraRun_freshCount]
  | succ fuel ih =>
    simp only [dijkstraRun_processedAcc, dijkstraRun_freshCount]
    cases hf : dijkstraStep_freshVertex vg dist heap hHeap with
    | none =>
      have hfresh : dijkstraStep_isFresh dist heap = false := by
        match hif : dijkstraStep_isFresh dist heap with
        | false => rfl
        | true =>
          exfalso
          rcases dijkstraStep_freshVertex_some_of_isFresh_true (vg := vg) dist heap hHeap hif with
            ⟨u, hsome⟩
          rw [hf] at hsome
          exact (Option.some_ne_none u).elim (Eq.symm hsome)
      simp only [hf, hfresh, if_false]
      exact ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) acc
    | some u =>
      have hfresh : dijkstraStep_isFresh dist heap = true :=
        dijkstraStep_isFresh_eq_true_of_freshVertex_some (vg := vg) dist heap hHeap u hf
      simp only [hf, hfresh, if_true]
      have hcard := Finset.card_insert_le u acc
      refine Nat.le_trans (ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) (insert u acc)) ?_
      omega

theorem dijkstraRun_processed_card_le_freshCount {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat) :
    (dijkstraRun_processed vg dist heap hHeap fuel).card ≤
      dijkstraRun_freshCount fuel g dist heap := by
  simpa [dijkstraRun_processed] using
    dijkstraRun_processedAcc_card_le_acc_add_freshCount (vg := vg) dist heap hHeap fuel ∅

-- Each fresh pop extends the processed accumulator (`u` was not already counted).
-- The reason is the relaxation guard `if nd < d[tgt]!`: `dist[v]` is updated
-- only on strict improvement, so the distances pushed for any fixed `v` are
-- strictly decreasing.  Consequently at most one entry can ever carry
-- `d = trueDist v`.  After that entry is popped the vertex never reappears
-- as a fresh pop (any remaining entries for `v` satisfy `item.d > dist[v]`
-- and are therefore stale).  Formalising the invariant `relax_step_pushes_only_on_strict_improvement`
-- is the remaining step to discharge `FreshPopInsertsNew`.

-- The strict-improvement guard inside `dijkstraStep_fresh` (the `if nd < d[tgt]!` check)
-- ensures that distances pushed for any fixed vertex are strictly decreasing.
-- This invariant is required to prove `FreshPopInsertsNew` (each vertex is fresh-popped at most once).
-- Formalising the invariant via `List.foldl` induction proved fragile; it is documented here
-- and left as a future formalisation target (or via mathlib `List.Sorted` infrastructure).

def FreshPopInsertsNew {n : ℕ} {g : RustGraph} (vg : ValidRustGraph n g) : Prop :=
  ∀ (dist : List Float) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (acc : Finset (Fin n)) (u : Fin n),
    dijkstraStep_freshVertex vg dist heap hHeap = some u → u ∉ acc

theorem dijkstraRun_processedAcc_card_eq_acc_add_freshCount {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (acc : Finset (Fin n)) (hNew : FreshPopInsertsNew (vg := vg)) :
    (dijkstraRun_processedAcc vg dist heap hHeap fuel acc).card =
      acc.card + dijkstraRun_freshCount fuel g dist heap := by
  induction fuel generalizing dist heap hHeap acc with
  | zero => simp [dijkstraRun_processedAcc, dijkstraRun_freshCount]
  | succ fuel ih =>
    simp only [dijkstraRun_processedAcc, dijkstraRun_freshCount]
    cases hf : dijkstraStep_freshVertex vg dist heap hHeap with
    | none =>
      have hfresh : dijkstraStep_isFresh dist heap = false := by
        match hif : dijkstraStep_isFresh dist heap with
        | false => rfl
        | true =>
          exfalso
          rcases dijkstraStep_freshVertex_some_of_isFresh_true (vg := vg) dist heap hHeap hif with
            ⟨u, hsome⟩
          rw [hf] at hsome
          exact (Option.some_ne_none u).elim (Eq.symm hsome)
      have hstep := ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) acc
      simp [hf, hfresh, if_false, hstep]
    | some u =>
      have hfresh : dijkstraStep_isFresh dist heap = true :=
        dijkstraStep_isFresh_eq_true_of_freshVertex_some (vg := vg) dist heap hHeap u hf
      have hu : u ∉ acc := hNew dist heap hHeap acc u hf
      have hcard : (insert u acc).card = acc.card + 1 := Finset.card_insert_of_notMem hu
      have hstep := ih (dijkstraStep g dist heap).1 (dijkstraStep g dist heap).2
        (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) (insert u acc)
      simp only [hf, hfresh, if_true, hcard, hstep]
      omega

theorem dijkstraRun_processed_card_eq_freshCount {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (hNew : FreshPopInsertsNew (vg := vg)) :
    (dijkstraRun_processed vg dist heap hHeap fuel).card =
      dijkstraRun_freshCount fuel g dist heap := by
  simpa [dijkstraRun_processed] using
    dijkstraRun_processedAcc_card_eq_acc_add_freshCount (vg := vg) dist heap hHeap fuel ∅ hNew

/-- At `dijkstraHeapFuel`, a stale bound is equivalent to `freshCount ≥ n + 1` (fuel identity). -/
theorem dijkstraRun_staleBound_iff_freshCount_ge_at_heapFuel {vg : ValidRustGraph n g} (s : Fin n) :
    (dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] ≤
        n * g.edgeTo.length) ↔
      n + 1 ≤
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] := by
  have hsum := dijkstraRun_freshCount_add_staleCount (g := g) (dijkstraHeapFuel g)
    (initDist g s.val) [⟨0.0, s.val⟩]
  constructor
  · intro hStale
    simpa [vg.hn] using
      dijkstraRun_freshCount_ge_n_add_one_at_heapFuel (vg := vg) s (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) hStale
  · intro hfresh
    have hfresh' : g.n + 1 ≤
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] := by
      simpa [vg.hn] using hfresh
    have htotal :
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] +
            dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] =
          g.n * g.edgeTo.length + g.n + 1 := by
      rw [dijkstraHeapFuel] at hsum
      exact hsum
    have hle : g.n + 1 + dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val)
        [⟨0.0, s.val⟩] ≤
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] +
          dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] :=
      Nat.add_le_add_right hfresh' _
    have hstale :
        dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] ≤
          g.n * g.edgeTo.length := by
      have hbound :
          g.n + 1 + dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] ≤
            (g.n + 1) + (g.n * g.edgeTo.length) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle.trans_eq htotal
      exact Nat.le_of_add_le_add_left hbound
    simpa [vg.hn] using hstale

theorem Finset.card_eq_univ_of_card_eq_fin {s : Finset (Fin n)} (h : s.card = n) :
    s = Finset.univ :=
  Finset.eq_univ_of_card s (by simpa [Fintype.card_fin] using h)

theorem dijkstraRun_processed_eq_univ_of_card_eq_n {vg : ValidRustGraph n g} (dist : List Float)
    (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat)
    (h : (dijkstraRun_processed vg dist heap hHeap fuel).card = n) :
    dijkstraRun_processed vg dist heap hHeap fuel = Finset.univ :=
  Finset.card_eq_univ_of_card_eq_fin h

theorem dijkstraRun_processed_eq_univ_at_heapFuel_of_freshCount_ge_and_card {vg : ValidRustGraph n g}
    (s : Fin n)
    (hFresh :
      n ≤
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩])
    (hCard :
      (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)).card =
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩]) :
    dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) = Finset.univ := by
  have hle :=
    dijkstraRun_processed_card_le_freshCount (vg := vg) (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)
  have hfin :
      (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)).card ≤ n := by
    simpa [Fintype.card_fin] using
      Finset.card_le_univ (s := dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
  have hEq : (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)).card = n := by
    omega
  exact dijkstraRun_processed_eq_univ_of_card_eq_n (vg := vg) (initDist g s.val) [⟨0.0, s.val⟩]
    (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) hEq

theorem dijkstraRun_processed_eq_univ_at_heapFuel_of_freshPopInsertsNew {vg : ValidRustGraph n g}
    (s : Fin n) (hFresh :
      n ≤
        dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩])
    (hNew : FreshPopInsertsNew (vg := vg)) :
    dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) = Finset.univ := by
  have hCard :=
    dijkstraRun_processed_card_eq_freshCount (vg := vg) (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) hNew
  exact dijkstraRun_processed_eq_univ_at_heapFuel_of_freshCount_ge_and_card (vg := vg) s hFresh hCard

/-- Reduce heap-side completeness to edge-upper bounds once `dHat s = 0`. -/
theorem dijkstraRun_dHat_all_complete_of_edgeUpper {vg : ValidRustGraph n g} (s : Fin n)
    (fuel : Nat) (hEdge : EdgeUpper vg.toGraph s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) fuel)) :
    ∀ v : Fin n,
      IsComplete vg.toGraph s
        (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) fuel) v := by
  intro v
  let dHat := dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
    (heapStateInv_init (vg := vg) s) fuel
  obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
  have hSound : Sound vg.toGraph s dHat :=
    (dijkstraRun_simInv_exact (vg := vg) s fuel (initDist g s.val) (initEstimate s)
      [⟨0.0, s.val⟩] hSim hHeap).sound
  exact isComplete_of_sound_and_edgeUpper (G := vg.toGraph) (s := s) (dHat := dHat)
    (dijkstraRun_dHat_source_eq (vg := vg) s fuel) hSound hEdge v

/-- Reduce heap-side completeness at `dijkstraHeapFuel` to global `EdgeUpper`. -/
theorem dijkstraRun_dHat_all_complete_at_heapFuel_of_edgeUpper {vg : ValidRustGraph n g} (s : Fin n)
    (hEdge : EdgeUpper vg.toGraph s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))) :
    ∀ v : Fin n,
      IsComplete vg.toGraph s
        (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v :=
  dijkstraRun_dHat_all_complete_of_edgeUpper (vg := vg) s (dijkstraHeapFuel g) hEdge

/-- When `dijkstraRun_processed = Finset.univ`, reduce to processed-edge-upper + `SetComplete` on univ. -/
theorem dijkstraRun_dHat_all_complete_at_heapFuel_of_processed_eq_univ {vg : ValidRustGraph n g}
    (s : Fin n)
    (hEq :
      dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) = Finset.univ)
    (hProc : ProcessedEdgeUpper (G := vg.toGraph) s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
      (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)))
    (hSet : SetComplete vg.toGraph s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
      Finset.univ) :
    ∀ v : Fin n,
      IsComplete vg.toGraph s
        (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v :=
  have hProc_univ : ProcessedEdgeUpper (G := vg.toGraph) s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) Finset.univ := by
    simpa [hEq] using hProc
  dijkstraRun_dHat_all_complete_at_heapFuel_of_edgeUpper (vg := vg) s
    (edgeUpper_of_processedEdgeUpper_univ (G := vg.toGraph) (s := s)
      (dHat := dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
      hProc_univ hSet)

theorem dijkstraRun_dHat_ge_trueDist {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat)
    (v : Fin n) :
    trueDist vg.toGraph s v ≤
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) fuel v := by
  obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
  exact (dijkstraRun_simInv_exact (vg := vg) s fuel (initDist g s.val) (initEstimate s)
    [⟨0.0, s.val⟩] hSim hHeap).sound v

/-- Reduce heap-side completeness to a pointwise upper bound against `relaxRound n init`. -/
theorem dijkstraRun_dHat_all_complete_of_le_relaxRound_n {vg : ValidRustGraph n g} (s : Fin n)
    (fuel : Nat)
    (hUpper :
      ∀ v : Fin n,
        dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) fuel v ≤
          Algo.relaxRound vg.toGraph n (initEstimate s) v) :
    ∀ v : Fin n,
      IsComplete vg.toGraph s
        (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) fuel) v := by
  intro v
  refine isComplete_of_sound_and_upper (G := vg.toGraph) (s := s) (v := v) ?_ ?_
  · intro w
    exact dijkstraRun_dHat_ge_trueDist (vg := vg) s fuel w
  · intro w
    rw [← dijkstraSpec_correct, ← Algo.dijkstra_correct (G := vg.toGraph) (s := s) (v := w)]
    exact hUpper w

theorem dijkstraStep_dHat_le {vg : ValidRustGraph n g} (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (v : Fin n) : dijkstraStep_dHat vg dist dHat heap hHeap v ≤ dHat v := by
  rcases hpop : heapPopMin heap with ⟨⟩ | ⟨item, rest⟩
  · exact le_of_eq (congrFun (dijkstraStep_dHat_none (vg := vg) dist dHat heap hHeap hpop) v)
  · by_cases hstale : distStale dist item
    · have hstale' : distStale dist item = true := by simp [hstale]
      exact le_of_eq (congrFun (dijkstraStep_dHat_stale (vg := vg) dist dHat heap hHeap item rest hpop hstale') v)
    · have hstale' : distStale dist item = false := by simp [hstale]
      have hmem := heapPopMin_some_mem hpop
      let u : Fin n := ⟨item.v, vg.hn ▸ hHeap.valid item hmem⟩
      rw [dijkstraStep_dHat_fresh (vg := vg) dist dHat heap hHeap item rest u rfl hpop hstale']
      exact Algo.le_relaxOutEdges (G := vg.toGraph) (dHat := dHat) (u := u) (v := v)

/-- After a fresh pop, `ProcessedEdgeUpper` extends to the newly processed complete vertex. -/
theorem dijkstraStep_fresh_processedEdgeUpper {vg : ValidRustGraph n g} {s : Fin n}
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (hHeap : HeapStateInv (vg := vg) dist heap) (acc : Finset (Fin n)) (uPop : Fin n)
    (hFresh : dijkstraStep_freshVertex vg dist heap hHeap = some uPop)
    (hEdge : ProcessedEdgeUpper (G := vg.toGraph) s dHat acc)
    (hComplete : IsComplete vg.toGraph s dHat uPop) :
    ProcessedEdgeUpper (G := vg.toGraph) s (dijkstraStep_dHat vg dist dHat heap hHeap) (insert uPop acc) := by
  intro z hz y w hwt
  rcases Finset.mem_insert.mp hz with hzEq | hz
  · rw [hzEq]
    rw [hzEq] at hwt
    obtain ⟨item, rest, hpop, hstale, hitemv⟩ :=
      dijkstraStep_freshVertex_some (vg := vg) dist heap hHeap uPop hFresh
    have hitemv' : item.v = uPop.val := hitemv.symm
    have hnotStale : distStale dist item = false := by simp [hstale]
    rw [dijkstraStep_dHat_fresh (vg := vg) dist dHat heap hHeap item rest uPop hitemv' hpop hnotStale]
    calc
      (relaxOutEdges vg.toGraph dHat uPop) y ≤ dHat uPop + (w : WithTop NNReal) :=
        Algo.relaxOutEdges_le_add_edge (G := vg.toGraph) dHat uPop y w hwt
      _ = trueDist vg.toGraph s uPop + (w : WithTop NNReal) := by rw [hComplete]
  · exact (dijkstraStep_dHat_le (vg := vg) dist dHat heap hHeap y).trans (hEdge z hz y w hwt)

/-- After a non-fresh heap step, `ProcessedEdgeUpper` on the past accumulator is preserved. -/
theorem dijkstraStep_stale_processedEdgeUpper {vg : ValidRustGraph n g} {s : Fin n}
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (hHeap : HeapStateInv (vg := vg) dist heap) (acc : Finset (Fin n))
    (_hFresh : dijkstraStep_freshVertex vg dist heap hHeap = none)
    (hEdge : ProcessedEdgeUpper (G := vg.toGraph) s dHat acc) :
    ProcessedEdgeUpper (G := vg.toGraph) s (dijkstraStep_dHat vg dist dHat heap hHeap) acc := by
  intro x hx y w hwt
  exact (dijkstraStep_dHat_le (vg := vg) dist dHat heap hHeap y).trans (hEdge x hx y w hwt)

/-- If every fresh pop is complete w.r.t. the current estimate, `ProcessedEdgeUpper` is preserved
    on the past-only processed accumulator through a heap run. -/
theorem dijkstraRun_processedAcc_processedEdgeUpper {vg : ValidRustGraph n g} {s : Fin n}
    (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
    (hHeap : HeapStateInv (vg := vg) dist heap) (fuel : Nat) (acc : Finset (Fin n))
    (hEdge : ProcessedEdgeUpper (G := vg.toGraph) s dHat acc)
    (hFreshComplete :
      ∀ (dist' : List Float) (dHat' : DistEstimate n) (heap' : List HeapItem)
        (hHeap' : HeapStateInv (vg := vg) dist' heap') (acc' : Finset (Fin n)) (uPop : Fin n),
        dijkstraStep_freshVertex vg dist' heap' hHeap' = some uPop →
        ProcessedEdgeUpper (G := vg.toGraph) s dHat' acc' →
        IsComplete vg.toGraph s dHat' uPop) :
    ProcessedEdgeUpper (G := vg.toGraph) s
      (dijkstraRun_dHat vg dist dHat heap hHeap fuel)
      (dijkstraRun_processedAcc vg dist heap hHeap fuel acc) := by
  induction fuel generalizing dist dHat heap hHeap acc hEdge with
  | zero =>
    simp [dijkstraRun_processedAcc, dijkstraRun_dHat]
    exact hEdge
  | succ fuel ih =>
    cases hf : dijkstraStep_freshVertex vg dist heap hHeap with
    | none =>
      simp only [dijkstraRun_processedAcc, dijkstraRun_dHat, hf]
      exact ih (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap)
        (dijkstraStep g dist heap).2 (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap) acc
        (dijkstraStep_stale_processedEdgeUpper (vg := vg) (s := s) dist dHat heap hHeap acc hf hEdge)
    | some uPop =>
      simp only [dijkstraRun_processedAcc, dijkstraRun_dHat, hf]
      have hComplete := hFreshComplete dist dHat heap hHeap acc uPop hf hEdge
      exact ih (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap)
        (dijkstraStep g dist heap).2 (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap)
        (insert uPop acc)
        (dijkstraStep_fresh_processedEdgeUpper (vg := vg) (s := s) dist dHat heap hHeap acc uPop hf
          hEdge hComplete)

theorem dijkstraRun_processed_processedEdgeUpper {vg : ValidRustGraph n g} {s : Fin n}
    (fuel : Nat)
    (hFreshComplete :
      ∀ (dist : List Float) (dHat : DistEstimate n) (heap : List HeapItem)
        (hHeap : HeapStateInv (vg := vg) dist heap) (acc : Finset (Fin n)) (uPop : Fin n),
        dijkstraStep_freshVertex vg dist heap hHeap = some uPop →
        ProcessedEdgeUpper (G := vg.toGraph) s dHat acc →
        IsComplete vg.toGraph s dHat uPop) :
    ProcessedEdgeUpper (G := vg.toGraph) s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) fuel)
      (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) fuel) := by
  simpa [dijkstraRun_processed] using
    dijkstraRun_processedAcc_processedEdgeUpper (vg := vg) (s := s) (initDist g s.val)
      (initEstimate s) [⟨0.0, s.val⟩] (heapStateInv_init (vg := vg) s) fuel ∅
      (processedEdgeUpper_empty (G := vg.toGraph) s (initEstimate s)) hFreshComplete

theorem dijkstraRun_dHat_mono {vg : ValidRustGraph n g} (dist : List Float)
    (dHat : DistEstimate n) (heap : List HeapItem) (hHeap : HeapStateInv (vg := vg) dist heap)
    (fuel : Nat) (v : Fin n) :
    dijkstraRun_dHat vg dist dHat heap hHeap (fuel + 1) v ≤
      dijkstraRun_dHat vg dist dHat heap hHeap fuel v := by
  induction fuel generalizing dist dHat heap hHeap with
  | zero =>
    simp [dijkstraRun_dHat]
    exact dijkstraStep_dHat_le (vg := vg) dist dHat heap hHeap v
  | succ fuel ih =>
    simp only [dijkstraRun_dHat]
    exact ih (dijkstraStep g dist heap).1 (dijkstraStep_dHat vg dist dHat heap hHeap)
      (dijkstraStep g dist heap).2 (dijkstraStep_preserves_heapInv (vg := vg) dist heap hHeap)

/-- Equal `DistEstimate`s when every vertex is complete on both. -/
theorem dHat_eq_of_all_IsComplete {G : Graph n} {s : Fin n}
    {dHat1 dHat2 : DistEstimate n}
    (h1 : ∀ v, IsComplete G s dHat1 v) (h2 : ∀ v, IsComplete G s dHat2 v) :
    dHat1 = dHat2 := by
  ext v
  rw [h1 v, h2 v]

theorem dijkstraRun_dist_sound {vg : ValidRustGraph n g} (s : Fin n) (fuel : Nat) :
    DistSound vg.toGraph s (dijkstraRun fuel g (initDist g s.val) [⟨0.0, s.val⟩]).1 := by
  constructor
  · obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
    have hSim' := dijkstraRun_simInv_exact (vg := vg) s fuel (initDist g s.val) (initEstimate s)
      [⟨0.0, s.val⟩] hSim hHeap
    exact hSim'.len
  · intro v
    obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
    have hSim' := dijkstraRun_simInv_exact (vg := vg) s fuel (initDist g s.val) (initEstimate s)
      [⟨0.0, s.val⟩] hSim hHeap
    rw [hSim'.aligned v]
    exact nnrealToFloat_monotone (hSim'.sound v)

/-- When the heap-side tracked estimate is complete everywhere, it equals verified `dijkstra`. -/
theorem dijkstraRun_dHat_eq_dijkstra_of_all_complete {vg : ValidRustGraph n g} (s : Fin n)
    (fuel : Nat)
    (hComplete :
      ∀ v : Fin n,
        IsComplete vg.toGraph s
          (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
            (heapStateInv_init (vg := vg) s) fuel) v) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) fuel = Algo.dijkstra vg.toGraph s := by
  ext v
  rw [hComplete v, Algo.dijkstra_correct (G := vg.toGraph) (s := s) (v := v), dijkstraSpec_correct]

/-- Distance lists agree when the heap-side estimate is complete at both fuels. -/
theorem dijkstraRun_eq_floatRelaxRound_of_heap_complete {vg : ValidRustGraph n g} (s : Fin n)
    (heapFuel relaxFuel : Nat) (hRelaxFuel : relaxFuel = n)
    (hHeapComplete :
      ∀ v : Fin n,
        IsComplete vg.toGraph s
          (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
            (heapStateInv_init (vg := vg) s) heapFuel) v) :
    (dijkstraRun heapFuel g (initDist g s.val) [⟨0.0, s.val⟩]).1 =
      floatRelaxRound relaxFuel g (initDist g s.val) := by
  obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
  apply dist_eq_of_simInv_both_complete
  · exact dijkstraRun_simInv_exact (vg := vg) s heapFuel (initDist g s.val) (initEstimate s)
      [⟨0.0, s.val⟩] hSim hHeap
  · exact floatRelaxRound_simInv (vg := vg) s relaxFuel (initDist g s.val) (initEstimate s) hSim
  · exact hHeapComplete
  · intro v
    subst hRelaxFuel
    exact relaxRound_n_all_complete vg.toGraph s v

/-- Schedule alignment at `dijkstraHeapFuel`, assuming heap-side completeness. -/
theorem dijkstraRun_dHat_schedule_of_all_complete {vg : ValidRustGraph n g} (s : Fin n)
    (hComplete :
      ∀ v : Fin n,
        IsComplete vg.toGraph s
          (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
            (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph n (initEstimate s) := by
  apply dHat_eq_of_all_IsComplete
  · exact hComplete
  · intro v
    exact relaxRound_n_all_complete vg.toGraph s v

/-- Schedule alignment from the upper-bound completeness reduction. -/
theorem dijkstraRun_dHat_schedule_of_upper {vg : ValidRustGraph n g} (s : Fin n)
    (hUpper :
      ∀ v : Fin n,
        dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) v ≤
          Algo.relaxRound vg.toGraph n (initEstimate s) v) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph n (initEstimate s) :=
  dijkstraRun_dHat_schedule_of_all_complete (vg := vg) s
    (dijkstraRun_dHat_all_complete_of_le_relaxRound_n (vg := vg) s (dijkstraHeapFuel g) hUpper)

/-- Reduce schedule alignment to heap-side completeness at `dijkstraHeapFuel`.

    **Open:** prove `dijkstraRun_dHat_all_complete_at_heapFuel` — e.g. via terminal
    `EdgeUpper` (not preserved from `initEstimate`), or `dHat ≤ relaxRound n init`. Once
    proved, use `dijkstraRun_dHat_schedule_of_all_complete`. -/
theorem dijkstraRun_dHat_schedule (vg : ValidRustGraph n g) (s : Fin n)
    (hComplete :
      ∀ v : Fin n,
        IsComplete vg.toGraph s
          (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
            (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph n (initEstimate s) :=
  dijkstraRun_dHat_schedule_of_all_complete (vg := vg) s hComplete

/-- When heap and float schedules share a final `DistEstimate`, distance lists agree. -/
theorem dijkstraRun_eq_floatRelaxRound {vg : ValidRustGraph n g} (s : Fin n)
    (heapFuel relaxFuel : Nat)
    (hSchedule :
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) heapFuel =
      relaxRound vg.toGraph relaxFuel (initEstimate s)) :
    (dijkstraRun heapFuel g (initDist g s.val) [⟨0.0, s.val⟩]).1 =
      floatRelaxRound relaxFuel g (initDist g s.val) := by
  obtain ⟨hSim, hHeap⟩ := dijkstraInit_simInv (vg := vg) s
  apply dist_eq_of_simInv_dHat_eq hSchedule
  · exact dijkstraRun_simInv_exact (vg := vg) s heapFuel (initDist g s.val) (initEstimate s)
      [⟨0.0, s.val⟩] hSim hHeap
  · exact floatRelaxRound_simInv (vg := vg) s relaxFuel (initDist g s.val) (initEstimate s) hSim

/-- Reduce `dijkstraHeap = dijkstraRelax` to schedule alignment at heap fuel vs `n` relax rounds. -/
theorem dijkstraHeap_eq_dijkstraRelax_of_schedule {vg : ValidRustGraph n g} (s : Fin n)
    (hSchedule :
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph g.n (initEstimate s)) :
    dijkstraHeap g s.val = dijkstraRelax g s.val := by
  rw [dijkstraHeap_eq_dijkstraRun, dijkstraRelax]
  have hSchedule' :
      dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph n (initEstimate s) := by
    rw [vg.hn] at hSchedule
    exact hSchedule
  simpa [vg.hn] using
    dijkstraRun_eq_floatRelaxRound (vg := vg) s (dijkstraHeapFuel g) n hSchedule'

/-! ### Settlement bundle (Phase 3c.4 target hypotheses)

    Discharging `dijkstraHeap_eq_dijkstraRelax` reduces to proving `HeapSettlement`
    (or the individual fields below). Fuel accounting lemmas show
    `freshCount ≥ n + 1` once `staleCount ≤ n * |edgeTo|`. -/

/-- Bundled heap-side obligations for schedule alignment at `dijkstraHeapFuel`. -/
structure HeapSettlement {n : ℕ} {g : RustGraph} (vg : ValidRustGraph n g) (s : Fin n) : Prop where
  /-- At heap fuel this is equivalent to `staleBound` via `dijkstraRun_staleBound_iff_freshCount_ge_at_heapFuel`. -/
  freshCount_ge :
    n + 1 ≤
      dijkstraRun_freshCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩]
  /-- Every vertex received a fresh pop by heap fuel. -/
  processed_univ :
    dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) = Finset.univ
  /-- Pointwise completeness on the processed frontier (usually from per-step settlement). -/
  setComplete_univ :
    SetComplete vg.toGraph s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
      Finset.univ
  /-- Edge-upper bounds along processed vertices. -/
  processedEdgeUpper :
    ProcessedEdgeUpper (G := vg.toGraph) s
      (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))
      (dijkstraRun_processed vg (initDist g s.val) [⟨0.0, s.val⟩]
        (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g))

namespace HeapSettlement

variable {n : ℕ} {g : RustGraph} {vg : ValidRustGraph n g} {s : Fin n}

theorem staleBound (h : HeapSettlement vg s) :
    dijkstraRun_staleCount (dijkstraHeapFuel g) g (initDist g s.val) [⟨0.0, s.val⟩] ≤
      n * g.edgeTo.length :=
  (dijkstraRun_staleBound_iff_freshCount_ge_at_heapFuel (vg := vg) s).2 h.freshCount_ge

end HeapSettlement

/-- Target completeness at heap fuel, assuming the settlement bundle. -/
theorem dijkstraRun_dHat_all_complete_at_heapFuel {vg : ValidRustGraph n g} (s : Fin n)
    (hSettle : HeapSettlement vg s) :
    ∀ v : Fin n,
      IsComplete vg.toGraph s
        (dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
          (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g)) v :=
  dijkstraRun_dHat_all_complete_at_heapFuel_of_processed_eq_univ (vg := vg) s
    hSettle.processed_univ hSettle.processedEdgeUpper hSettle.setComplete_univ

/-- Unconditional schedule alignment from settlement. -/
theorem dijkstraRun_dHat_schedule_of_settlement {vg : ValidRustGraph n g} (s : Fin n)
    (hSettle : HeapSettlement vg s) :
    dijkstraRun_dHat vg (initDist g s.val) (initEstimate s) [⟨0.0, s.val⟩]
      (heapStateInv_init (vg := vg) s) (dijkstraHeapFuel g) =
      relaxRound vg.toGraph n (initEstimate s) :=
  dijkstraRun_dHat_schedule (vg := vg) s
    (dijkstraRun_dHat_all_complete_at_heapFuel (vg := vg) s hSettle)

end Refine
end Sssp
