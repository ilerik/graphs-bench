/-
  Sssp.Refine.RelaxBridge

  Align CSR `floatRelax*` with verified `relax*` on `csrToGraph` (Phase 3b/3c).
  Edge alignment: `floatRelaxEdge_aligned` proved; out alignment proved modulo
  `relaxOutEdges_eq_relaxCsrOut`; all-round still axiomatized.
-/

import Mathlib
import Sssp.Refine.GraphBridge
import Sssp.Refine.NumericBridge
import Sssp.Algo.Dijkstra

namespace Sssp
namespace Refine

open Sssp Algo FloatNat

variable {n : ℕ} {g : RustGraph}

structure SimInv {g : RustGraph} (vg : ValidRustGraph n g) (s : Fin n)
    (dist : List Float) (dHat : DistEstimate n) : Prop where
  len : dist.length = n
  aligned : ∀ v : Fin n, dist[v.val]! = nnrealToFloat (dHat v)
  sound : Sound vg.toGraph s dHat

/-! ### List length -/

theorem floatRelaxEdge_length (dist : List Float) (u tgt : Nat) (w : Float) (hn : dist.length = g.n) :
    (floatRelaxEdge dist u tgt w).length = g.n := by
  simp only [floatRelaxEdge]; split_ifs <;> simp [List.length_set, hn]

theorem floatRelaxOut_length (dist : List Float) (u : Nat) (hn : dist.length = g.n) :
    (floatRelaxOut g dist u).length = g.n := by
  dsimp [floatRelaxOut]
  induction g.outEdges u generalizing dist with
  | nil => exact hn
  | cons p xs ih =>
    simp only [List.foldl_cons]
    exact ih (floatRelaxEdge dist u p.1 p.2) (floatRelaxEdge_length dist u p.1 p.2 hn)

theorem floatRelaxAll_length (dist : List Float) (hn : dist.length = g.n) (hgn : g.n = n) :
    (floatRelaxAll g dist).length = n := by
  dsimp [floatRelaxAll]
  induction List.range g.n generalizing dist with
  | nil => rw [← hgn]; exact hn
  | cons u us ih =>
    simp only [List.foldl_cons]
    exact ih (floatRelaxOut g dist u) (floatRelaxOut_length dist u hn)

/-! ### List lookup -/

private theorem floatRelaxEdge_get_ne (dist : List Float) (u tgt i : Nat) (w : Float)
    (hi : i < dist.length) (hne : i ≠ tgt) :
    (floatRelaxEdge dist u tgt w)[i]! = dist[i]! := by
  simp only [floatRelaxEdge]
  split_ifs <;> grind

/-! ### Edge alignment -/

/-- Single-edge float relax matches verified `relaxEdge` off the target vertex. -/
theorem floatRelaxEdge_aligned_ne {vg : ValidRustGraph n g} (dHat : DistEstimate n)
    (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) (u v : Fin n) (w : Nat)
    (x : Fin n) (hx : x ≠ v) :
    (floatRelaxEdge dist u.val v.val (floatWeight w))[x.val]! =
      nnrealToFloat (relaxEdge dHat u v (nnrealWeight w) x) := by
  have hi : x.val < dist.length := by rw [hlen]; exact x.isLt
  have hne : x.val ≠ v.val := fun heq => hx (Fin.ext heq)
  rw [floatRelaxEdge_get_ne dist u.val v.val x.val (floatWeight w) hi hne]
  simp [relaxEdge, Function.update, hx, halign x]

/-- Single-edge float relax matches verified `relaxEdge` at the target vertex. -/
theorem floatRelaxEdge_aligned_v {vg : ValidRustGraph n g} (dHat : DistEstimate n)
    (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) (u v : Fin n) (w : Nat) :
    (floatRelaxEdge dist u.val v.val (floatWeight w))[v.val]! =
      nnrealToFloat (relaxEdge dHat u v (nnrealWeight w) v) := by
  by_cases hlt : dist[u.val]! + floatWeight w < dist[v.val]!
  · have halign_u := halign u
    have halign_v := halign v
    have hfloat : nnrealToFloat (dHat u) + floatWeight w < nnrealToFloat (dHat v) := by
      rw [← halign_u, ← halign_v]; simpa [floatWeight] using hlt
    have hget : (dist.set v.val (dist[u.val]! + floatWeight w))[v.val]! =
        dist[u.val]! + floatWeight w := by grind
    have hf : floatRelaxEdge dist u.val v.val (floatWeight w) =
        dist.set v.val (dist[u.val]! + floatWeight w) := by
      dsimp [floatRelaxEdge]; rw [if_pos hlt]
    have hr : relaxEdge dHat u v (nnrealWeight w) v = min (dHat v) (dHat u + ↑(nnrealWeight w)) := by
      simp [relaxEdge, Function.update, nnrealWeight]
    have hmin : nnrealToFloat (dHat u) + floatWeight w =
        nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) := by
      calc nnrealToFloat (dHat u) + floatWeight w
        _ = min (nnrealToFloat (dHat v)) (nnrealToFloat (dHat u) + floatWeight w) := by
            exact (float_min_eq_right_of_le (float_le_of_lt hfloat)).symm
        _ = min (nnrealToFloat (dHat v)) (nnrealToFloat (dHat u + ↑(nnrealWeight w))) := by
            congr 1; exact (nnrealToFloat_add_weight (dHat u) w).symm
        _ = nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) :=
            (nnrealToFloat_min (dHat v) (dHat u + ↑(nnrealWeight w))).symm
    calc
      (floatRelaxEdge dist u.val v.val (floatWeight w))[v.val]!
          = (dist.set v.val (dist[u.val]! + floatWeight w))[v.val]! := by rw [hf]
      _ = dist[u.val]! + floatWeight w := hget
      _ = nnrealToFloat (dHat u) + floatWeight w := by rw [halign u]
      _ = nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) := hmin
      _ = nnrealToFloat (relaxEdge dHat u v (nnrealWeight w) v) := by rw [hr]
  · have halign_v := halign v
    have hle : dist[v.val]! ≤ dist[u.val]! + floatWeight w := float_le_of_not_lt hlt
    have hfloat : nnrealToFloat (dHat v) ≤ nnrealToFloat (dHat u + ↑(nnrealWeight w)) := by
      have hadd := nnrealToFloat_add_weight (dHat u) w
      rw [show nnrealToFloat (dHat u + ↑(nnrealWeight w)) =
          nnrealToFloat (dHat u) + floatWeight w from hadd]
      rw [← halign u, ← halign v]
      exact hle
    have hf : floatRelaxEdge dist u.val v.val (floatWeight w) = dist := by
      dsimp [floatRelaxEdge]; rw [if_neg hlt]
    have hr : relaxEdge dHat u v (nnrealWeight w) v = min (dHat v) (dHat u + ↑(nnrealWeight w)) := by
      simp [relaxEdge, Function.update, nnrealWeight]
    have hmin : nnrealToFloat (dHat v) =
        nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) := by
      calc nnrealToFloat (dHat v)
        _ = min (nnrealToFloat (dHat v)) (nnrealToFloat (dHat u + ↑(nnrealWeight w))) :=
            (float_min_eq_left_of_le hfloat).symm
        _ = nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) :=
            (nnrealToFloat_min (dHat v) (dHat u + ↑(nnrealWeight w))).symm
    calc
      (floatRelaxEdge dist u.val v.val (floatWeight w))[v.val]!
          = dist[v.val]! := by rw [hf]
      _ = nnrealToFloat (dHat v) := halign v
      _ = nnrealToFloat (min (dHat v) (dHat u + ↑(nnrealWeight w))) := hmin
      _ = nnrealToFloat (relaxEdge dHat u v (nnrealWeight w) v) := by rw [hr]

theorem floatRelaxEdge_aligned {vg : ValidRustGraph n g} (dHat : DistEstimate n)
    (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) (u v : Fin n) (w : Nat)
    (_hmem : nnrealWeight w ∈ vg.toGraph.edges u v) :
    ∀ x : Fin n,
      (floatRelaxEdge dist u.val v.val (floatWeight w))[x.val]! =
        nnrealToFloat (relaxEdge dHat u v (nnrealWeight w) x) := by
  intro x
  by_cases hx : x = v
  · cases hx
    exact floatRelaxEdge_aligned_v (vg := vg) dHat dist hlen halign u v w
  · exact floatRelaxEdge_aligned_ne (vg := vg) dHat dist hlen halign u v w x hx

/-! ### Out-edge alignment -/

/-- `Fin n` / `NNReal` edge at CSR index `i` (same order as `floatRelaxOut`). -/
noncomputable def csrOutEdgeFin (vg : ValidRustGraph n g) (u : Fin n) (i : Nat)
    (hi : i < (g.outEdges u.val).length) : Fin n × NNReal :=
  let p := (g.outEdges u.val)[i]'hi
  (⟨p.1, vg.htgt u p (List.getElem_mem hi)⟩, nnrealWeight (vg.hwt.edgeWeight u.val i hi))

/-- Relax CSR out-edges in index order (matches `floatRelaxOut`). -/
private noncomputable def relaxCsrOutAux (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n)
    (idx : Nat) (edges : List (Nat × Float)) (hidx : idx + edges.length = (g.outEdges u.val).length) :
    DistEstimate n :=
  match edges with
  | [] => dHat
  | p :: xs =>
    have hi : idx < (g.outEdges u.val).length := by
      rw [← hidx, List.length_cons]; omega
    relaxCsrOutAux vg u
      (relaxEdge dHat u (csrOutEdgeFin vg u idx hi).1 (csrOutEdgeFin vg u idx hi).2)
      (idx + 1) xs (by rw [← hidx, List.length_cons]; omega)

noncomputable def relaxCsrOut (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n) :
    DistEstimate n :=
  relaxCsrOutAux vg u dHat 0 (g.outEdges u.val) (by simp)

private lemma mem_edges_of_csrOutEdgeFin (vg : ValidRustGraph n g) (u v : Fin n) (i : Nat)
    (hi : i < (g.outEdges u.val).length)
    (htgt' : ((g.outEdges u.val)[i]'hi).1 = v.val) :
    (csrOutEdgeFin vg u i hi).2 ∈ vg.toGraph.edges u v := by
  dsimp [csrOutEdgeFin]
  refine RustGraph.csr_outEdge_mem (g := g) (n := n) vg.hn (hwt := vg.hwt) (htgt := vg.htgt)
    (hdeg := vg.hdeg) hi htgt' rfl

private lemma drop_zero (l : List (Nat × Float)) : l.drop 0 = l := by simp

private theorem floatRelaxOut_relaxCsrOutAux_aligned (vg : ValidRustGraph n g) (u : Fin n)
    (dHat : DistEstimate n) (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) (csrIdx : Nat)
    (edges : List (Nat × Float)) (hcsrIdx : csrIdx + edges.length = (g.outEdges u.val).length)
    (hsub : edges = (g.outEdges u.val).drop csrIdx) :
    ∀ x : Fin n,
      (edges.foldl (fun dist' edge => floatRelaxEdge dist' u.val edge.1 edge.2) dist)[x.val]! =
        nnrealToFloat ((relaxCsrOutAux vg u dHat csrIdx edges hcsrIdx) x) := by
  intro x
  revert x hsub hcsrIdx csrIdx halign hlen dist dHat
  induction edges with
  | nil =>
    intro dHat dist hlen halign csrIdx hcsrIdx hsub x
    simp [relaxCsrOutAux, halign x]
  | cons edge xs ih =>
    intro dHat dist hlen halign csrIdx hcsrIdx hsub x
    have hi : csrIdx < (g.outEdges u.val).length := by
      rw [← hcsrIdx, List.length_cons]; omega
    have hdrop : (g.outEdges u.val).drop csrIdx = edge :: xs := by simpa [hsub] using hsub
    have hedge : (g.outEdges u.val)[csrIdx]'hi = edge := by
      have hcons := List.cons_getElem_drop_succ (l := g.outEdges u.val) (n := csrIdx) (h := hi)
      rw [hdrop] at hcons
      injection hcons with hhead _
    let e := csrOutEdgeFin vg u csrIdx hi
    let v : Fin n := e.1
    let w : Nat := vg.hwt.edgeWeight u.val csrIdx hi
    have htgt_mem : edge.1 = v.val := by dsimp [e, csrOutEdgeFin, v]; simp [hedge]
    have htgt' : ((g.outEdges u.val)[csrIdx]'hi).1 = v.val := by simpa [hedge] using htgt_mem
    have hmem : nnrealWeight w ∈ vg.toGraph.edges u v :=
      mem_edges_of_csrOutEdgeFin vg u v csrIdx hi htgt'
    let dist' := floatRelaxEdge dist u.val edge.1 edge.2
    let dHat' := relaxEdge dHat u e.1 e.2
    have hlen' : dist'.length = n := by
      have hg : dist.length = g.n := hlen.trans vg.hn.symm
      rw [← vg.hn]
      exact floatRelaxEdge_length dist u.val edge.1 edge.2 hg
    have halign' : ∀ y : Fin n, dist'[y.val]! = nnrealToFloat (dHat' y) := by
      intro y
      have hfw : floatWeight w = edge.2 := by
        dsimp [w, e, csrOutEdgeFin]
        rw [vg.hwt.edgeWeight_spec, hedge]
      have hv : v.val = edge.1 := htgt_mem.symm
      simpa [dist', dHat', v, e, hv, hfw] using
        floatRelaxEdge_aligned (vg := vg) dHat dist hlen halign u v w hmem y
    have hcsrIdx' : (csrIdx + 1) + xs.length = (g.outEdges u.val).length := by
      rw [← hcsrIdx, List.length_cons]; omega
    have hsub' : xs = (g.outEdges u.val).drop (csrIdx + 1) := by
      calc xs = List.drop 1 (edge :: xs) := rfl
        _ = List.drop 1 ((g.outEdges u.val).drop csrIdx) := by rw [← hdrop]
        _ = (g.outEdges u.val).drop (csrIdx + 1) := by rw [List.drop_drop]
    simp only [relaxCsrOutAux, List.foldl_cons]
    exact ih dHat' dist' hlen' halign' (csrIdx + 1) hcsrIdx' hsub' x

private theorem floatRelaxOut_relaxCsrOut_aligned (vg : ValidRustGraph n g) (u : Fin n)
    (dHat : DistEstimate n) (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ x : Fin n,
      (floatRelaxOut g dist u.val)[x.val]! = nnrealToFloat (relaxCsrOut vg u dHat x) := by
  intro x
  dsimp [floatRelaxOut, relaxCsrOut]
  exact floatRelaxOut_relaxCsrOutAux_aligned (vg := vg) u dHat dist hlen halign 0 (g.outEdges u.val)
    (by simp) (drop_zero (g.outEdges u.val)) x

axiom relaxOutEdges_eq_relaxCsrOut (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n) :
    relaxOutEdges vg.toGraph dHat u = relaxCsrOut vg u dHat

theorem floatRelaxOut_aligned (vg : ValidRustGraph n g) (dHat : DistEstimate n) (dist : List Float)
    (u : Fin n) (hlen : dist.length = n) (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ x : Fin n,
      (floatRelaxOut g dist u.val)[x.val]! = nnrealToFloat (relaxOutEdges vg.toGraph dHat u x) := by
  intro x
  rw [floatRelaxOut_relaxCsrOut_aligned (vg := vg) u dHat dist hlen halign x,
    relaxOutEdges_eq_relaxCsrOut (vg := vg) (u := u) (dHat := dHat)]

private theorem foldl_floatRelaxOut_aligned (vg : ValidRustGraph n g) (us : List (Fin n))
    (dHat : DistEstimate n) (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ x : Fin n,
      ((us.map fun u => u.val).foldl (fun dist' u => floatRelaxOut g dist' u) dist)[x.val]! =
        nnrealToFloat ((us.foldl (fun dHat' u => relaxOutEdges vg.toGraph dHat' u) dHat) x) := by
  induction us generalizing dHat dist with
  | nil =>
    intro x
    simp [halign x]
  | cons u us ih =>
    intro x
    have hlen' : (floatRelaxOut g dist u.val).length = n := by
      have hg : dist.length = g.n := hlen.trans vg.hn.symm
      exact (floatRelaxOut_length dist u.val hg).trans vg.hn
    have halign' : ∀ y : Fin n,
        (floatRelaxOut g dist u.val)[y.val]! =
          nnrealToFloat ((relaxOutEdges vg.toGraph dHat u) y) :=
      floatRelaxOut_aligned vg dHat dist u hlen halign
    simpa [List.map_cons, List.foldl_cons] using
      ih (dHat := relaxOutEdges vg.toGraph dHat u) (dist := floatRelaxOut g dist u.val)
        hlen' halign' x

theorem foldl_range_floatRelaxAll_aligned (vg : ValidRustGraph n g) (dHat : DistEstimate n)
    (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ v : Fin n,
      (floatRelaxAll g dist)[v.val]! = nnrealToFloat (relaxAll vg.toGraph dHat v) := by
  intro v
  dsimp [floatRelaxAll, relaxAll]
  have hrange : List.range g.n = (List.finRange n).map (fun u : Fin n => u.val) := by
    rw [vg.hn]
    exact (List.map_coe_finRange_eq_range (n := n)).symm
  rw [hrange]
  exact foldl_floatRelaxOut_aligned vg (List.finRange n) dHat dist hlen halign v

theorem floatRelaxAll_simInv (vg : ValidRustGraph n g) (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (h : SimInv vg s dist dHat) :
    SimInv vg s (floatRelaxAll g dist) (relaxAll vg.toGraph dHat) where
  len := floatRelaxAll_length dist (by rw [vg.hn]; exact h.len) vg.hn
  aligned := fun v => foldl_range_floatRelaxAll_aligned vg dHat dist h.len h.aligned v
  sound := relaxAll_sound (G := vg.toGraph) (s := s) dHat h.sound

end Refine
end Sssp
