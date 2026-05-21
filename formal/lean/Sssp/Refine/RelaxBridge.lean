/-
  Sssp.Refine.RelaxBridge

  Align CSR `floatRelax*` with verified `relax*` on `csrToGraph` (Phase 3b/3c).
  Edge alignment: `floatRelaxEdge_aligned` proved; out alignment via
  `relaxOutEdges_eq_relaxCsrOut`; all-round via `foldl_range_floatRelaxAll_aligned`.
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
    (idx : Nat) (edges : List (Nat × Float)) : DistEstimate n :=
  match edges with
  | [] => dHat
  | _ :: xs =>
    if hi : idx < (g.outEdges u.val).length then
      relaxCsrOutAux vg u
        (relaxEdge dHat u (csrOutEdgeFin vg u idx hi).1 (csrOutEdgeFin vg u idx hi).2)
        (idx + 1) xs
    else dHat

noncomputable def relaxCsrOut (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n) :
    DistEstimate n :=
  relaxCsrOutAux vg u dHat 0 (g.outEdges u.val)

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
        nnrealToFloat ((relaxCsrOutAux vg u dHat csrIdx edges) x) := by
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
    simp only [relaxCsrOutAux, List.foldl_cons, dif_pos hi]
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

/-! ### Out-edge order bridge (outDeg ≤ 2, no self-loops) -/

private lemma csrTarget_ne_source (vg : ValidRustGraph n g) (u : Fin n) (i : Nat)
    (hi : i < (g.outEdges u.val).length) :
    u ≠ (csrOutEdgeFin vg u i hi).1 := by
  dsimp [csrOutEdgeFin]
  exact Fin.ne_of_val_ne (vg.hns u i hi).symm

private lemma relaxEdge_twice_same (dHat : DistEstimate n) (u v : Fin n) (a b : NNReal)
    (huv : u ≠ v) :
    relaxEdge (relaxEdge dHat u v a) u v b =
      Function.update dHat v (min (min (dHat v) (dHat u + a)) (dHat u + b)) := by
  funext x
  by_cases hx : x = v
  · subst hx
    simp [relaxEdge, Function.update, huv, min_assoc, min_comm]
  · simp [relaxEdge, Function.update, hx, huv]

private lemma relaxEdge_commute (dHat : DistEstimate n) (u v w : Fin n) (wv ww : NNReal)
    (huv : u ≠ v) (huw : u ≠ w) :
    relaxEdge (relaxEdge dHat u v wv) u w ww =
    relaxEdge (relaxEdge dHat u w ww) u v wv := by
  obtain rfl | hvw := eq_or_ne v w
  · rw [relaxEdge_twice_same dHat u v wv ww huv, relaxEdge_twice_same dHat u v ww wv huv]
    funext x
    by_cases hx : x = v
    · subst hx
      simp [Function.update]
      grind [min_comm, min_assoc, min_left_comm]
    · simp [Function.update, hx]
  · unfold relaxEdge
    funext x
    by_cases hx : x = v <;> by_cases hy : x = w
    · subst hy; exact absurd hx hvw.symm
    · subst hx; simp [Function.update, hvw, huw, huv]
    · subst hy; grind
    · rw [Function.update_comm hvw]
      simp [Function.update, hx, hy, hvw, huw, huv]

private lemma foldl_relaxEdge_pair (dHat : DistEstimate n) (u : Fin n) (p q : Fin n × NNReal)
    (hup : u ≠ p.1) (huq : u ≠ q.1) :
    [p, q].foldl (fun d e => relaxEdge d u e.1 e.2) dHat =
    [q, p].foldl (fun d e => relaxEdge d u e.1 e.2) dHat := by
  simp [List.foldl, relaxEdge_commute dHat u p.1 q.1 p.2 q.2 hup huq]

private lemma mem_outEdges_to_csr (vg : ValidRustGraph n g) (u : Fin n)
    {p : Fin n × NNReal} (hp : p ∈ vg.toGraph.outEdges u) :
    ∃ i hi, p = csrOutEdgeFin vg u i hi := by
  rcases p with ⟨v, w⟩
  rw [Sssp.mem_outEdges_iff, ValidRustGraph.toGraph, RustGraph.mem_edges_csrToGraph] at hp
  obtain ⟨i, hi, htgt, hw⟩ := hp
  refine ⟨i, hi, ?_⟩
  apply Prod.ext
  · exact (Fin.ext htgt).symm
  · exact hw

private lemma mem_outEdges_csrIndex (vg : ValidRustGraph n g) (u : Fin n) (h0 : 0 < (g.outEdges u.val).length)
    (h1 : 1 < (g.outEdges u.val).length) (hlen : (g.outEdges u.val).length = 2) {p : Fin n × NNReal}
    (hp : p ∈ vg.toGraph.outEdges u) :
    p = csrOutEdgeFin vg u 0 h0 ∨ p = csrOutEdgeFin vg u 1 h1 := by
  rcases mem_outEdges_to_csr (vg := vg) (u := u) hp with ⟨i, hi, hp'⟩
  have hi1 : i = 0 ∨ i = 1 := by
    have : i < 2 := by rw [← hlen]; exact hi
    omega
  rcases hi1 with hi0 | hi1
  · subst hi0
    left
    exact hp'
  · subst hi1
    right
    exact hp'

private lemma outEdges_toList_singleton (vg : ValidRustGraph n g) (u : Fin n) (e : Fin n × NNReal)
    (hcard : (vg.toGraph.outEdges u).card = 1) (hem : e ∈ vg.toGraph.outEdges u) :
    (vg.toGraph.outEdges u).toList = [e] := by
  rcases Multiset.card_eq_one.mp hcard with ⟨a, ha⟩
  have heq : e = a := by
    have hem' : e ∈ ({a} : Multiset (Fin n × NNReal)) := by rwa [← ha]
    exact Multiset.mem_singleton.mp hem'
  have hsingle : vg.toGraph.outEdges u = {e} := by
    rw [← heq] at ha
    exact ha
  rw [hsingle, Multiset.toList_singleton]

private lemma csr1_eq_csr0_of_toList_pair (vg : ValidRustGraph n g) (u : Fin n)
    (h0 : 0 < (g.outEdges u.val).length) (h1 : 1 < (g.outEdges u.val).length)
    (e0 : Fin n × NNReal) (hlist : (vg.toGraph.outEdges u).toList = [e0, e0]) :
    csrOutEdgeFin vg u 1 h1 = e0 := by
  have hem1 := RustGraph.outEdge_index_mem (g := g) (n := n) vg.hn (hwt := vg.hwt)
    (htgt := vg.htgt) (hdeg := vg.hdeg) (u := u) (i := 1) h1
  have : csrOutEdgeFin vg u 1 h1 ∈ [e0, e0] := by
    rw [← hlist, Multiset.mem_toList]
    exact hem1
  simp at this
  exact this

private lemma outEdges_toList_pair (vg : ValidRustGraph n g) (u : Fin n)
    (hlen : (g.outEdges u.val).length = 2) (hcard : (vg.toGraph.outEdges u).card = 2) :
    let h0 : 0 < (g.outEdges u.val).length := by omega
    let h1 : 1 < (g.outEdges u.val).length := by omega
    let e0 := csrOutEdgeFin vg u 0 h0
    let e1 := csrOutEdgeFin vg u 1 h1
    (vg.toGraph.outEdges u).toList = [e0, e1] ∨
      (vg.toGraph.outEdges u).toList = [e1, e0] := by
  let h0 : 0 < (g.outEdges u.val).length := by omega
  let h1 : 1 < (g.outEdges u.val).length := by omega
  let e0 := csrOutEdgeFin vg u 0 h0
  let e1 := csrOutEdgeFin vg u 1 h1
  have hlen' : (vg.toGraph.outEdges u).toList.length = 2 := by
    rw [Multiset.length_toList, hcard]
  rw [List.length_eq_two] at hlen'
  obtain ⟨p, q, hlist⟩ := hlen'
  have hp_mem : p ∈ (vg.toGraph.outEdges u).toList := by rw [hlist]; simp
  have hq_mem : q ∈ (vg.toGraph.outEdges u).toList := by rw [hlist]; simp
  have hp := mem_outEdges_csrIndex (vg := vg) (u := u) h0 h1 hlen (Multiset.mem_toList.mp hp_mem)
  have hq := mem_outEdges_csrIndex (vg := vg) (u := u) h0 h1 hlen (Multiset.mem_toList.mp hq_mem)
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · left
    have heq01 := csr1_eq_csr0_of_toList_pair vg u h0 h1 e0 (by rw [hlist, hp, hq])
    rw [hlist, hp, hq, heq01]
  · left
    rw [hlist, hp, hq]
  · right
    rw [hlist, hp, hq]
  · right
    have heq01 : e0 = e1 := by
      have hem0 := RustGraph.outEdge_index_mem (g := g) (n := n) vg.hn (hwt := vg.hwt)
        (htgt := vg.htgt) (hdeg := vg.hdeg) (u := u) (i := 0) h0
      have hlist' : (vg.toGraph.outEdges u).toList = [e1, e1] := by rw [hlist, hp, hq]
      have : e0 ∈ [e1, e1] := by rw [← hlist', Multiset.mem_toList]; exact hem0
      simpa using this
    rw [hlist, hp, hq, show csrOutEdgeFin vg u 0 h0 = e1 from heq01]

private lemma relaxOutEdges_nil (G : Graph n) (dHat : DistEstimate n) (u : Fin n)
    (hempty : G.outEdges u = 0) :
    relaxOutEdges G dHat u = dHat := by
  ext x
  dsimp [relaxOutEdges]
  rw [(Multiset.toList_eq_nil).2 hempty]
  simp [List.foldl_nil]

private lemma relaxCsrOut_nil (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n)
    (hlen : (g.outEdges u.val).length = 0) :
    relaxCsrOut vg u dHat = dHat := by
  dsimp [relaxCsrOut]
  rw [List.eq_nil_of_length_eq_zero hlen]
  simp [relaxCsrOutAux]

private lemma relaxOutEdges_singleton (G : Graph n) (dHat : DistEstimate n) (u : Fin n) (e : Fin n × NNReal)
    (hlist : (G.outEdges u).toList = [e]) :
    relaxOutEdges G dHat u = relaxEdge dHat u e.1 e.2 := by
  ext x
  dsimp [relaxOutEdges]
  rw [hlist]
  simp [List.foldl]

private lemma relaxCsrOut_singleton (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n)
    (h0 : 0 < (g.outEdges u.val).length) (hlen : (g.outEdges u.val).length = 1) :
    relaxCsrOut vg u dHat = relaxEdge dHat u (csrOutEdgeFin vg u 0 h0).1 (csrOutEdgeFin vg u 0 h0).2 := by
  have h_edges := List.eq_cons_of_length_one hlen
  ext x
  dsimp [relaxCsrOut]
  rw [h_edges]
  simp [relaxCsrOutAux, csrOutEdgeFin, List.foldl, dif_pos h0]

private lemma relaxOutEdges_pair (G : Graph n) (dHat : DistEstimate n) (u : Fin n) (e0 e1 : Fin n × NNReal)
    (hlist : (G.outEdges u).toList = [e0, e1]) :
    relaxOutEdges G dHat u = [e0, e1].foldl (fun d e => relaxEdge d u e.1 e.2) dHat := by
  ext x
  dsimp [relaxOutEdges]
  rw [hlist]
  simp [List.foldl]

private lemma relaxCsrOut_pair (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n)
    (h0 : 0 < (g.outEdges u.val).length) (h1 : 1 < (g.outEdges u.val).length)
    (hlen : (g.outEdges u.val).length = 2) :
    let e0 := csrOutEdgeFin vg u 0 h0
    let e1 := csrOutEdgeFin vg u 1 h1
    relaxCsrOut vg u dHat = [e0, e1].foldl (fun d e => relaxEdge d u e.1 e.2) dHat := by
  obtain ⟨p, q, h_edges⟩ := (List.length_eq_two).mp hlen
  ext x
  dsimp [relaxCsrOut]
  rw [h_edges]
  simp [relaxCsrOutAux, csrOutEdgeFin, dif_pos h0, dif_pos h1, List.foldl]

/-- CSR-index fold matches verified `relaxOutEdges` when out-degree ≤ 2 and there are no self-loops. -/
theorem relaxOutEdges_eq_relaxCsrOut (vg : ValidRustGraph n g) (u : Fin n) (dHat : DistEstimate n) :
    relaxOutEdges vg.toGraph dHat u = relaxCsrOut vg u dHat := by
  let G := vg.toGraph
  let edges := g.outEdges u.val
  have hle := vg.hdeg u
  match hlen : edges.length, hle with
  | 0, _ =>
    have hempty : G.outEdges u = 0 := (Multiset.card_eq_zero).mp (by
      rw [ValidRustGraph.outEdges_card (vg := vg) (u := u), hlen])
    rw [relaxOutEdges_nil G dHat u hempty, relaxCsrOut_nil vg u dHat hlen]
  | 1, _ =>
    have h0 : 0 < edges.length := by omega
    let e0 := csrOutEdgeFin vg u 0 h0
    have hcard : (G.outEdges u).card = 1 := by
      rw [ValidRustGraph.outEdges_card (vg := vg) (u := u), hlen]
    have hem0 := RustGraph.outEdge_index_mem (g := g) (n := n) vg.hn (hwt := vg.hwt)
      (htgt := vg.htgt) (hdeg := vg.hdeg) (u := u) (i := 0) h0
    have hlist := outEdges_toList_singleton (vg := vg) (u := u) e0 hcard hem0
    rw [relaxOutEdges_singleton G dHat u e0 hlist, relaxCsrOut_singleton vg u dHat h0 hlen]
  | 2, _ =>
    have h0 : 0 < edges.length := by omega
    have h1 : 1 < edges.length := by omega
    let e0 := csrOutEdgeFin vg u 0 h0
    let e1 := csrOutEdgeFin vg u 1 h1
    have hcard : (G.outEdges u).card = 2 := by
      rw [ValidRustGraph.outEdges_card (vg := vg) (u := u), hlen]
    have hpair := outEdges_toList_pair (vg := vg) (u := u) hlen hcard
    have hcsr := relaxCsrOut_pair vg u dHat h0 h1 hlen
    rcases hpair with hlist | hlist
    · rw [hcsr, relaxOutEdges_pair G dHat u e0 e1 hlist]
    · rw [hcsr, relaxOutEdges_pair G dHat u e1 e0 hlist,
        foldl_relaxEdge_pair dHat u e1 e0 (csrTarget_ne_source vg u 1 h1)
          (csrTarget_ne_source vg u 0 h0)]
  | len + 3, _ => omega

theorem floatRelaxOut_aligned (vg : ValidRustGraph n g) (dHat : DistEstimate n) (dist : List Float)
    (u : Fin n) (hlen : dist.length = n) (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ x : Fin n,
      (floatRelaxOut g dist u.val)[x.val]! = nnrealToFloat (relaxOutEdges vg.toGraph dHat u x) := by
  intro x
  rw [floatRelaxOut_relaxCsrOut_aligned (vg := vg) u dHat dist hlen halign x,
    relaxOutEdges_eq_relaxCsrOut (vg := vg) (u := u) (dHat := dHat)]

/-! ### All-vertex round alignment -/

private lemma floatRelaxAll_eq_foldl_finRange (hgn : g.n = n) (dist : List Float) :
    floatRelaxAll g dist =
      (List.finRange n).foldl (fun d u => floatRelaxOut g d u.val) dist := by
  dsimp [floatRelaxAll]
  rw [hgn, ← List.map_coe_finRange_eq_range]
  induction List.finRange n generalizing dist with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, List.map_cons]
    exact ih (floatRelaxOut g dist u.val)

private theorem foldl_floatRelaxAll_finRange_aligned (vg : ValidRustGraph n g) (dHat : DistEstimate n)
    (dist : List Float) (us : List (Fin n)) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) (v : Fin n) :
    (us.foldl (fun d u => floatRelaxOut g d u.val) dist)[v.val]! =
      nnrealToFloat (us.foldl (fun d u => relaxOutEdges vg.toGraph d u) dHat v) := by
  suffices h : ∀ (us' : List (Fin n)) (dist' : List Float) (dHat' : DistEstimate n),
      dist'.length = n →
      (∀ x : Fin n, dist'[x.val]! = nnrealToFloat (dHat' x)) →
      ∀ v' : Fin n,
        (us'.foldl (fun d u => floatRelaxOut g d u.val) dist')[v'.val]! =
          nnrealToFloat (us'.foldl (fun d u => relaxOutEdges vg.toGraph d u) dHat' v') by
    exact h us dist dHat hlen halign v
  intro us' dist' dHat' hlen' halign' v'
  revert dist' dHat' hlen' halign' v'
  induction us' with
  | nil =>
    intro dist' dHat' hlen' halign' v'
    simp only [List.foldl_nil]
    exact halign' v'
  | cons u us ih =>
    intro dist' dHat' hlen' halign' v'
    simp only [List.foldl_cons]
    have hlen'' : (floatRelaxOut g dist' u.val).length = n :=
      (floatRelaxOut_length dist' u.val (hlen'.trans vg.hn.symm)).trans vg.hn
    have halign'' : ∀ x : Fin n,
        (floatRelaxOut g dist' u.val)[x.val]! =
          nnrealToFloat (relaxOutEdges vg.toGraph dHat' u x) :=
      fun x => floatRelaxOut_aligned (vg := vg) dHat' dist' u hlen' halign' x
    exact ih (floatRelaxOut g dist' u.val) (relaxOutEdges vg.toGraph dHat' u) hlen'' halign'' v'

theorem foldl_range_floatRelaxAll_aligned (vg : ValidRustGraph n g) (dHat : DistEstimate n)
    (dist : List Float) (hlen : dist.length = n)
    (halign : ∀ x : Fin n, dist[x.val]! = nnrealToFloat (dHat x)) :
    ∀ v : Fin n,
      (floatRelaxAll g dist)[v.val]! = nnrealToFloat (relaxAll vg.toGraph dHat v) := by
  intro v
  rw [floatRelaxAll_eq_foldl_finRange vg.hn dist]
  dsimp [relaxAll]
  exact foldl_floatRelaxAll_finRange_aligned vg dHat dist (List.finRange n) hlen halign v

theorem floatRelaxAll_simInv (vg : ValidRustGraph n g) (s : Fin n) (dist : List Float)
    (dHat : DistEstimate n) (h : SimInv vg s dist dHat) :
    SimInv vg s (floatRelaxAll g dist) (relaxAll vg.toGraph dHat) where
  len := floatRelaxAll_length dist (by rw [vg.hn]; exact h.len) vg.hn
  aligned := fun v => foldl_range_floatRelaxAll_aligned vg dHat dist h.len h.aligned v
  sound := relaxAll_sound (G := vg.toGraph) (s := s) dHat h.sound

end Refine
end Sssp
