/-
  Sssp.Refine.GraphBridge

  Phase 3b: general bridge from CSR `RustGraph` to verified `Graph n`.
  Integer-weighted graphs (`floatWeight w`) are the first supported class.
-/

import Mathlib
import Sssp.Refine.Dijkstra

namespace Sssp
namespace Refine

open Sssp

/-- CSR edge weights are natural numbers rendered as `Float`. -/
structure HasNatWeights (g : RustGraph) where
  edgeWeight : ∀ (u i : Nat), i < (g.outEdges u).length → Nat
  edgeWeight_spec :
    ∀ (u i : Nat) (hi : i < (g.outEdges u).length),
      floatWeight (edgeWeight u i hi) = ((g.outEdges u)[i]'hi).2

/-- Every CSR out-edge weight is the `Float` image of a natural number (legacy view). -/
structure HasNatWeights' (g : RustGraph) where
  weight : ∀ (u : Nat) (p : Nat × Float), p ∈ g.outEdges u → Nat
  weight_spec :
    ∀ (u : Nat) (p : Nat × Float) (hp : p ∈ g.outEdges u),
      floatWeight (weight u p hp) = p.2

def HasNatWeights'.toHasNatWeights {g : RustGraph} (h : HasNatWeights' g) :
    HasNatWeights g where
  edgeWeight u i hi := h.weight u ((g.outEdges u)[i]'hi) (List.getElem_mem hi)
  edgeWeight_spec u i hi := h.weight_spec u ((g.outEdges u)[i]'hi) (List.getElem_mem hi)

def edgeListGraph (n : Nat) (es : List (Nat × Nat × Nat)) : RustGraph :=
  RustGraph.fromEdgeList n (es.map fun e => (e.1, e.2.1, floatWeight e.2.2))

def edgeOutWeight (n : Nat) (es : List (Nat × Nat × Nat)) (u i : Nat)
    (hi : i < ((edgeListGraph n es).outEdges u).length) : Float :=
  let edges := (edgeListGraph n es).outEdges u
  (edges[i]'hi).2

/-- CSR out-edge indices are bounded by the right endpoint of their head range. -/
private theorem outEdgeIndices_getElem_lt_head_next (g : RustGraph) (u i : Nat)
    (hi : i < (g.outEdgeIndices u).length) :
    (g.outEdgeIndices u)[i]'hi < g.head[u + 1]! := by
  by_cases hhead : u + 1 < g.head.length
  · simp [RustGraph.outEdgeIndices, hhead] at hi ⊢
    omega
  · simp [RustGraph.outEdgeIndices, hhead] at hi

/-- A one-hot sum over a no-duplicate natural list is the list count. -/
private theorem sum_map_beq_eq_count (a : Nat) :
    ∀ l : List Nat, ((l.map fun x => if a == x then 1 else 0).sum) = l.count a
  | [] => by simp
  | x :: xs => by
      simp only [List.map_cons, List.sum_cons]
      rw [sum_map_beq_eq_count a xs]
      by_cases h : a = x
      · subst a
        simp [Nat.add_comm]
      · simp [h, Ne.symm h]

/-- A one-hot source contribution is counted at most once over `range n`. -/
private theorem sum_map_beq_range_le_one (a n : Nat) :
    ((List.range n).map fun x => if a == x then 1 else 0).sum ≤ 1 := by
  rw [sum_map_beq_eq_count]
  exact (List.nodup_iff_count_le_one.mp List.nodup_range) a

/-- The sum of per-source edge counts over `range n` is bounded by the edge-list length. -/
private theorem counts_sum_le_edges_length (n : Nat) (edges : List (Nat × Nat × Float)) :
    ((List.range n).map fun u => (edges.filter fun e => e.1 == u).length).sum ≤
      edges.length := by
  induction edges with
  | nil =>
      simp
  | cons e es ih =>
      have hpoint : ∀ u,
          ((e :: es).filter fun e' => e'.1 == u).length =
            (if e.1 == u then 1 else 0) + (es.filter fun e' => e'.1 == u).length := by
        intro u
        by_cases h : e.1 == u
        · simp [h]
          omega
        · simp [h]
      calc
        ((List.range n).map fun u => ((e :: es).filter fun e' => e'.1 == u).length).sum
            = ((List.range n).map fun u => (if e.1 == u then 1 else 0)).sum +
                ((List.range n).map fun u => (es.filter fun e' => e'.1 == u).length).sum := by
              simp_rw [hpoint]
              simp [List.sum_map_add]
        _ ≤ 1 + es.length := Nat.add_le_add (sum_map_beq_range_le_one e.1 n) ih
        _ = (e :: es).length := by simp [Nat.add_comm]

/-- The CSR-head builder appends one entry for each count. -/
private theorem foldl_head_length (counts acc : List Nat) :
    (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) acc).length =
      acc.length + counts.length := by
  induction counts generalizing acc with
  | nil =>
      simp
  | cons c cs ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (acc ++ [acc.getLast! + c])

/-- Every generated head entry is bounded by the previous last entry plus remaining counts. -/
private theorem foldl_head_mem_le_last_add_sum (counts acc : List Nat)
    (hacc_le : ∀ x ∈ acc, x ≤ acc.getLast!) {x : Nat}
    (hx : x ∈ counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) acc) :
    x ≤ acc.getLast! + counts.sum := by
  induction counts generalizing acc with
  | nil =>
      simpa using hacc_le x hx
  | cons c cs ih =>
      let acc' := acc ++ [acc.getLast! + c]
      have hacc' : acc' ≠ [] := by simp [acc']
      have hlast : acc'.getLast! = acc.getLast! + c := by
        simp [acc']
      have hacc'_le : ∀ y ∈ acc', y ≤ acc'.getLast! := by
        intro y hy
        rw [hlast]
        simp [acc'] at hy
        rcases hy with hy | hy
        · exact Nat.le_trans (hacc_le y hy) (Nat.le_add_right _ _)
        · simp [hy]
      have hx' : x ∈ cs.foldl (fun acc c => acc ++ [acc.getLast! + c]) acc' := by
        simpa [acc'] using hx
      have hle := ih acc' hacc'_le hx'
      rw [hlast] at hle
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

/-- Any indexed head entry generated from counts is bounded by the count sum. -/
private theorem foldl_head_getElem_le_sum (counts : List Nat) (idx : Nat)
    (hidx : idx < (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0]).length) :
    (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0])[idx]'hidx ≤ counts.sum := by
  have hmem :
      (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0])[idx]'hidx ∈
        counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0] :=
    List.getElem_mem hidx
  simpa using
    (foldl_head_mem_le_last_add_sum counts [0]
      (by intro x hx; simpa using hx) hmem)

/-- Any total head lookup generated from counts is bounded by the count sum. -/
private theorem foldl_head_getElem!_le_sum (counts : List Nat) (idx : Nat) :
    (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0])[idx]! ≤ counts.sum := by
  by_cases hidx : idx < (counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0]).length
  · let head := counts.foldl (fun acc c => acc ++ [acc.getLast! + c]) [0]
    have hidx' : idx < head.length := by simpa [head] using hidx
    have hget : head[idx]! = head[idx]'hidx' := getElem!_pos head idx hidx'
    change head[idx]! ≤ counts.sum
    rw [hget]
    simpa [head] using foldl_head_getElem_le_sum counts idx hidx
  · rw [getElem!_neg]
    · simp
    · exact hidx

/-- Every CSR head entry built by `fromEdgeList` is bounded by `edgeW.length`. -/
private theorem fromEdgeList_head_getElem_le_edgeW_length
    (n : Nat) (edges : List (Nat × Nat × Float)) (idx : Nat) :
    (RustGraph.fromEdgeList n edges).head[idx]! ≤
      (RustGraph.fromEdgeList n edges).edgeW.length := by
  unfold RustGraph.fromEdgeList
  exact le_trans (foldl_head_getElem!_le_sum
    ((List.range n).map fun u => (edges.filter fun e => e.1 == u).length) idx)
    (by simpa using counts_sum_le_edges_length n edges)

/-- Every CSR head entry built from nat triples is bounded by `edgeW.length`. -/
private theorem edgeListGraph_head_getElem_le_edgeW_length
    (n : Nat) (es : List (Nat × Nat × Nat)) (idx : Nat) :
    (edgeListGraph n es).head[idx]! ≤ (edgeListGraph n es).edgeW.length := by
  unfold edgeListGraph
  exact fromEdgeList_head_getElem_le_edgeW_length n
    (es.map fun e => (e.1, e.2.1, floatWeight e.2.2)) idx

/-- Every stored weight in a graph built from nat triples has a nat preimage. -/
private theorem edgeListGraph_edgeW_mem_preimage (n : Nat) (es : List (Nat × Nat × Nat))
    {w : Float} (hw : w ∈ (edgeListGraph n es).edgeW) :
    ∃ k : Nat, floatWeight k = w := by
  unfold edgeListGraph RustGraph.fromEdgeList at hw
  simp only [List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  obtain ⟨e, he, rfl⟩ := hp
  have he' : e ∈ es.map fun e => (e.1, e.2.1, floatWeight e.2.2) := by
    exact (List.Perm.mem_iff (List.mergeSort_perm _ _)).mp he
  simp only [List.mem_map] at he'
  obtain ⟨e', _, heq⟩ := he'
  subst e
  exact ⟨e'.2.2, rfl⟩

/-- Every in-bounds `edgeW` lookup in a nat-edge-list graph has a nat preimage. -/
private theorem edgeListGraph_edgeW_getElem_preimage (n : Nat) (es : List (Nat × Nat × Nat))
    (idx : Nat) (hidx : idx < (edgeListGraph n es).edgeW.length) :
    ∃ k : Nat, floatWeight k = (edgeListGraph n es).edgeW[idx]! := by
  have hmem : (edgeListGraph n es).edgeW[idx]! ∈ (edgeListGraph n es).edgeW := by
    simp [hidx]
  exact edgeListGraph_edgeW_mem_preimage n es hmem

/-- Every CSR slot built from a nat edge list stores a `floatWeight` image. -/
theorem outEdge_floatWeight_preimage (n : Nat) (es : List (Nat × Nat × Nat)) (u i : Nat)
    (hi : i < ((edgeListGraph n es).outEdges u).length) :
    ∃ k : Nat, floatWeight k = edgeOutWeight n es u i hi := by
  unfold edgeOutWeight RustGraph.outEdges
  simp only [List.getElem_map]
  have hidx :
      ((edgeListGraph n es).outEdgeIndices u)[i]'(by simpa [RustGraph.outEdges] using hi) <
        (edgeListGraph n es).edgeW.length :=
    Nat.lt_of_lt_of_le
      (outEdgeIndices_getElem_lt_head_next (edgeListGraph n es) u i
        (by simpa [RustGraph.outEdges] using hi))
      (edgeListGraph_head_getElem_le_edgeW_length n es (u + 1))
  exact edgeListGraph_edgeW_getElem_preimage n es
    (((edgeListGraph n es).outEdgeIndices u)[i]'(by simpa [RustGraph.outEdges] using hi)) hidx

/-- Construct `HasNatWeights` for graphs built from `(u, v, w)` nat triples. -/
noncomputable def hasNatWeights_fromEdgeList (n : Nat) (es : List (Nat × Nat × Nat)) :
    HasNatWeights (edgeListGraph n es) where
  edgeWeight u i hi := Classical.choose (outEdge_floatWeight_preimage n es u i hi)
  edgeWeight_spec u i hi := Classical.choose_spec (outEdge_floatWeight_preimage n es u i hi)

/-- Out-degree (with multiplicity) at each vertex is at most 2. -/
def outDegNatLe (g : RustGraph) (n : Nat) : Prop :=
  ∀ u : Fin n, (g.outEdges u.val).length ≤ 2

/-- Every out-edge target is a valid vertex index. -/
def targetsIn (g : RustGraph) (n : Nat) : Prop :=
  ∀ (u : Fin n) (p : Nat × Float), p ∈ g.outEdges u.val → p.1 < n

namespace RustGraph

set_option maxHeartbeats 800000

/-- Extract `Graph n` edge weights at `(u,v)` from CSR out-edges. -/
def weightsToTarget (g : RustGraph) (hwt : HasNatWeights g) (u tgt : Nat) : List NNReal :=
  (List.range (g.outEdges u).length).flatMap fun i =>
    if h : i < (g.outEdges u).length then
      if ((g.outEdges u)[i]'h).1 == tgt then
        [nnrealWeight (hwt.edgeWeight u i h)]
      else []
    else []

private lemma weightsToTarget_length_self (g : RustGraph) (hwt : HasNatWeights g)
    (u t : Nat) (hlen : (g.outEdges u).length = 1) (h0 : 0 < (g.outEdges u).length)
    (htgt0 : ((g.outEdges u)[0]'h0).1 = t) :
    (weightsToTarget g hwt u t).length = 1 := by
  simp only [weightsToTarget, hlen, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil]
  grind

private lemma weightsToTarget_length_ne (g : RustGraph) (hwt : HasNatWeights g)
    (u b t : Nat) (hlen : (g.outEdges u).length = 1) (h0 : 0 < (g.outEdges u).length)
    (htgt0 : ((g.outEdges u)[0]'h0).1 = t) (hb' : b ≠ t) :
    (weightsToTarget g hwt u b).length = 0 := by
  simp only [weightsToTarget, hlen, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil]
  grind

private lemma weightsToTarget_length_two_same (g : RustGraph) (hwt : HasNatWeights g)
    (u t : Nat) (hlen : (g.outEdges u).length = 2) (h0 : 0 < (g.outEdges u).length)
    (h1 : 1 < (g.outEdges u).length) (htgt0 : ((g.outEdges u)[0]'h0).1 = t)
    (htgt1 : ((g.outEdges u)[1]'h1).1 = t) :
    (weightsToTarget g hwt u t).length = 2 := by
  simp only [weightsToTarget, hlen, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil]
  grind

private lemma weightsToTarget_length_two_diff (g : RustGraph) (hwt : HasNatWeights g)
    (u b t0 t1 : Nat) (hlen : (g.outEdges u).length = 2) (h0 : 0 < (g.outEdges u).length)
    (h1 : 1 < (g.outEdges u).length) (htgt0 : ((g.outEdges u)[0]'h0).1 = t0)
    (htgt1 : ((g.outEdges u)[1]'h1).1 = t1) (hb0 : b ≠ t0) (hb1 : b ≠ t1) :
    (weightsToTarget g hwt u b).length = 0 := by
  simp only [weightsToTarget, hlen, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil]
  grind

private lemma weightsToTarget_length_at0 (g : RustGraph) (hwt : HasNatWeights g)
    (u t tOther : Nat) (hlen : (g.outEdges u).length = 2) (h0 : 0 < (g.outEdges u).length)
    (h1 : 1 < (g.outEdges u).length) (htgt0 : ((g.outEdges u)[0]'h0).1 = t)
    (htgt1 : ((g.outEdges u)[1]'h1).1 = tOther) (hne : t ≠ tOther) :
    (weightsToTarget g hwt u t).length = 1 := by
  have hdef :
      weightsToTarget g hwt u t =
        (if ((g.outEdges u)[0]'h0).1 == t then [nnrealWeight (hwt.edgeWeight u 0 h0)] else []) ++
          (if ((g.outEdges u)[1]'h1).1 == t then [nnrealWeight (hwt.edgeWeight u 1 h1)] else []) := by
    simp [weightsToTarget, hlen, List.range_succ, List.flatMap_cons, List.flatMap_nil, if_pos h0,
      if_pos h1]
  rw [hdef]
  simp [beq_iff_eq, htgt0, htgt1, Ne.symm hne, List.length_append, List.length_cons,
    List.length_nil]

private lemma weightsToTarget_length_at1 (g : RustGraph) (hwt : HasNatWeights g)
    (u t tOther : Nat) (hlen : (g.outEdges u).length = 2) (h0 : 0 < (g.outEdges u).length)
    (h1 : 1 < (g.outEdges u).length) (htgt0 : ((g.outEdges u)[0]'h0).1 = tOther)
    (htgt1 : ((g.outEdges u)[1]'h1).1 = t) (hne : t ≠ tOther) :
    (weightsToTarget g hwt u t).length = 1 := by
  have hdef :
      weightsToTarget g hwt u t =
        (if ((g.outEdges u)[0]'h0).1 == t then [nnrealWeight (hwt.edgeWeight u 0 h0)] else []) ++
          (if ((g.outEdges u)[1]'h1).1 == t then [nnrealWeight (hwt.edgeWeight u 1 h1)] else []) := by
    simp [weightsToTarget, hlen, List.range_succ, List.flatMap_cons, List.flatMap_nil, if_pos h0,
      if_pos h1]
  rw [hdef]
  simp [beq_iff_eq, htgt0, htgt1, Ne.symm hne, List.length_append, List.length_cons,
    List.length_nil]

private lemma sum_weightsToTarget_zero (g : RustGraph) (hwt : HasNatWeights g) (n : Nat)
    (u : Fin n) (hlen : (g.outEdges u.val).length = 0) :
    ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = 0 := by
  simp [weightsToTarget, hlen]

private lemma sum_weightsToTarget_one (g : RustGraph) (hwt : HasNatWeights g) (n : Nat)
    (htgt : targetsIn g n) (u : Fin n) (hlen : (g.outEdges u.val).length = 1) :
    ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = 1 := by
  have h0 : 0 < (g.outEdges u.val).length := by omega
  let t := ((g.outEdges u.val)[0]'h0).1
  let a : Fin n := ⟨t, htgt u ((g.outEdges u.val)[0]'h0) (List.getElem_mem h0)⟩
  have htgt0 : ((g.outEdges u.val)[0]'h0).1 = t := rfl
  rw [Finset.sum_eq_single a]
  · exact weightsToTarget_length_self g hwt u.val t hlen h0 htgt0
  · intro b _ hb
    have hb' : b.val ≠ t := (Fin.ext_iff.not).mp hb
    exact weightsToTarget_length_ne g hwt u.val b.val t hlen h0 htgt0 hb'
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma sum_weightsToTarget_two (g : RustGraph) (hwt : HasNatWeights g) (n : Nat)
    (htgt : targetsIn g n) (u : Fin n) (hlen : (g.outEdges u.val).length = 2) :
    ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = 2 := by
  have h0 : 0 < (g.outEdges u.val).length := by omega
  have h1 : 1 < (g.outEdges u.val).length := by omega
  let t0 := ((g.outEdges u.val)[0]'h0).1
  let t1 := ((g.outEdges u.val)[1]'h1).1
  let a : Fin n := ⟨t0, htgt u ((g.outEdges u.val)[0]'h0) (List.getElem_mem h0)⟩
  let b : Fin n := ⟨t1, htgt u ((g.outEdges u.val)[1]'h1) (List.getElem_mem h1)⟩
  have htgt0 : ((g.outEdges u.val)[0]'h0).1 = t0 := rfl
  have htgt1 : ((g.outEdges u.val)[1]'h1).1 = t1 := rfl
  by_cases h : t0 = t1
  · have htgt1' : ((g.outEdges u.val)[1]'h1).1 = t0 := htgt1.trans h.symm
    rw [Finset.sum_eq_single a]
    · exact weightsToTarget_length_two_same g hwt u.val t0 hlen h0 h1 htgt0 htgt1'
    · intro c _ hc
      have hc0 : c.val ≠ t0 := (Fin.ext_iff.not).mp hc
      have hc1 : c.val ≠ t1 := by
        intro heq
        exact hc0 (h ▸ heq)
      exact weightsToTarget_length_two_diff g hwt u.val c.val t0 t1 hlen h0 h1 htgt0 htgt1 hc0 hc1
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · have hne : a ≠ b := Fin.ne_of_val_ne h
    have hf0 := weightsToTarget_length_at0 g hwt u.val t0 t1 hlen h0 h1 htgt0 htgt1 h
    have hf1 := weightsToTarget_length_at1 g hwt u.val t1 t0 hlen h0 h1 htgt0 htgt1 (Ne.symm h)
    have hrest : ∀ c : Fin n, c ≠ a → c ≠ b →
        (weightsToTarget g hwt u.val c.val).length = 0 := by
      intro c hca hcb
      exact weightsToTarget_length_two_diff g hwt u.val c.val t0 t1 hlen h0 h1 htgt0 htgt1
        (fun heq => hca (Fin.ext heq)) (fun heq => hcb (Fin.ext heq))
    have hsum_erase :
        ∑ v ∈ Finset.univ.erase a, (weightsToTarget g hwt u.val v.val).length = 1 := by
      rw [Finset.sum_eq_single b]
      · show (weightsToTarget g hwt u.val b.val).length = 1
        simpa [b] using hf1
      · intro c hcMem hcNe
        have hca : c ≠ a := (Finset.mem_erase.mp hcMem).1
        exact hrest c hca hcNe
      · intro hb'
        exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ b⟩) hb'
    have hmain :
        ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length =
          (weightsToTarget g hwt u.val a.val).length +
            ∑ v ∈ Finset.univ.erase a, (weightsToTarget g hwt u.val v.val).length := by
      rw [← Finset.sum_erase_add (s := Finset.univ)
        (f := fun v => (weightsToTarget g hwt u.val v.val).length) (a := a)
        (Finset.mem_univ a), add_comm]
    rw [hmain, show (weightsToTarget g hwt u.val a.val).length = 1 from by simpa [a] using hf0,
      hsum_erase]

/-- Partitioning CSR out-edges by target preserves total out-degree. -/
theorem sum_weightsToTarget_length (g : RustGraph) (n : Nat) (hwt : HasNatWeights g)
    (htgt : targetsIn g n) (hdeg : outDegNatLe g n) (u : Fin n) :
    ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length = (g.outEdges u.val).length := by
  have hle := hdeg u
  match hlen : (g.outEdges u.val).length, hle with
  | 0, _ => exact sum_weightsToTarget_zero g hwt n u hlen
  | 1, _ => exact sum_weightsToTarget_one g hwt n htgt u hlen
  | 2, _ => exact sum_weightsToTarget_two g hwt n htgt u hlen
  | len + 3, _ => omega

/-- Build a verified `Graph n` from a CSR graph with natural `Float` weights. -/
noncomputable def csrToGraph (g : RustGraph) (n : Nat) (hn : g.n = n) (hwt : HasNatWeights g)
    (htgt : targetsIn g n) (hdeg : outDegNatLe g n) : Graph n where
  edges := fun u v => Multiset.ofList (weightsToTarget g hwt u.val v.val)
  outDeg_le := by
    intro u
    calc
      ∑ v : Fin n, (Multiset.ofList (weightsToTarget g hwt u.val v.val)).card
          = ∑ v : Fin n, (weightsToTarget g hwt u.val v.val).length := by
            refine Finset.sum_congr rfl fun v _ => ?_
            exact (Multiset.coe_card _).symm
      _ = (g.outEdges u.val).length := sum_weightsToTarget_length g n hwt htgt hdeg u
      _ ≤ 2 := hdeg u

theorem mem_edges_csrToGraph {g : RustGraph} {n : Nat} (hn : g.n = n) {hwt : HasNatWeights g}
    {htgt : targetsIn g n} {hdeg : outDegNatLe g n} {u v : Fin n} {w : NNReal} :
    w ∈ (csrToGraph g n hn hwt htgt hdeg).edges u v ↔
      ∃ (i : Nat) (hi : i < (g.outEdges u.val).length),
        ((g.outEdges u.val)[i]'hi).1 = v.val ∧
          w = nnrealWeight (hwt.edgeWeight u.val i hi) := by
  simp only [csrToGraph, Multiset.mem_coe]
  constructor
  · intro hw
    dsimp [weightsToTarget] at hw
    rw [List.mem_flatMap] at hw
    obtain ⟨i, hi, hw'⟩ := hw
    rw [List.mem_range] at hi
    by_cases htgt' : ((g.outEdges u.val)[i]'hi).1 = v.val
    · simp [htgt', hi] at hw'
      exact ⟨i, hi, htgt', hw'⟩
    · simp [htgt', hi] at hw'
  · intro ⟨i, hi, htgt', hw⟩
    dsimp [weightsToTarget]
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simp [hi, htgt', hw]

theorem csr_outEdge_mem {g : RustGraph} {n : Nat} (hn : g.n = n) {hwt : HasNatWeights g}
    {htgt : targetsIn g n} {hdeg : outDegNatLe g n} {u v : Fin n} {w : Nat} {i : Nat}
    (hi : i < (g.outEdges u.val).length) (htgt' : ((g.outEdges u.val)[i]'hi).1 = v.val)
    (hw : w = hwt.edgeWeight u.val i hi) :
    nnrealWeight w ∈ (csrToGraph g n hn hwt htgt hdeg).edges u v := by
  rw [mem_edges_csrToGraph (g := g) (n := n) hn (hwt := hwt) (htgt := htgt) (hdeg := hdeg)]
  exact ⟨i, hi, htgt', by simpa [nnrealWeight, hw]⟩

theorem csr_outEdge_float {g : RustGraph} {n : Nat} (_hn : g.n = n) {hwt : HasNatWeights g}
    {u : Fin n} {i : Nat} (hi : i < (g.outEdges u.val).length) :
    floatWeight (hwt.edgeWeight u.val i hi) = ((g.outEdges u.val)[i]'hi).2 :=
  hwt.edgeWeight_spec u.val i hi

/-- CSR out-edge list membership ↔ verified `Graph.outEdges` membership. -/
theorem mem_outEdges_csrToGraph {g : RustGraph} {n : Nat} (hn : g.n = n) {hwt : HasNatWeights g}
    {htgt : targetsIn g n} {hdeg : outDegNatLe g n} {u v : Fin n} {w : Nat} {i : Nat}
    (hi : i < (g.outEdges u.val).length) (htgt' : ((g.outEdges u.val)[i]'hi).1 = v.val)
    (hw : w = hwt.edgeWeight u.val i hi) :
    (v, nnrealWeight w) ∈ (csrToGraph g n hn hwt htgt hdeg).outEdges u := by
  rw [Sssp.mem_outEdges_iff (G := csrToGraph g n hn hwt htgt hdeg) (u := u)]
  exact csr_outEdge_mem (g := g) (n := n) hn (hwt := hwt) (htgt := htgt) (hdeg := hdeg)
    hi htgt' hw

/-- Every CSR out-edge index yields a verified-graph out-edge. -/
theorem outEdge_index_mem {g : RustGraph} {n : Nat} (hn : g.n = n) {hwt : HasNatWeights g}
    {htgt : targetsIn g n} {hdeg : outDegNatLe g n} {u : Fin n} {i : Nat}
    (hi : i < (g.outEdges u.val).length) :
    let tgt := ((g.outEdges u.val)[i]'hi).1
    let w := hwt.edgeWeight u.val i hi
    (⟨tgt, htgt u ((g.outEdges u.val)[i]'hi) (List.getElem_mem hi)⟩, nnrealWeight w) ∈
      (csrToGraph g n hn hwt htgt hdeg).outEdges u := by
  dsimp
  exact mem_outEdges_csrToGraph (g := g) (n := n) hn (hwt := hwt) (htgt := htgt) (hdeg := hdeg)
    hi rfl rfl

end RustGraph

/-- Bundled validity predicate for Phase 3b refinement proofs. -/
structure ValidRustGraph (n : Nat) (g : RustGraph) where
  hn : g.n = n
  hwt : HasNatWeights g
  htgt : targetsIn g n
  hdeg : outDegNatLe g n

namespace ValidRustGraph

variable {n : Nat} {g : RustGraph}

noncomputable def toGraph (vg : ValidRustGraph n g) : Graph n :=
  RustGraph.csrToGraph g n vg.hn vg.hwt vg.htgt vg.hdeg

end ValidRustGraph

end Refine
end Sssp
