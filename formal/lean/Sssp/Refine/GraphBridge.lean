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

/-- Every CSR slot built from a nat edge list stores a `floatWeight` image. -/
theorem outEdge_floatWeight_preimage (n : Nat) (es : List (Nat × Nat × Nat)) (u i : Nat)
    (hi : i < ((edgeListGraph n es).outEdges u).length) :
    ∃ w : Nat, floatWeight w = edgeOutWeight n es u i hi := by
  let g := edgeListGraph n es
  have hu := RustGraph.outEdges_nonempty_head (g := g) (u := u) (i := i) hi
  let idx := g.head[u]! + i
  have hidx := RustGraph.fromEdgeList_csr_index_lt n (natEdgeMap es) u i hu hi
  have hidx' : idx < g.edgeW.length := by
    dsimp [idx, g, edgeListGraph, natEdgeMap] at hidx ⊢
    exact hidx
  obtain ⟨w, hw⟩ := fromEdgeList_edgeW_floatWeight n es idx (by
    dsimp [idx, edgeListGraph, g, natEdgeMap]
    exact hidx)
  have heq : edgeOutWeight n es u i hi = g.edgeW[idx]! := by
    dsimp [edgeOutWeight, idx]
    rw [RustGraph.outEdges_getElem_snd (g := g) u i hu hi hidx', getElem!_pos g.edgeW idx hidx']
  have hcast : (RustGraph.fromEdgeList n (natEdgeMap es)).edgeW[idx] = g.edgeW[idx]! := by
    dsimp [edgeListGraph, g, natEdgeMap, idx]
    exact (getElem!_pos g.edgeW idx hidx').symm
  exact ⟨w, hw.trans (hcast.trans heq.symm)⟩

/-- Construct `HasNatWeights` for graphs built from `(u, v, w)` nat triples. -/
noncomputable def hasNatWeights_fromEdgeList (n : Nat) (es : List (Nat × Nat × Nat)) :
    HasNatWeights (edgeListGraph n es) where
  edgeWeight u i hi := Classical.choose (outEdge_floatWeight_preimage n es u i hi)
  edgeWeight_spec u i hi := Classical.choose_spec (outEdge_floatWeight_preimage n es u i hi)

/-- Out-degree (with multiplicity) at each vertex is at most 2. -/
def outDegNatLe (g : RustGraph) (n : Nat) : Prop :=
  ∀ u : Fin n, (g.outEdges u.val).length ≤ 2

/-- No out-edge returns to its source (matches benchmark edge lists). -/
def noSelfLoops (g : RustGraph) (n : Nat) : Prop :=
  ∀ (u : Fin n) (i : Nat) (hi : i < (g.outEdges u.val).length),
    ((g.outEdges u.val)[i]'hi).1 ≠ u.val

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
  hns : noSelfLoops g n

namespace ValidRustGraph

variable {n : Nat} {g : RustGraph}

noncomputable def toGraph (vg : ValidRustGraph n g) : Graph n :=
  RustGraph.csrToGraph g n vg.hn vg.hwt vg.htgt vg.hdeg

/-- Verified out-edge count matches CSR out-degree. -/
theorem outEdges_card (vg : ValidRustGraph n g) (u : Fin n) :
    (vg.toGraph.outEdges u).card = (g.outEdges u.val).length := by
  dsimp [toGraph, RustGraph.csrToGraph, Graph.outEdges]
  rw [Multiset.card_bind]
  trans ∑ v : Fin n, (RustGraph.weightsToTarget g vg.hwt u.val v.val).length
  · refine Finset.sum_congr rfl fun v _ => ?_
    change ((Multiset.ofList (RustGraph.weightsToTarget g vg.hwt u.val v.val)).map (Prod.mk v)).card =
        (RustGraph.weightsToTarget g vg.hwt u.val v.val).length
    rw [Multiset.card_map, Multiset.coe_card]
  exact RustGraph.sum_weightsToTarget_length g n vg.hwt vg.htgt vg.hdeg u

end ValidRustGraph

end Refine
end Sssp
