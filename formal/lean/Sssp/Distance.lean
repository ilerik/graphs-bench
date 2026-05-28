/-
  Sssp.Distance

  True distance `d(v)`, the upper-bound estimate `dHat[v]`, completeness, and
  the `T(S) / T(S^*)` notations of §3.5 of the paper. These are the central
  vocabulary used in every BMSSP correctness statement.

  Mirrors §2 ("Labels Used in the Algorithm") of
  `formal/paper/source/preliminary.tex` and the `d` field of `Context` in
  `src/bmssp.rs:42`.

  Naming convention: in Lean source we write `dHat` for the paper's `d̂`
  to avoid combining-mark headaches. Documentation still uses `d̂`.
-/

import Sssp.Graph
import Sssp.Path
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.WithBot
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin

namespace Sssp

open Classical

noncomputable section

/-- True distance from `s` to `v`: the infimum length of any walk `s ⇝ v`,
    or `+∞` if no such walk exists. -/
noncomputable def trueDist {n : ℕ} (G : Graph n) (s v : Fin n) :
    WithTop NNReal :=
  ⨅ (w : Walk G s v), (w.length : WithTop NNReal)

/-- The empty walk shows distance from `s` to itself is zero. -/
theorem trueDist_self {n : ℕ} (G : Graph n) (s : Fin n) : trueDist G s s = 0 := by
  let w : Walk G s s := ⟨[], WalkValid.nil rfl⟩
  have hlen : (w.length : WithTop NNReal) = 0 := by
    simp [w, Walk.length]
  apply le_antisymm
  · calc
      trueDist G s s ≤ (w.length : WithTop NNReal) := iInf_le _ w
      _ = 0 := hlen
  · refine le_iInf fun w' => ?_
    have h : (0 : NNReal) ≤ w'.length := zero_le _
    exact WithTop.coe_le_coe.mpr h

/-- Any walk provides an upper bound on the true distance. -/
theorem trueDist_le_walk_length {n : ℕ} (G : Graph n) (s v : Fin n) (w : Walk G s v) :
    trueDist G s v ≤ (w.length : WithTop NNReal) :=
  iInf_le _ w

/-- A single edge gives an upper bound on distance. -/
theorem trueDist_edge {n : ℕ} (G : Graph n) (u v : Fin n) (w : NNReal)
    (h : w ∈ G.edges u v) : trueDist G u v ≤ (w : WithTop NNReal) := by
  let walk : Walk G u v := ⟨[(v, w)], WalkValid.cons u v w [] h (WalkValid.nil rfl)⟩
  have hlen : walk.length = w := by
    simp [walk, Walk.length]
  simpa [hlen] using trueDist_le_walk_length G u v walk

/-- Triangle inequality for true distance. -/
theorem trueDist_triangle {n : ℕ} (G : Graph n) (s u v : Fin n) :
    trueDist G s v ≤ trueDist G s u + trueDist G u v := by
  have h1 : ∀ (w2 : Walk G u v), trueDist G s v ≤ trueDist G s u + (w2.length : WithTop NNReal) := by
    intro w2
    have concat_bound : ∀ (w1 : Walk G s u), trueDist G s v ≤
        (w1.length : WithTop NNReal) + (w2.length : WithTop NNReal) := by
      intro w1
      have h := trueDist_le_walk_length G s v (w1.append w2)
      rw [Walk.length_append] at h
      exact h
    calc
      trueDist G s v ≤ ⨅ (w1 : Walk G s u), ((w1.length : WithTop NNReal) + (w2.length : WithTop NNReal)) :=
        le_iInf concat_bound
      _ = (⨅ (w1 : Walk G s u), (w1.length : WithTop NNReal)) + (w2.length : WithTop NNReal) := by
        have h := (ENNReal.iInf_add (f := fun (w1 : Walk G s u) => (w1.length : WithTop NNReal))
          (a := (w2.length : WithTop NNReal))).symm
        simpa using h
      _ = trueDist G s u + (w2.length : WithTop NNReal) := rfl
  calc
    trueDist G s v ≤ ⨅ (w2 : Walk G u v), (trueDist G s u + (w2.length : WithTop NNReal)) :=
      le_iInf h1
    _ = trueDist G s u + ⨅ (w2 : Walk G u v), (w2.length : WithTop NNReal) := by
      have h := (ENNReal.add_iInf (a := trueDist G s u)
        (f := fun (w2 : Walk G u v) => (w2.length : WithTop NNReal))).symm
      simpa using h
    _ = trueDist G s u + trueDist G u v := rfl

/-- The estimate `d̂[v]` maintained by the algorithm. -/
abbrev DistEstimate (n : ℕ) := Fin n → WithTop NNReal

/-- Initial estimate: `d̂[s] = 0`, `d̂[v] = ∞` elsewhere. -/
noncomputable def initEstimate {n : ℕ} (s : Fin n) : DistEstimate n :=
  fun v => if v = s then ((0 : NNReal) : WithTop NNReal) else ⊤

theorem initEstimate_self {n : ℕ} (s : Fin n) : initEstimate s s = 0 := by
  simp [initEstimate]

theorem initEstimate_ne {n : ℕ} (s v : Fin n) (hv : v ≠ s) : initEstimate s v = ⊤ := by
  simp [initEstimate, hv]

/-- If the true distance is finite, a connecting walk exists. -/
theorem nonempty_walk_of_trueDist_lt_top {n : ℕ} (G : Graph n) (s u : Fin n)
    (h : trueDist G s u < ⊤) : Nonempty (Walk G s u) := by
  by_contra hne
  have hEmpty : IsEmpty (Walk G s u) := ⟨fun w => hne ⟨w⟩⟩
  haveI : IsEmpty (Walk G s u) := hEmpty
  have : trueDist G s u = ⊤ := by
    dsimp [trueDist]
    simp [iInf_of_isEmpty]
  rw [this] at h
  simp [lt_top_iff_ne_top] at h

/-- Every walk can be loop-trimmed to use at most `n` edges without increasing length. -/
theorem exists_trimmed_walk {n : ℕ} (G : Graph n) {s u : Fin n} (w : Walk G s u) :
    ∃ w' : Walk G s u, w'.length ≤ w.length ∧ w'.numEdges ≤ n :=
  Walk.exists_trimmed_walk w

/-- Trim a walk that already has optimal length down to at most `n` edges. -/
private theorem exists_shortest_at_trueDist {n : ℕ} {G : Graph n} {s u : Fin n}
    (w : Walk G s u) (heq : (w.length : WithTop NNReal) = trueDist G s u) :
    ∃ w' : Walk G s u, (w'.length : WithTop NNReal) = trueDist G s u ∧ w'.numEdges ≤ n := by
  by_cases hn : w.numEdges ≤ n
  · exact ⟨w, heq, hn⟩
  · have hlen : n + 1 ≤ w.vertices.length := by rw [Walk.vertices_length]; omega
    have hcard : Fintype.card (Fin n) < w.vertices.length := by simp [Fintype.card_fin]; omega
    have hnodup : ¬ w.vertices.Nodup := by
      intro H; exact Nat.not_lt_of_ge (List.Nodup.length_le_card (α := Fin n) H) hcard
    obtain ⟨x, hx⟩ := (List.exists_duplicate_iff_not_nodup).2 hnodup
    obtain ⟨i, j, hij, hxi, hxj⟩ := Walk.duplicate_exists_lt_getElem hx
    have hi' : i.val ≤ w.numEdges := by
      have : i.val < w.numEdges + 1 := by simpa [Walk.vertices_length] using i.isLt
      exact Nat.lt_succ_iff.mp this
    have hj' : j.val ≤ w.numEdges := by
      have : j.val < w.numEdges + 1 := by simpa [Walk.vertices_length] using j.isLt
      exact Nat.lt_succ_iff.mp this
    have hdup : Walk.vertexAt w i.val hi' = Walk.vertexAt w j.val hj' := by
      simp only [Walk.vertexAt, Walk.vertices]
      exact hxi.trans hxj.symm
    let w' := Walk.removeLoop w hi' hj' hij hdup
    have heq' : (w'.length : WithTop NNReal) = trueDist G s u := by
      apply le_antisymm
      · rw [← heq]; exact WithTop.coe_le_coe.mpr (Walk.removeLoop_length_le w hi' hj' hij hdup)
      · exact trueDist_le_walk_length G s u w'
    obtain ⟨w'', heq'', hn''⟩ := exists_shortest_at_trueDist w' heq'
    exact ⟨w'', heq'', hn''⟩
  termination_by w.numEdges
  decreasing_by
    exact Walk.removeLoop_numEdges_lt _ _ _ _ _

lemma trueDist_eq_ciInf_edges_le {n : ℕ} {G : Graph n} {s u : Fin n}
    (hne : Nonempty { w : Walk G s u // w.numEdges ≤ n }) :
    trueDist G s u =
      ⨅ w' : { w : Walk G s u // w.numEdges ≤ n }, (w'.val.length : WithTop NNReal) := by
  apply le_antisymm
  · dsimp [trueDist]
    refine le_ciInf fun w' => trueDist_le_walk_length G s u w'.val
  · dsimp [trueDist]
    refine le_iInf fun w => ?_
    obtain ⟨w', hle, hn⟩ := exists_trimmed_walk G w
    calc
      (⨅ w' : { w : Walk G s u // w.numEdges ≤ n }, (w'.val.length : WithTop NNReal)) ≤
          (w'.length : WithTop NNReal) := iInf_le _ (⟨w', hn⟩ : { w : Walk G s u // w.numEdges ≤ n })
      _ ≤ (w.length : WithTop NNReal) := WithTop.coe_le_coe.mpr hle

private lemma mem_outEdges_iff {n : ℕ} {G : Graph n} {u v : Fin n} {w : NNReal} :
    (v, w) ∈ G.outEdges u ↔ w ∈ G.edges u v := by
  simp [Graph.outEdges, Multiset.mem_bind, Multiset.mem_map]

/-- All walks from `s` to `u` using exactly `k` edges. -/
noncomputable def walksOfLength {n : ℕ} (G : Graph n) (s u : Fin n) : ℕ → Finset (Walk G s u)
| 0 =>
  if h : s = u then
    { (⟨[], WalkValid.nil h⟩ : Walk G s u) }
  else
    ∅
| k + 1 =>
  (G.outEdges s).toFinset.attach.biUnion fun p =>
    (walksOfLength G p.1.1 u k).image fun w' =>
      Walk.consStep p.1.2 w' (mem_outEdges_iff.mp (Multiset.mem_toFinset.mp p.2))

/-- All walks from `s` to `u` using at most `n` edges. -/
noncomputable def boundedWalks {n : ℕ} (G : Graph n) (s u : Fin n) : Finset (Walk G s u) :=
  (Finset.range (n + 1)).biUnion fun k => walksOfLength G s u k

private lemma walksOfLength_numEdges {n : ℕ} {G : Graph n} {s u : Fin n} {k : ℕ}
    {w : Walk G s u} (hw : w ∈ walksOfLength G s u k) : w.numEdges = k := by
  induction k generalizing w s u with
  | zero =>
    by_cases h : s = u
    · simp [walksOfLength, h, Finset.mem_singleton] at hw
      cases hw
      rfl
    · simp [walksOfLength, h] at hw
  | succ k ih =>
    simp only [walksOfLength, Finset.mem_biUnion, Finset.mem_image, true_and] at hw
    obtain ⟨p, _, w', hw', rfl⟩ := hw
    dsimp [Walk.consStep, Walk.numEdges]
    exact congrArg Nat.succ (ih (s := p.1.1) hw')

private lemma mem_walksOfLength_of_numEdges {n : ℕ} {G : Graph n} {s u : Fin n} {k : ℕ}
    (w : Walk G s u) (hk : w.numEdges = k) : w ∈ walksOfLength G s u k := by
  induction k generalizing w s u with
  | zero =>
    rcases w with ⟨steps, valid⟩
    simp [Walk.numEdges] at hk
    cases valid with
    | nil h =>
      simp [walksOfLength, h, Finset.mem_singleton]
    | cons _ _ _ _ _ _ => simp [Walk.numEdges] at hk
  | succ k ih =>
    rcases w with ⟨steps, valid⟩
    cases valid with
    | nil => simp [Walk.numEdges] at hk
    | cons _ v w₀ rest h_edge h_tail =>
      simp only [Walk.numEdges] at hk
      have hk' : rest.length = k := by simp [Walk.numEdges] at hk; omega
      let w' : Walk G v u := ⟨rest, h_tail⟩
      have hw' : w' ∈ walksOfLength G v u k := ih w' hk'
      have hout : (v, w₀) ∈ (G.outEdges s).toFinset := by
        simpa [Multiset.mem_toFinset, mem_outEdges_iff] using h_edge
      let edge : ↥(G.outEdges s).toFinset := ⟨(v, w₀), hout⟩
      simp only [walksOfLength, Finset.mem_biUnion, Finset.mem_image, true_and]
      refine ⟨edge, ?_, w', hw', rfl⟩
      exact Finset.mem_attach _ edge

private lemma mem_boundedWalks_of_numEdges_le {n : ℕ} {G : Graph n} {s u : Fin n}
    {w : Walk G s u} (hk : w.numEdges ≤ n) : w ∈ boundedWalks G s u := by
  simp [boundedWalks, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨w.numEdges, Nat.lt_succ_of_le hk, mem_walksOfLength_of_numEdges w rfl⟩

private lemma boundedWalks_nonempty {n : ℕ} {G : Graph n} {s u : Fin n}
    (h : trueDist G s u < ⊤) : (boundedWalks G s u).Nonempty := by
  obtain ⟨w0⟩ := nonempty_walk_of_trueDist_lt_top G s u h
  obtain ⟨w', _, hn⟩ := exists_trimmed_walk G w0
  exact ⟨w', mem_boundedWalks_of_numEdges_le hn⟩

private lemma trueDist_eq_inf_boundedWalks {n : ℕ} {G : Graph n} {s u : Fin n}
    (h : trueDist G s u < ⊤) :
    trueDist G s u =
      (boundedWalks G s u).inf' (boundedWalks_nonempty h)
        (fun w => (w.length : WithTop NNReal)) := by
  obtain ⟨w0⟩ := nonempty_walk_of_trueDist_lt_top G s u h
  obtain ⟨w', _, hn'⟩ := exists_trimmed_walk G w0
  have hne : Nonempty { w : Walk G s u // w.numEdges ≤ n } := ⟨⟨w', hn'⟩⟩
  rw [trueDist_eq_ciInf_edges_le hne]
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro w hw
    have hn : w.numEdges ≤ n := by
      simp [boundedWalks, Finset.mem_biUnion, Finset.mem_range] at hw
      obtain ⟨k, hk, hwk⟩ := hw
      simpa [← walksOfLength_numEdges hwk] using Nat.le_of_lt_succ hk
    exact iInf_le (f := fun (w : { w : Walk G s u // w.numEdges ≤ n }) =>
      (w.val.length : WithTop NNReal)) ⟨w, hn⟩
  · refine le_ciInf (f := fun (w : { w : Walk G s u // w.numEdges ≤ n }) =>
      (w.val.length : WithTop NNReal)) fun w =>
    Finset.inf'_le _ (mem_boundedWalks_of_numEdges_le w.property)

/-- Shortest distances are achieved by some walk using at most `n` edges. -/
theorem exists_shortest_bounded_walk {n : ℕ} (G : Graph n) (s u : Fin n)
    (h : trueDist G s u < ⊤) :
    ∃ w : Walk G s u, (w.length : WithTop NNReal) = trueDist G s u ∧ w.numEdges ≤ n := by
  have hne := boundedWalks_nonempty h
  obtain ⟨w, hw, hinf⟩ :=
    Finset.exists_mem_eq_inf' (s := boundedWalks G s u) (H := hne)
      (f := fun w => (w.length : WithTop NNReal))
  have heq : (w.length : WithTop NNReal) = trueDist G s u := by
    rw [← hinf, trueDist_eq_inf_boundedWalks h]
  have hn : w.numEdges ≤ n := by
    simp [boundedWalks, Finset.mem_biUnion, Finset.mem_range] at hw
    obtain ⟨k, hk, hwk⟩ := hw
    simpa [← walksOfLength_numEdges hwk] using Nat.le_of_lt_succ hk
  exact ⟨w, heq, hn⟩

private lemma trueDist_eq_length_of_shortest {n : ℕ} {G : Graph n} {s u : Fin n}
    {walk : Walk G s u} (heq : (walk.length : WithTop NNReal) = trueDist G s u) :
    trueDist G s u = walk.length := heq.symm

private lemma walk_numEdges_zero_eq_source {n : ℕ} {G : Graph n} {s u : Fin n}
    {walk : Walk G s u} (h : walk.numEdges = 0) : u = s := by
  rcases walk with ⟨steps, valid⟩
  match steps with
  | [] =>
    cases valid with
    | nil heq' => exact heq'.symm
  | _ :: _ => simp [Walk.numEdges] at h

private lemma wt_eq_zero_of_dist_le_add {n : ℕ} {G : Graph n} {s x : Fin n} {wt : NNReal}
    (hfinx : trueDist G s x < ⊤) (hle : trueDist G s x + wt ≤ trueDist G s x) : wt = 0 := by
  have hle' : trueDist G s x + (wt : WithTop NNReal) ≤ trueDist G s x + 0 := by simpa [add_zero] using hle
  have h := WithTop.le_of_add_le_add_left (ne_of_lt hfinx) hle'
  simpa [NNReal.coe_eq_zero] using WithTop.coe_le_coe.mp h

/-- Last step of a nonempty walk is one edge into the target. -/
private lemma exists_last_edge_of_pos {n : ℕ} {G : Graph n} {s u : Fin n}
    (walk : Walk G s u) (hm : 0 < walk.numEdges) :
    ∃ x wt, wt ∈ G.edges x u ∧
      x = walk.vertexAt (walk.numEdges - 1) (Nat.pred_le walk.numEdges) ∧
      walk.length =
        (walk.takeSteps (walk.numEdges - 1) (Nat.pred_le walk.numEdges)).length + wt ∧
      (walk.dropSteps (walk.numEdges - 1) (Nat.pred_le walk.numEdges)).length = wt := by
  let j := walk.numEdges - 1
  let hj := Nat.pred_le walk.numEdges
  have hdrop : (walk.dropSteps j hj).numEdges = 1 := by
    rw [Walk.numEdges_dropSteps]
    dsimp [j]
    omega
  set tail := walk.dropSteps j hj
  have hm : 0 < tail.numEdges := by rw [hdrop]; omega
  obtain ⟨v, wt, tailWalk, hsteps, h_edge⟩ := Walk.exists_first_step_tail hm
  have hw'nil : tailWalk.steps = [] := by
    have hn : tailWalk.steps.length = 0 := by
      have hlen : tailWalk.steps.length + 1 = tail.steps.length := by
        simpa [List.length_cons] using congrArg List.length hsteps.symm
      have htail : tail.steps.length = 1 := by simpa [Walk.numEdges] using hdrop
      linarith
    exact List.eq_nil_of_length_eq_zero hn
  have hvu : v = u := by
    have hvalid := tailWalk.valid
    rw [hw'nil] at hvalid
    cases hvalid with
    | nil hTU => exact hTU
  have hlen_tail : tail.length = wt := by
    have hsteps' : tail.steps = [(v, wt)] := by
      rw [hw'nil] at hsteps
      simpa using hsteps
    rcases tail with ⟨steps, valid⟩
    subst hsteps'
    simp [Walk.length]
  refine ⟨walk.vertexAt j hj, wt,
    by simpa [Walk.vertexAt_zero, Walk.dropSteps, hvu] using h_edge, rfl, ?_, hlen_tail⟩
  rw [← hlen_tail]
  simpa [tail, Walk.dropSteps] using Walk.length_takeSteps_add_dropSteps (w := walk) (j := j) hj

private lemma numEdges_cast {n : ℕ} {G : Graph n} {s v u : Fin n} (h : v = u) (w : Walk G s v) :
    (cast (congr_arg (Walk G s) h) w).numEdges = w.numEdges := by subst h; rfl

private lemma length_cast {n : ℕ} {G : Graph n} {s v u : Fin n} (h : v = u) (w : Walk G s v) :
    (cast (congr_arg (Walk G s) h) w).length = w.length := by subst h; rfl

private lemma trueDist_le_takeSteps_length {n : ℕ} {G : Graph n} {s u : Fin n}
    (walk : Walk G s u) {j : ℕ} (hj : j ≤ walk.numEdges) :
    trueDist G s (walk.vertexAt j hj) ≤ (walk.takeSteps j hj).length :=
  trueDist_le_walk_length G s (walk.vertexAt j hj) (walk.takeSteps j hj)

/-- Core induction on walk length: a shortest bounded walk yields a tight predecessor in `S`. -/
private theorem exists_tight_pred_of_min_outside_go {n : ℕ} (G : Graph n) (s u : Fin n)
    (S : Finset (Fin n)) (hu : u ∉ S) (hs : s ∈ S)
    (hmin : ∀ y ∉ S, trueDist G s u ≤ trueDist G s y) (_hfin : trueDist G s u < ⊤)
    (hdist : ∀ {v w : Fin n}, v ≠ w → trueDist G s v ≠ trueDist G s w) :
    ∀ (m : ℕ) (walk : Walk G s u), walk.numEdges = m → m ≤ n →
      (walk.length : WithTop NNReal) = trueDist G s u →
      ∃ x ∈ S, ∃ w : NNReal, w ∈ G.edges x u ∧ trueDist G s u = trueDist G s x + w := by
  intro m walk hm hbound heq
  induction m using Nat.strong_induction_on generalizing walk heq with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      have hu' : u = s := walk_numEdges_zero_eq_source (walk := walk) hm
      subst hu'
      exact absurd hs hu
    have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => hm0 h)
    have hmpos' : 0 < walk.numEdges := by simpa [hm] using hmpos
    obtain ⟨x, wt, hwt, hx, hlen_split, _⟩ :=
      exists_last_edge_of_pos (walk := walk) hmpos'
    let j := walk.numEdges - 1
    let hj := Nat.pred_le walk.numEdges
    have hle_prefix' : trueDist G s (walk.vertexAt j hj) ≤ (walk.takeSteps j hj).length :=
      trueDist_le_takeSteps_length (walk := walk) (j := j) (hj := hj)
    have hle_prefix : trueDist G s x ≤ (walk.takeSteps j hj).length := by
      simpa [hx] using hle_prefix'
    have hle_upper : trueDist G s u ≤ trueDist G s x + wt := by
      calc
        trueDist G s u ≤ trueDist G s x + trueDist G x u := trueDist_triangle G s x u
        _ ≤ trueDist G s x + wt := add_le_add (le_refl _) (trueDist_edge G x u wt hwt)
    have hle_lower : trueDist G s x + wt ≤ trueDist G s u := by
      rw [heq.symm, hlen_split]
      exact add_le_add_left hle_prefix wt
    by_cases hxS : x ∈ S
    · refine ⟨x, hxS, wt, hwt, (hle_lower.antisymm hle_upper).symm⟩
    · by_cases hpos : 0 < wt
      · exfalso
        have hfinx : trueDist G s x < ⊤ := lt_of_le_of_lt hle_prefix (WithTop.coe_lt_top _)
        exact ne_of_gt hpos (wt_eq_zero_of_dist_le_add hfinx (le_trans hle_lower (hmin x hxS)))
      · have hwt_zero : wt = 0 := le_antisymm (not_lt.mp hpos) (zero_le wt)
        have heqdist : trueDist G s u = trueDist G s x :=
          le_antisymm (hmin x hxS) (by
            rw [heq.symm, hlen_split, hwt_zero, add_zero]
            exact hle_prefix)
        rcases eq_or_ne x u with hxu | hxu
        · have hm1 : 1 < m := by
            by_contra hnot
            push_neg at hnot
            have h1 : m = 1 := by omega
            subst h1
            simp [j, hm, Walk.vertexAt_zero] at hx
            have hxs : x = s := by simpa [j, hm, Walk.vertexAt_zero] using hx
            exact hxS (hxs ▸ hs)
          have hva : walk.vertexAt j hj = u := (hxu.symm.trans hx).symm
          let wprefix := walk.takeSteps j hj
          have hnum : wprefix.numEdges = m - 1 := by
            simpa [wprefix, Walk.numEdges_takeSteps, j, hm] using
              Walk.numEdges_takeSteps j walk hj
          have hwp_len : wprefix.length = walk.length := by
            apply Eq.symm
            rw [hlen_split, hwt_zero, add_zero]
          have hco : (wprefix.length : WithTop NNReal) = (walk.length : WithTop NNReal) :=
            WithTop.coe_eq_coe.mpr hwp_len
          have heq' : (wprefix.length : WithTop NNReal) = trueDist G s u := hco.trans heq
          let wcast : Walk G s u := cast (congr_arg (Walk G s) hva) wprefix
          have hnum' : wcast.numEdges = m - 1 := by rw [numEdges_cast hva, hnum]
          have heq'' : (wcast.length : WithTop NNReal) = trueDist G s u := by
            rw [← heq', WithTop.coe_inj.mpr (length_cast hva wprefix)]
          exact ih (m - 1) (by omega) wcast hnum'
            (Nat.le_trans (Nat.sub_le _ _) hbound) heq''
        · exact absurd heqdist.symm (hdist hxu)

/-- Among vertices outside `S`, a minimum-`trueDist` vertex has a tight settled predecessor in `S`. -/
theorem exists_tight_pred_of_min_outside {n : ℕ} (G : Graph n) {s u : Fin n}
    (S : Finset (Fin n)) (hu : u ∉ S) (hs : s ∈ S)
    (hmin : ∀ y ∉ S, trueDist G s u ≤ trueDist G s y) (hfin : trueDist G s u < ⊤)
    (hdist : ∀ {v w : Fin n}, v ≠ w → trueDist G s v ≠ trueDist G s w) :
    ∃ x ∈ S, ∃ w : NNReal, w ∈ G.edges x u ∧ trueDist G s u = trueDist G s x + w := by
  obtain ⟨walk, heq, hn⟩ := exists_shortest_bounded_walk G s u hfin
  exact exists_tight_pred_of_min_outside_go (G := G) (s := s) (u := u) S hu hs hmin hfin hdist
    walk.numEdges walk rfl hn heq

/-- Soundness invariant maintained throughout the algorithm:
    `d̂[v] ≥ d(v)` for every `v`. -/
def Sound {n : ℕ} (G : Graph n) (s : Fin n) (dHat : DistEstimate n) : Prop :=
  ∀ v, trueDist G s v ≤ dHat v

/-- The initial estimate is sound: `d(v) ≤ d̂[v]` for every vertex. -/
theorem initEstimate_sound {n : ℕ} (G : Graph n) (s : Fin n) : Sound G s (initEstimate s) := by
  intro v
  by_cases hv : v = s
  · subst hv
    rw [initEstimate_self, trueDist_self]
  · rw [initEstimate_ne _ _ hv]
    exact le_top

/-- Along any walk, edge-upper estimates grow by at most walk length from the walk start. -/
theorem dHat_le_add_walk_length {n : ℕ} {G : Graph n} {dHat : DistEstimate n}
    (hEdge : ∀ {u v : Fin n} {w : NNReal}, w ∈ G.edges u v → dHat v ≤ dHat u + w)
    {src tgt : Fin n} (walk : Walk G src tgt) :
    dHat tgt ≤ dHat src + (walk.length : WithTop NNReal) := by
  have h : ∀ (src tgt : Fin n) (walk : Walk G src tgt) (fuel : Nat),
      walk.numEdges = fuel → dHat tgt ≤ dHat src + (walk.length : WithTop NNReal) := by
    intro src tgt walk fuel
    induction fuel generalizing src tgt walk with
    | zero =>
      intro hfuel
      rcases walk with ⟨steps, valid⟩
      have hnil : steps = [] := by
        cases steps with
        | nil => rfl
        | cons _ _ => simp [Walk.numEdges] at hfuel
      subst hnil
      cases valid with
      | nil heq =>
        subst heq
        simp [Walk.length, add_zero]
    | succ fuel ih =>
      intro hfuel
      have hn : 0 < walk.numEdges := by rw [hfuel]; exact Nat.succ_pos fuel
      obtain ⟨v, w0, w', hsteps, h_edge⟩ := Walk.exists_first_step_tail (G := G) hn
      have hfuel' : w'.numEdges = fuel := by
        simp [Walk.numEdges, hsteps] at hfuel ⊢
        omega
      have hlen : (walk.length : WithTop NNReal) = (w0 : WithTop NNReal) + w'.length := by
        simp [Walk.length, hsteps, List.sum_cons]
      calc
        dHat tgt ≤ dHat v + (w'.length : WithTop NNReal) := ih v tgt w' hfuel'
        _ ≤ dHat src + (w0 : WithTop NNReal) + w'.length := by
          gcongr
          exact hEdge h_edge
        _ = dHat src + ((w0 : WithTop NNReal) + w'.length) := by rw [add_assoc]
        _ = dHat src + (walk.length : WithTop NNReal) := by rw [hlen]
  exact h src tgt walk walk.numEdges rfl

/-- Along any walk from `s`, edge-upper estimates are bounded by walk length. Requires `dHat s = 0`. -/
theorem dHat_le_walk_length {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hSource : dHat s = 0)
    (hEdge : ∀ {u v : Fin n} {w : NNReal}, w ∈ G.edges u v → dHat v ≤ dHat u + w)
    {t : Fin n} (w : Walk G s t) :
    dHat t ≤ (w.length : WithTop NNReal) := by
  have h := dHat_le_add_walk_length (G := G) (dHat := dHat) hEdge w
  calc
    dHat t ≤ dHat s + (w.length : WithTop NNReal) := h
    _ = (w.length : WithTop NNReal) := by rw [hSource, zero_add]

/-- Edge-upper estimates never exceed true distance. Requires `dHat s = 0`. -/
theorem dHat_le_trueDist_of_edgeUpper {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hSource : dHat s = 0)
    (hEdge : ∀ {u v : Fin n} {w : NNReal}, w ∈ G.edges u v → dHat v ≤ dHat u + w) :
    ∀ v, dHat v ≤ trueDist G s v := by
  intro v
  apply le_iInf
  intro walk
  exact dHat_le_walk_length (G := G) (s := s) hSource hEdge walk

/-- A vertex `v` is **complete** w.r.t. `dHat` iff its current estimate
    equals its true distance. -/
def IsComplete {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (v : Fin n) : Prop :=
  dHat v = trueDist G s v

/-- Every edge is tight-upper relative to `dHat` (a relaxation fixpoint condition). -/
def EdgeUpper {n : ℕ} (G : Graph n) (_s : Fin n) (dHat : DistEstimate n) : Prop :=
  (∀ {u v : Fin n} {w : NNReal}, w ∈ G.edges u v → dHat v ≤ dHat u + w)

/-- `Sound` plus edge-upper bounds give completeness. Requires `dHat s = 0`. -/
theorem isComplete_of_sound_and_edgeUpper {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    (hSource : dHat s = 0) (hSound : Sound G s dHat) (hEdge : EdgeUpper G s dHat) (v : Fin n) :
    IsComplete G s dHat v := by
  dsimp [IsComplete]
  exact le_antisymm (dHat_le_trueDist_of_edgeUpper (G := G) (s := s) hSource
    (fun h => hEdge h) v) (hSound v)

/-- A set `S` is **complete** iff every vertex in `S` is complete. -/
def SetComplete {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ S, IsComplete G s dHat v

/-- `S^*` — the complete vertices of `S`. -/
noncomputable def completeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (IsComplete G s dHat)

lemma mem_completeOf_iff {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} {v : Fin n} : v ∈ completeOf G s dHat S ↔ v ∈ S ∧ IsComplete G s dHat v := by
  simp [completeOf]

lemma completeOf_subset {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} : completeOf G s dHat S ⊆ S := by
  intro v hv; rcases (mem_completeOf_iff.mp hv) with ⟨hvS, _⟩; exact hvS

/-- `T(v) = { u | d(s,u) = d(s,v) + d(v,u) }` — vertices whose unique
    shortest path from `s` passes through `v`. Under `HasDistinctLengths`
    this is exactly the subtree rooted at `v` in the shortest-path tree. -/
noncomputable def subtree {n : ℕ} (G : Graph n) (s v : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun u => trueDist G s u = trueDist G s v + trueDist G v u)

/-- `T(S) = ⋃ v ∈ S, T(v)`. -/
noncomputable def subtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  S.biUnion (subtree G s)

lemma subtreeOf_empty {n : ℕ} (G : Graph n) (s : Fin n) : subtreeOf G s ∅ = ∅ := by
  simp [subtreeOf]

/-- `T_{<B}(S) = { v ∈ T(S) : d(v) < B }`. -/
noncomputable def boundedSubtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) (B : WithTop NNReal) : Finset (Fin n) :=
  (subtreeOf G s S).filter (fun v => trueDist G s v < B)

lemma mem_boundedSubtreeOf_iff {n : ℕ} {G : Graph n} {s : Fin n}
    {S : Finset (Fin n)} {B : WithTop NNReal} {v : Fin n} :
    v ∈ boundedSubtreeOf G s S B ↔ v ∈ subtreeOf G s S ∧ trueDist G s v < B := by
  simp [boundedSubtreeOf]

lemma boundedSubtreeOf_empty {n : ℕ} (G : Graph n) (s : Fin n) (B : WithTop NNReal) :
    boundedSubtreeOf G s ∅ B = ∅ := by
  simp [boundedSubtreeOf, subtreeOf_empty]

/-- `T_{[a, b)}(S)` — the "annulus" used in the proof of Lemma 3.6 et seq. -/
noncomputable def rangeSubtreeOf {n : ℕ} (G : Graph n) (s : Fin n)
    (S : Finset (Fin n)) (a b : WithTop NNReal) : Finset (Fin n) :=
  (subtreeOf G s S).filter (fun v => a ≤ trueDist G s v ∧ trueDist G s v < b)

/-- The `Ũ` of the paper (top of §3.4): vertices below `B` whose shortest
    path visits a complete vertex of `S`. Coincides with `T_{<B}(S^*)`. -/
noncomputable def expectU {n : ℕ} (G : Graph n) (s : Fin n)
    (dHat : DistEstimate n) (S : Finset (Fin n))
    (B : WithTop NNReal) : Finset (Fin n) :=
  boundedSubtreeOf G s (completeOf G s dHat S) B

lemma mem_expectU_iff {n : ℕ} {G : Graph n} {s : Fin n} {dHat : DistEstimate n}
    {S : Finset (Fin n)} {B : WithTop NNReal} {v : Fin n} :
    v ∈ expectU G s dHat S B ↔
      v ∈ subtreeOf G s (completeOf G s dHat S) ∧ trueDist G s v < B :=
  mem_boundedSubtreeOf_iff

/-- Strengthening of `HasDistinctLengths`: every pair of distinct vertices
    has distinct true distance from `s`.  The paper achieves this with
    probability 1 by sampling continuous random edge weights; we expose it
    as an explicit assumption.  This is what makes "the `k+1` closest
    vertices to `x`" a well-defined set, hence what makes the size bound
    `|U| ≤ 4k` of `baseCase` constructively provable. -/
class HasDistinctVertexDistances {n : ℕ} (G : Graph n) (s : Fin n) : Prop where
  distinct : ∀ {u v : Fin n}, u ≠ v → trueDist G s u ≠ trueDist G s v

/-- Same conclusion under globally distinct vertex distances (e.g. BMSSP assumption). -/
theorem exists_tight_pred_of_min_outside_distinct {n : ℕ} (G : Graph n) {s u : Fin n}
    (S : Finset (Fin n)) (hu : u ∉ S) (hs : s ∈ S)
    (hmin : ∀ y ∉ S, trueDist G s u ≤ trueDist G s y) (hfin : trueDist G s u < ⊤)
    [HasDistinctVertexDistances G s] :
    ∃ x ∈ S, ∃ w : NNReal, w ∈ G.edges x u ∧ trueDist G s u = trueDist G s x + w :=
  exists_tight_pred_of_min_outside (G := G) (s := s) S hu hs hmin hfin
    (fun {v w} hne => HasDistinctVertexDistances.distinct (G := G) (s := s) hne)

/-! ### Truncation witness

    The combinatorial backbone of both `BaseCase` and the inductive step of
    `BMSSP`: under `HasDistinctVertexDistances`, for any frontier `S`, any
    cap `B`, and any `k * M`-sized "budget", we can pick a truncated bound
    `B' ≤ B` whose induced bounded subtree has size at most `4 * k * M`,
    *and* if we strictly cut down (`B' < B`) we kept at least `k * M`
    vertices.  This is the key fact that makes the BMSSP size bound
    (Lemma 3.10) algorithmically realisable. -/

/-- Combinatorial helper: for any `Finset α` over a linear order, the
    number of elements strictly below the `i`-th smallest is exactly
    `i`. -/
private lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (s.filter (· < s.orderEmbOfFin h i)).card = i := by
  set e := s.orderEmbOfFin h with he
  conv_lhs =>
    rw [show s = Finset.image e Finset.univ from
          (Finset.image_orderEmbOfFin_univ s h).symm]
  rw [Finset.filter_image]
  have h_filter_eq :
      ((Finset.univ : Finset (Fin k)).filter (fun a => e a < e i)) =
        (Finset.univ : Finset (Fin k)).filter (fun a => a < i) := by
    ext j; simp [e.lt_iff_lt]
  rw [h_filter_eq, Finset.card_image_of_injective _ e.injective]
  have := @Fin.card_filter_val_lt k i.val
  rw [Nat.min_eq_right (Nat.le_of_lt i.isLt)] at this
  exact this

/-- **Truncation witness.** For every frontier `S`, cap `B`, and budget
    parameters `k, M`, there exists a truncated bound `B' ≤ B` such that
    the bounded subtree below `B'` has at most `4 * k * M` vertices, and
    (if we strictly cut, `B' < B`) at least `k * M` vertices.  The proof
    is a direct order-theoretic argument on the finset of distances. -/
theorem exists_truncation_witness {n : ℕ} (G : Graph n) (s : Fin n)
    [HasDistinctVertexDistances G s]
    (k M : ℕ) (B : WithTop NNReal) (S : Finset (Fin n)) :
    ∃ B', B' ≤ B ∧
      (boundedSubtreeOf G s S B').card ≤ 4 * k * M ∧
      (B' < B → k * M ≤ (boundedSubtreeOf G s S B').card) := by
  set T := boundedSubtreeOf G s S B with hT_def
  by_cases h_small : T.card ≤ 4 * k * M
  · -- Case A: T already fits; take `B' := B`, in which case `T_{<B} = T`.
    refine ⟨B, le_refl _, ?_, ?_⟩
    · simpa [hT_def] using h_small
    · intro h_lt; exact absurd h_lt (lt_irrefl _)
  · -- Case B: `T.card > 4 * k * M`.  Sort distances and pick the
    -- `(k * M)`-th smallest as the new bound.
    have h_small : 4 * k * M < T.card := Nat.lt_of_not_le h_small
    set f : Fin n → WithTop NNReal := trueDist G s with hf_def
    set DT : Finset (WithTop NNReal) := T.image f with hDT_def
    -- Distinct vertex distances ⇒ `f` is injective on `T`.
    have h_inj_on : Set.InjOn f (T : Set (Fin n)) := by
      intro u _ v _ h_eq
      by_contra h_ne
      exact (HasDistinctVertexDistances.distinct h_ne) h_eq
    have hDT_card : DT.card = T.card := Finset.card_image_of_injOn h_inj_on
    have h_kM_le_4kM : k * M ≤ 4 * k * M := by
      have : k * M ≤ 4 * (k * M) := Nat.le_mul_of_pos_left _ (by norm_num)
      simpa [Nat.mul_assoc] using this
    have h_kM_lt_card : k * M < DT.card := by
      rw [hDT_card]; exact lt_of_le_of_lt h_kM_le_4kM h_small
    set B' : WithTop NNReal := DT.orderEmbOfFin rfl ⟨k * M, h_kM_lt_card⟩ with hB'_def
    -- `B'` is a real distance to some `v ∈ T`, hence `B' < B`.
    have hB'_in_DT : B' ∈ DT := Finset.orderEmbOfFin_mem DT rfl _
    rw [hDT_def, Finset.mem_image] at hB'_in_DT
    obtain ⟨v, hv_in_T, hv_eq⟩ := hB'_in_DT
    have hv_lt_B : f v < B := by
      rw [hT_def, mem_boundedSubtreeOf_iff] at hv_in_T; exact hv_in_T.2
    have hB'_lt_B : B' < B := by rw [← hv_eq]; exact hv_lt_B
    have hB'_le_B : B' ≤ B := le_of_lt hB'_lt_B
    -- Cardinalities transfer through the bijection `T ↔ DT`.
    have h_T_filter_card : (T.filter (fun v => f v < B')).card = k * M := by
      have h_image_eq :
          DT.filter (· < B') = (T.filter (fun v => f v < B')).image f := by
        rw [hDT_def, Finset.filter_image]
      have h_card_eq :
          (DT.filter (· < B')).card = (T.filter (fun v => f v < B')).card := by
        rw [h_image_eq]
        apply Finset.card_image_of_injOn
        intro u hu v hv h_uv_eq
        simp at hu hv
        exact h_inj_on hu.1 hv.1 h_uv_eq
      rw [← h_card_eq]
      exact card_filter_lt_orderEmbOfFin DT rfl ⟨k * M, h_kM_lt_card⟩
    -- The filter equals `boundedSubtreeOf G s S B'` because `B' ≤ B`.
    have h_filter_eq :
        T.filter (fun v => f v < B') = boundedSubtreeOf G s S B' := by
      rw [hT_def]
      ext u
      rw [Finset.mem_filter, mem_boundedSubtreeOf_iff, mem_boundedSubtreeOf_iff]
      refine ⟨fun ⟨⟨h_sub, _⟩, h_lt_B'⟩ => ⟨h_sub, h_lt_B'⟩, ?_⟩
      intro ⟨h_sub, h_lt_B'⟩
      exact ⟨⟨h_sub, lt_of_lt_of_le h_lt_B' hB'_le_B⟩, h_lt_B'⟩
    have h_card_BS : (boundedSubtreeOf G s S B').card = k * M := by
      rw [← h_filter_eq, h_T_filter_card]
    refine ⟨B', hB'_le_B, ?_, ?_⟩
    · rw [h_card_BS]; exact h_kM_le_4kM
    · intro _; rw [h_card_BS]

end

end Sssp
