import LeanCompletion.UAV.TreeBudgetSubtreeStatsBounds

/-! Composition of local envelopes and tree-wide accounting. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeState TreeFlowExistence
variable {m N : ℕ}

def scaleEnvelope (q : ℕ) (b : DPStats) : DPStats :=
  ⟨q * b.nodeCalls,
   q * b.compositionCalls,
   q * b.rangeChoices,
   q * b.columnsGenerated,
   q * b.columnsAccepted,
   q * b.subsetCalls,
   q * b.insidePairs,
   q * b.rootPairs,
   q * b.rootRejected,
   q * b.ratAdds,
   q * b.ratMuls,
   q * b.dedupInput,
   q * b.dedupOutput,
   q * b.eqCalls,
   q * b.acceptCalls,
   b.maxRawTable, b.maxDedupTable⟩

theorem covers_sum (ss : List DPStats) (b : DPStats)
    (h : ∀ s ∈ ss, Covers s b) : Covers (sumStats ss) (scaleEnvelope ss.length b) := by
  induction ss with
  | nil => simp [sumStats, scaleEnvelope, Covers]
  | cons s ss ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    have hh := covers_add hs ht
    simp only [sumStats]
    simp only [Covers, DPStats.add, scaleEnvelope, List.length_cons, Nat.add_mul, one_mul] at hh ⊢
    omega

theorem sumStats_compositions_only (ss : List DPStats)
    (h : ∀ s ∈ ss, s = { compositionCalls := s.compositionCalls, rangeChoices := s.rangeChoices }) :
    sumStats ss =
      { compositionCalls := (sumStats ss).compositionCalls,
        rangeChoices := (sumStats ss).rangeChoices } := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    rw [sumStats, hs, ht]
    rfl

theorem compositionProfile_only (m h : ℕ) :
    compositionProfile m h =
      { compositionCalls := (compositionProfile m h).compositionCalls,
        rangeChoices := (compositionProfile m h).rangeChoices } := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    rw [compositionProfile]
    have hh := sumStats_compositions_only
      ((List.range (h + 1)).map fun a => compositionProfile m (h - a)) (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
        exact ih _)
    rw [hh]
    rfl

theorem compositionProfile_covers (m h C : ℕ) (hc : (compositionProfile m h).compositionCalls ≤ C) :
    Covers (compositionProfile m h) { compositionCalls := C, rangeChoices := C } := by
  have hr := compositionProfile_choices m h
  rw [compositionProfile_only]
  simp only [Covers]
  omega

def nodeEnvelope (m k C P : ℕ) : DPStats :=
  { compositionCalls := C, rangeChoices := C, columnsGenerated := P, columnsAccepted := P,
    subsetCalls := k * P, insidePairs := k * P, ratAdds := m * (k * P), ratMuls := m * P,
    dedupInput := (k + 1) * P, dedupOutput := (k + 1) * P, eqCalls := (k + 1) * P ^ 2,
    maxRawTable := P, maxDedupTable := P }

theorem nodeProfile_bounds (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) (C P : ℕ)
    (hc : (compositionProfile m (H v)).compositionCalls ≤ C)
    (hp : columnFactor m (H v) * safeProduct ts ≤ P) :
    Covers (nodeProfile R H s m v ts) (nodeEnvelope m ts.length C P) := by
  let q := (localCandidates R H m v).length
  let B := safeProduct ts
  have hb : 1 ≤ B := safeProduct_pos ts
  have hq := localCandidates_length_le R H m v
  have hqB : q * B ≤ P := (Nat.mul_le_mul_right B hq).trans hp
  have hB : B ≤ P := by
    have := le_max_left 1 (columnCount m (H v))
    change 1 ≤ columnFactor m (H v) at this
    nlinarith
  have hqp : q ≤ P := by nlinarith
  have hgen : (compositionsV m (H v)).length ≤ P := by
    rw [compositionsV_length]
    apply (le_max_right 1 (columnCount m (H v))).trans
    change columnFactor m (H v) ≤ P
    nlinarith
  have hlocal : Covers ((compositionProfile m (H v)).add
      { columnsGenerated := (compositionsV m (H v)).length, columnsAccepted := q })
      { compositionCalls := C, rangeChoices := C, columnsGenerated := P, columnsAccepted := P } := by
    have hh := covers_add (compositionProfile_covers m (H v) C hc)
      (show Covers
        ({ columnsGenerated := (compositionsV m (H v)).length, columnsAccepted := q } : DPStats)
        { columnsGenerated := P, columnsAccepted := P } from by
        simp only [Covers]; omega)
    simpa only [DPStats.add, Nat.zero_add, Nat.add_zero, max_self] using hh
  let bs : DPStats := (insideEnvelope m ts.length B).add { ratMuls := m }
  have hi : ∀ qv ∈ localCandidates R H m v,
      Covers ((insideProfile (support qv)
        (Vector.ofFn fun i => linearWeight R s v * ((val qv i : ℕ) : ℚ)) ts).add
          { ratMuls := m }) bs := by
    intro qv _
    exact covers_add (insideProfile_bounds _ _ _) (by simp [Covers])
  have hsum := covers_sum ((localCandidates R H m v).map fun qv =>
      (insideProfile (support qv)
        (Vector.ofFn fun i => linearWeight R s v * ((val qv i : ℕ) : ℚ)) ts).add { ratMuls := m })
      bs (by
        intro t ht
        obtain ⟨qv, hqv, rfl⟩ := List.mem_map.mp ht
        exact hi qv hqv)
  have hraw : (nodeRaw R H s m v ts).length ≤ P :=
    (nodeRaw_length_le R H s m v ts).trans
      ((Nat.mul_le_mul_left q (tableProduct_le_safeProduct ts)).trans hqB)
  have hd := dedupProfile_bounds (nodeRaw R H s m v ts) P hraw
  have hh := covers_add hlocal (covers_add hsum hd)
  change Covers _ _ at hh
  have hlin := Nat.mul_le_mul_left ts.length hqB
  have hadd := Nat.mul_le_mul_left m hlin
  have hmul := Nat.mul_le_mul_left m hqp
  have hsqr : q * B ^ 2 ≤ P ^ 2 := by
    nlinarith [Nat.mul_le_mul_right B hqB, Nat.mul_le_mul_left P hB]
  have heq := Nat.mul_le_mul_left ts.length hsqr
  simp only [Covers, scaleEnvelope, bs, insideEnvelope, DPStats.add,
    dedupEnvelope, List.length_map] at hh
  change Covers _ (nodeEnvelope m ts.length C P)
  unfold nodeProfile
  change Covers _ _
  simp only [Covers, nodeEnvelope, DPStats.add]
  dsimp [q, B, nodeRaw] at hh hlin hadd hmul heq hB
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hh hlin hadd hmul heq ⊢
  simp only [Nat.add_zero, Nat.zero_add, Nat.zero_mul, Nat.mul_zero] at hh ⊢
  omega

def forestEnvelope (m C P a b : ℕ) : DPStats :=
  { nodeCalls := a, compositionCalls := a * C, rangeChoices := a * C,
    columnsGenerated := a * P, columnsAccepted := a * P, subsetCalls := b * P,
    insidePairs := b * P, ratAdds := m * (b * P), ratMuls := m * (a * P),
    dedupInput := (a + b) * P, dedupOutput := (a + b) * P, eqCalls := (a + b) * P ^ 2,
    maxRawTable := P, maxDedupTable := P }

theorem forestEnvelope_add (m C P a b c d : ℕ) :
    (forestEnvelope m C P a b).add (forestEnvelope m C P c d) =
      forestEnvelope m C P (a + c) (b + d) := by
  simp only [forestEnvelope, DPStats.add]
  congr 1 <;> (try simp) <;> ring

theorem covers_forest_sum {α : Type} (xs : List α) (f : α → DPStats) (a b : α → ℕ)
    (m C P : ℕ) (h : ∀ x ∈ xs, Covers (f x) (forestEnvelope m C P (a x) (b x))) :
    Covers (sumStats (xs.map f))
      (forestEnvelope m C P (xs.map a).sum (xs.map b).sum) := by
  induction xs with
  | nil => simp [sumStats, Covers, forestEnvelope]
  | cons x xs ih =>
    have hh := covers_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
    simpa only [List.map_cons, List.sum_cons, sumStats, forestEnvelope_add] using hh

noncomputable def subtreeSize (R : RootedTree (Fin N)) (v : Fin N) : ℕ := (subtree R v).card

theorem subtreeSize_pos (R : RootedTree (Fin N)) (v : Fin N) : 1 ≤ subtreeSize R v := by
  exact Finset.card_pos.mpr ⟨v, (mem_subtree _ _ _).mpr .self⟩

theorem subtreeSize_split (R : RootedTree (Fin N)) (v : Fin N) :
    subtreeSize R v = 1 + ((childrenList R v).map (subtreeSize R)).sum := by
  have hh := sum_subtree R v (fun _ => (1 : ℕ))
  simpa [subtreeSize, childrenList_sum] using hh

theorem sum_pred_sizes (R : RootedTree (Fin N)) (xs : List (Fin N)) :
    (xs.map fun u => subtreeSize R u - 1).sum + xs.length = (xs.map (subtreeSize R)).sum := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
    have := subtreeSize_pos R u
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem safeProduct_children_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (v : Fin N) :
    safeProduct ((childrenList R v).map (computeCompact R H s m)) ≤
      ∏ u ∈ R.children v, columnProduct R H m u := by
  unfold safeProduct
  rw [List.map_map, ← List.prod_toFinset _ (childrenList_nodup R v), childrenList_toFinset]
  apply Finset.prod_le_prod'
  intro u _
  exact max_le (columnProduct_pos R H m u) (computeCompact_length_le_columnProduct R H s m u)

theorem computeProfile_bounds (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m C P : ℕ)
    (hC : ∀ v, v ≠ R.root → (compositionProfile m (H v)).compositionCalls ≤ C)
    (hP : ∀ v, v ≠ R.root → columnProduct R H m v ≤ P) (v : Fin N) (hv : v ≠ R.root) :
    Covers (computeProfile R H s m v)
      (forestEnvelope m C P (subtreeSize R v) (subtreeSize R v - 1)) := by
  have hc := covers_forest_sum (childrenList R v) (computeProfile R H s m)
    (subtreeSize R) (fun u => subtreeSize R u - 1) m C P (by
      intro u hu
      have hchild := (mem_childrenList _ _ _).mp hu
      exact computeProfile_bounds R H s m C P hC hP u ((R.mem_children _ _).mp hchild).1)
  have hp : columnFactor m (H v) *
      safeProduct ((childrenList R v).map (computeCompact R H s m)) ≤ P := by
    apply (Nat.mul_le_mul_left _ (safeProduct_children_le R H s m v)).trans
    rw [← columnProduct_split]
    exact hP v hv
  have hn := nodeProfile_bounds R H s m v _ C P (hC v hv) hp
  have hh := covers_add (show Covers ({ nodeCalls := 1 } : DPStats) { nodeCalls := 1 } by
      simp [Covers]) (covers_add hc hn)
  have he (a b k : ℕ) : ({ nodeCalls := 1 } : DPStats).add
      ((forestEnvelope m C P a b).add (nodeEnvelope m k C P)) =
        forestEnvelope m C P (1 + a) (b + k) := by
    simp only [forestEnvelope, nodeEnvelope, DPStats.add]
    congr 1 <;> simp <;> ring
  rw [List.length_map, he] at hh
  have hsz := subtreeSize_split R v
  have hpred := sum_pred_sizes R (childrenList R v)
  rw [hpred, ← hsz] at hh
  have heq : ((childrenList R v).map (subtreeSize R)).sum = subtreeSize R v - 1 := by omega
  rw [heq] at hh
  rw [computeProfile]
  simpa only [List.attach_map_val] using hh
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u).mp hu)

def globalEnvelope (m C P n : ℕ) : DPStats :=
  { nodeCalls := n, compositionCalls := n * C, rangeChoices := n * C,
    columnsGenerated := n * P, columnsAccepted := n * P, subsetCalls := n * P,
    insidePairs := n * P, rootPairs := n * P, rootRejected := n * P,
    ratAdds := m * (n * P), ratMuls := m * (n * P), dedupInput := 2 * n * P,
    dedupOutput := 2 * n * P, eqCalls := 2 * n * P ^ 2, acceptCalls := P,
    maxRawTable := P, maxDedupTable := P }

theorem acceptComparisons_le {α : Type} (p : α → Bool) (xs : List α) :
    acceptComparisons p xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [acceptComparisons, List.length_cons]; split <;> omega

theorem checkCompactStats_covers (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m C : ℕ) (T : ℚ)
    (hC : ∀ v, v ≠ R.root → (compositionProfile m (H v)).compositionCalls ≤ C) :
    Covers (checkCompactStats R H s m T).stats (globalEnvelope m C (globalProduct R H m) (N - 1)) ∧
      (checkCompactStats R H s m T).stats.insidePairs +
        (checkCompactStats R H s m T).stats.rootPairs ≤ (N - 1) * globalProduct R H m := by
  let P := globalProduct R H m
  let xs := childrenList R R.root
  let ts := xs.map (computeCompact R H s m)
  have hP := globalProduct_pos R H m
  have hc := covers_forest_sum xs (computeProfile R H s m)
    (subtreeSize R) (fun u => subtreeSize R u - 1) m C P (by
      intro u hu
      exact computeProfile_bounds R H s m C P hC (columnProduct_le_globalProduct R H m) u
        ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1)
  have hb : safeProduct ts ≤ P := by
    exact (safeProduct_children_le R H s m R.root).trans_eq (root_children_product R H m)
  have hr := rootProfile_bounds ts
  have hr' : Covers (rootProfile ts) (rootEnvelope m xs.length P) := by
    have hmul := Nat.mul_le_mul_left xs.length hb
    have hadd := Nat.mul_le_mul_left m hmul
    have heq := Nat.mul_le_mul_left xs.length (Nat.pow_le_pow_left hb 2)
    simp only [Covers, rootEnvelope, ts, List.length_map] at hr ⊢
    dsimp [ts] at hmul hadd heq hb
    omega
  have ha : Covers ({ acceptCalls := acceptComparisons (acceptRootB T) (rootFold ts) } : DPStats)
      { acceptCalls := P } := by
    have hh := (acceptComparisons_le (acceptRootB T) (rootFold ts)).trans
      (rootFold_length_le_globalProduct R H s m)
    simp only [Covers]
    omega
  have hh := covers_add hc (covers_add hr' ha)
  have hsz : (xs.map (subtreeSize R)).sum = N - 1 := by
    have hsplit := subtreeSize_split R R.root
    simp only [subtreeSize, subtree_root, Finset.card_univ, Fintype.card_fin] at hsplit
    dsimp [xs]
    omega
  have hpred := sum_pred_sizes R xs
  have hcount : (xs.map fun u => subtreeSize R u - 1).sum + xs.length = N - 1 := by omega
  have hlin := congrArg (fun z => z * P) hcount
  have hadd := congrArg (fun z => m * (z * P)) hcount
  have heq := congrArg (fun z => z * P ^ 2) hcount
  rw [checkCompactStats_count]
  simp only [Covers, forestEnvelope, rootEnvelope, DPStats.add] at hh
  rw [hsz] at hh
  constructor
  · simp only [Covers, globalEnvelope, DPStats.add, Nat.mul_assoc]
    dsimp [xs, ts, P] at hh hlin hadd heq
    simp only [Nat.add_mul, Nat.mul_assoc] at hlin heq
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hadd
    simp only [Nat.add_mul, Nat.mul_assoc] at hh
    omega
  · dsimp [xs, ts, P] at hh hlin
    simp only [Nat.add_mul] at hlin
    simp only [DPStats.add]
    omega

theorem checkCompactStats_bounds (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ)
    (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    Covers (checkCompactStats R H s m T).stats
      (globalEnvelope m ((m + 1) * (U + 1) * globalProduct R H m)
        (globalProduct R H m) (N - 1)) ∧
      (checkCompactStats R H s m T).stats.insidePairs +
        (checkCompactStats R H s m T).stats.rootPairs ≤ (N - 1) * globalProduct R H m := by
  apply checkCompactStats_covers
  intro v hv
  apply (compositionProfile_calls_le m (H v)).trans
  have hfactor : columnFactor m (H v) ≤ globalProduct R H m := by
    apply le_trans ?_ (columnProduct_le_globalProduct R H m v hv)
    unfold columnProduct
    exact Finset.single_le_prod' (fun x _ => show 1 ≤ columnFactor m (H x) from le_max_left _ _)
      ((mem_subtree _ _ _).mpr .self)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hU v hv) 1)) hfactor

theorem checkCompactStats_eqCalls_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    (checkCompactStats R H s m T).stats.eqCalls ≤ (N - 1) * globalProduct R H m ^ 2 := by
  have hh := (checkCompactStats_bounds R H s m U T hU).1
  simp only [Covers, globalEnvelope, Nat.mul_assoc] at hh
  omega

theorem checkCompactStats_logicalWork_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    logicalWork (checkCompactStats R H s m T).stats ≤
      32 * N * (m + 1) * (U + 1) * globalProduct R H m ^ 2 := by
  let P := globalProduct R H m
  let A := (m + 1) * (U + 1)
  let n := N - 1
  let B := N * A * P ^ 2
  have hp : 1 ≤ P := globalProduct_pos R H m
  have hn : n ≤ N := Nat.sub_le _ _
  have hN : 1 ≤ N := by have := R.root.isLt; omega
  have ha : 1 ≤ A := by dsimp [A]; nlinarith
  have hm : m ≤ A := by dsimp [A]; nlinarith
  have hpsq : P ≤ P ^ 2 := by nlinarith
  have h1 : n ≤ B := by
    calc
      n ≤ N := hn
      _ = N * 1 * 1 := by ring
      _ ≤ B := Nat.mul_le_mul (Nat.mul_le_mul_left N ha) (by nlinarith)
  have h2 : n * (A * P) ≤ B := by
    simpa [B, Nat.mul_assoc] using Nat.mul_le_mul (Nat.mul_le_mul_right A hn) hpsq
  have h3 : n * P ≤ B := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul hn ha) hpsq
    simpa [B] using hh
  have h4 : m * (n * P) ≤ B := by
    simpa [B, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul (Nat.mul_le_mul hn hm) hpsq
  have h5 : n * P ^ 2 ≤ B := by
    have hh := Nat.mul_le_mul hn ha
    simpa [B] using Nat.mul_le_mul_right (P ^ 2) hh
  have h6 : P ≤ B := by
    have hh := Nat.mul_le_mul hN ha
    have hg := Nat.mul_le_mul hh hpsq
    simpa [B] using hg
  have hh := (checkCompactStats_bounds R H s m U T hU).1
  change Covers _ (globalEnvelope m (A * P) P n) at hh
  have he := checkCompactStats_eqCalls_le R H s m U T hU
  change _ ≤ n * P ^ 2 at he
  have hsum : logicalWork (checkCompactStats R H s m T).stats ≤ 32 * B := by
    simp only [Covers, globalEnvelope, Nat.mul_assoc] at hh
    simp only [logicalWork]
    simp only [Nat.mul_assoc] at h3
    omega
  simpa [B, A, P, Nat.mul_assoc] using hsum

theorem nodeProfile_nodeCalls (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeProfile R H s m v ts).nodeCalls = 0 := by
  have hh := nodeProfile_bounds R H s m v ts (compositionProfile m (H v)).compositionCalls
    (columnFactor m (H v) * safeProduct ts) le_rfl le_rfl
  exact Nat.eq_zero_of_le_zero hh.1

theorem sumStats_nodeCalls (ss : List DPStats) :
    (sumStats ss).nodeCalls = (ss.map DPStats.nodeCalls).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [sumStats, DPStats.add, ih]

theorem computeProfile_nodeCalls (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : (computeProfile R H s m v).nodeCalls = subtreeSize R v := by
  rw [computeProfile]
  simp only [DPStats.add, nodeProfile_nodeCalls, Nat.add_zero, sumStats_nodeCalls, List.map_map]
  rw [subtreeSize_split]
  congr 1
  have hh : (childrenList R v).attach.map (fun u => (computeProfile R H s m u.val).nodeCalls) =
      (childrenList R v).map (subtreeSize R) := by
    rw [← List.attach_map_val (l := childrenList R v)]
    apply List.map_congr_left
    intro u _
    exact computeProfile_nodeCalls R H s m u.val
  exact congrArg List.sum hh
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem checkCompactStats_nodeCalls (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : (checkCompactStats R H s m T).stats.nodeCalls = N - 1 := by
  rw [checkCompactStats_count]
  have hr := (rootProfile_bounds ((childrenList R R.root).map (computeCompact R H s m))).1
  have hz : (rootProfile ((childrenList R R.root).map (computeCompact R H s m))).nodeCalls = 0 :=
    Nat.eq_zero_of_le_zero hr
  simp only [DPStats.add, hz, Nat.add_zero, sumStats_nodeCalls, List.map_map,
    Function.comp_def, computeProfile_nodeCalls]
  have hs := subtreeSize_split R R.root
  simp only [subtreeSize, subtree_root, Finset.card_univ, Fintype.card_fin] at hs
  change N = 1 + ((childrenList R R.root).map (fun u => (subtree R u).card)).sum at hs
  change ((childrenList R R.root).map (fun u => (subtree R u).card)).sum = N - 1
  omega

end UAVProof.TreeBudgetSubtreeStats
