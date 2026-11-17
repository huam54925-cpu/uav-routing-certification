import LeanCompletion.UAV.TreeBudgetSubtreeScalarRanges

/-! Control-range transport follows actual call costs. In particular a child's
list cursors are charged to its construction and then to every ancestor call;
no capacity or total-cost assumption is introduced at the entry point. -/
namespace UAVProof.TreeBudgetSubtreeScalar
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeStats
variable {N m : Nat}

theorem filterC_callback_le {α : Type} (p : α → Counted Bool) (xs : List α)
    (x : α) (hx : x ∈ xs) : (p x).ops ≤ (filterC p xs).ops := by
  have hh : (p x).ops ≤ (xs.map fun y => (p y).ops).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [filterC_ops]; omega

theorem flatMapC_callback_le {α β : Type} (f : α → Counted (List β))
    (xs : List α) (x : α) (hx : x ∈ xs) : (f x).ops ≤ (flatMapC f xs).ops := by
  have hh : (f x).ops+3*(f x).value.length ≤
      (xs.map fun y => (f y).ops+3*(f y).value.length).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [flatMapC_ops]; omega

theorem tabulateC_callback_le {α : Type} {n : Nat} (f : Fin n → Counted α)
    (i : Fin n) : (f i).ops ≤ (tabulateC f).ops := by
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (f j).ops)
    (Finset.mem_univ i)
  rw [tabulateC_ops]; omega

theorem insideC_tail_le (a : Vector Bool m) (b : Vector Int m)
    (t : List (Entry N m)) (ts : List (List (Entry N m))) :
    (insideC a b ts).ops ≤ (insideC a b (t::ts)).ops := by
  simp only [insideC]; omega

theorem rootsC_tail_le (t : List (Entry N m)) (ts : List (List (Entry N m))) :
    (rootsC ts).ops ≤ (rootsC (t::ts)).ops := by simp only [rootsC]; omega

theorem compositionsC_child_le (m h a : Nat) (ha : a < h+1) :
    (compositionsC m (h-a)).ops ≤ (compositionsC (m+1) h).ops := by
  have hh : (compositionsC m (h-a)).ops ≤
      ((List.range (h+1)).map fun x => (compositionsC m (h-x)).ops).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩)
  rw [compositionsC_ops_step]; omega

theorem compositionsC_output_le_ops (m h : Nat) :
    (compositionsC m h).value.value.length ≤ (compositionsC m h).ops := by
  cases m with
  | zero => by_cases hh : h=0 <;> simp [compositionsC, hh]
  | succ m =>
    rw [compositionsC_value, compositionsStats_erase, compositionsC_ops_step]
    have hh := Nat.mul_le_mul_right (compositionsV (m+1) h).length
      (by omega : 1 ≤ 8*m+15)
    have ht : (compositionsV (m+1) h).length ≤ (8*m+15)*(compositionsV (m+1) h).length := by
      simpa only [one_mul] using hh
    exact ht.trans (by omega)

theorem insideC_output_le_ops (a : Vector Bool m) (b : Vector Int m)
    (ts : List (List (Entry N m))) :
    (insideC a b ts).value.value.length ≤ (insideC a b ts).ops := by
  cases ts with
  | nil => simp [insideC]
  | cons t ts =>
    let r := insideC a b ts
    let e := filterC (fun e => let c := subsetC e.key.active a; ⟨c.value,c.ops+1⟩) t
    let raw := flatMapC (fun e => mapC (insidePairC e) r.value.value) e.value
    have h := dedupC_lengths Inside.cost vectorEqC raw.value
    change (dedupC Inside.cost vectorEqC raw.value).value.value.length ≤
      r.ops+e.ops+raw.ops+(dedupC Inside.cost vectorEqC raw.value).ops+5
    omega

theorem nodeC_output_le_ops (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    (nodeC R H w m v ts).value.value.length ≤ (nodeC R H w m v ts).ops := by
  let runs := collectC ((candidatesC R H m v).value.value.map (nodeRunC v (w v) ts))
  let flat := flatMapC (fun xs => ⟨xs,1⟩) runs.value.value
  have h := dedupC_lengths Entry.key stateEqC flat.value
  change (dedupC Entry.key stateEqC flat.value).value.value.length ≤
    (candidatesC R H m v).ops+runs.ops+flat.ops+(dedupC Entry.key stateEqC flat.value).ops+5
  omega

theorem computeC_output_le_ops (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) :
    (computeC R H w m v).value.value.length ≤ (computeC R H w m v).ops := by
  rw [computeC]
  dsimp only
  exact (nodeC_output_le_ops R H w m v _).trans (by omega)

theorem computeC_child_le (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v u : Fin N) (hu : u ∈ (childrenC R v).value) :
    (computeC R H w m u).ops ≤ (computeC R H w m v).ops := by
  let rs := (childrenC R v).value.attach.map (fun x => computeC R H w m x.val)
  have hh : computeC R H w m u ∈ rs :=
    List.mem_map.mpr ⟨⟨u,hu⟩, List.mem_attach _ _, rfl⟩
  have hc := collectC_callback_le rs (computeC R H w m u) hh
  conv_rhs => rw [computeC]
  change _ ≤ (childrenC R v).ops+(collectC rs).ops+_+5
  omega

theorem computeC_descendant_le (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) {v u : Fin N}
    (h : Relation.ReflTransGen (fun x y => y ∈ (childrenC R x).value) v u) :
    (computeC R H w m u).ops ≤ (computeC R H w m v).ops := by
  induction h with
  | refl => exact le_rfl
  | @tail y z _ hy ih => exact (computeC_child_le R H w m y z hy).trans ih

theorem solveC_child_le (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (B : Int) (u : Fin N)
    (hu : u ∈ (childrenC R R.root).value) :
    (computeC R H w m u).ops ≤ (solveC R H w m B).ops := by
  let rs := (childrenC R R.root).value.map (computeC R H w m)
  have hc := collectC_callback_le rs (computeC R H w m u) (List.mem_map.mpr ⟨u,hu,rfl⟩)
  change _ ≤ (childrenC R R.root).ops+(collectC rs).ops+_+_+_+7
  omega

/-- Cursors in any descendant's ordered output table are bounded by the
actual whole run. The premises identify an executed child path, not a capacity. -/
theorem solveC_descendant_cursor (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (B : Int) (u v : Fin N)
    (hu : u ∈ (childrenC R R.root).value)
    (hv : Relation.ReflTransGen (fun x y => y ∈ (childrenC R x).value) u v)
    (k : Nat) (hk : k ≤ (computeC R H w m v).value.value.length) :
    k.size ≤ (solveC R H w m B).ops :=
  (TreeBudgetSubtreePre.size_self_le k).trans
    (hk.trans ((computeC_output_le_ops R H w m v).trans
      ((computeC_descendant_le R H w m hv).trans (solveC_child_le R H w m B u hu))))

theorem index_control_padded (N m b h c k : Nat) (hk : k ≤ N ∨ k ≤ m ∨ k ≤ c) :
    k.size+1 ≤ dpWidth N m b h c := by
  have hs := TreeBudgetSubtreePre.size_self_le k
  unfold dpWidth
  rcases hk with hk | hk | hk <;> omega

theorem mass_control_padded (N m b h c a : Nat) (ha : a.size ≤ h) :
    a.size+1 ≤ dpWidth N m b h c := by unfold dpWidth; nlinarith

theorem budget_padded (R : RootedTree (Fin N)) (s : Fin N → Rat) (T : Rat)
    (b h c : Nat) (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b)
    (hT : TreeBudgetSubtreePre.RatFits T b) :
    (prepare R s T).budget.natAbs.size+1 ≤ dpWidth N m b h c := by
  have hh := prepared_budget_bits R s T b hs hT
  unfold dpWidth; nlinarith


theorem candidate_range_padded (N m b h c a k : Nat) (ha : a.size ≤ h) (hk : k ≤ a+1) :
    k.size+1 ≤ dpWidth N m b h c := by
  have hs := (Nat.size_le_size hk).trans (TreeBudgetSubtreePre.size_add a 1)
  have hb : max a.size (Nat.size 1) ≤ h+1 := by norm_num; omega
  have ht : k.size ≤ h+2 := by omega
  unfold dpWidth; nlinarith

/-- Values actually present in counted compute tables, via complete erasure;
this includes every operand used by state-key comparisons. -/
theorem computeC_cost_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (hv : v ≠ R.root) (e : Entry N m)
    (he : e ∈ (computeC R H (val (prepare R s T).weight) m v).value.value) (i : Fin m) :
    (val e.key.cost i).natAbs.size+1 ≤ dpWidth N m b h c := by
  have hc : e ∈ compute R H (val (prepare R s T).weight) m v := by simpa using he
  exact magnitude_padded R H s T b h c hs hH _
    ((realizes_cost_bound R H _ v e (compute_realizes R H _ m v e hc) i).trans
      (subtreeMagnitude_le R H _ v hv))

theorem computeC_matrix_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (b h c : Nat) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (e : Entry N m) (he : e ∈ (computeC R H w m v).value.value)
    (i : Fin m) (x : Fin N) :
    (TreeBudgetSubtreeWitness.matrixVal e.matrix i x).size+1 ≤ dpWidth N m b h c := by
  have hc : e ∈ compute R H w m v := by simpa using he
  exact mass_control_padded N m b h c _
    ((Nat.size_le_size (realizes_coordinate_le R H w v e (compute_realizes R H w m v e hc) i x)).trans (hH x))


/-- Concrete parent-table reads implementing the tree interface. This avoids
an uncharged parent-function oracle in the scalar interpretation. -/
def childrenInputC (I : TreeBudgetSubtreePre.Input N) (v : Fin N) : Counted (List (Fin N)) :=
  let r := filterC (fun u => ⟨decide (u ≠ I.root ∧ I.parent[u] = v), 6⟩) (List.finRange N)
  ⟨r.value, r.ops+2*N+1⟩

theorem childrenInputC_eq (I : TreeBudgetSubtreePre.Input N) (R : RootedTree (Fin N))
    (hr : TreeBudgetSubtreePre.Represents I R) (v : Fin N) : childrenInputC I v = childrenC R v := by
  simp only [childrenInputC, childrenC, hr.1, hr.2]

def candidateCapInputC (I : TreeBudgetSubtreePre.Input N) (v : Fin N)
    (q : Vector Nat m) : Counted Bool :=
  if I.parent[v] = I.root then
    let r := allC (fun i => ⟨decide (val q i ≤ 1), 2⟩) (List.finRange m)
    ⟨r.value, r.ops+2*m+4⟩
  else ⟨true,3⟩

theorem candidateCapInputC_eq (I : TreeBudgetSubtreePre.Input N) (R : RootedTree (Fin N))
    (hr : TreeBudgetSubtreePre.Represents I R) (v : Fin N) (q : Vector Nat m) :
    candidateCapInputC I v q = candidateCapC R v q := by
  simp only [candidateCapInputC, candidateCapC, hr.1, hr.2]

end UAVProof.TreeBudgetSubtreeScalar
