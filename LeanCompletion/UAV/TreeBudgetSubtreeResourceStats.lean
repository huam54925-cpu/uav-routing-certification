import LeanCompletion.UAV.TreeBudgetSubtreeResourceExecutorSeed

/-! Ordered key projection and all-field statistical erasure of the single-run
integer witness executor. No injectivity of payload keys is assumed. -/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeStats TreeBudgetSubtreeIntegerWitnessSeed
variable {N m : ℕ}

theorem inside_keys (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) :
    (inside a base ts).map Inside.cost =
      TreeBudgetSubtreeInteger.inside a base (ts.map (List.map Entry.key)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [inside, TreeBudgetSubtreeWitness.dedupKey_map,
      TreeBudgetSubtreeInteger.inside, List.map_cons, List.map_flatMap,
      List.map_map, List.filter_map, List.flatMap_map, Function.comp_def]
    congr 1
    apply List.flatMap_congr
    intro e _
    rw [← ih, List.map_map]
    rfl

theorem node_keys (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) :
    (node R H w m v ts).map Entry.key =
      TreeBudgetSubtreeInteger.node R H w m v (ts.map (List.map Entry.key)) := by
  simp only [node, TreeBudgetSubtreeInteger.node, TreeBudgetSubtreeWitness.dedupKey_map,
    List.map_flatMap, List.map_map, Function.comp_def]
  congr 1
  apply List.flatMap_congr
  intro q _
  rw [← inside_keys, List.map_map]
  rfl

theorem compute_keys (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) :
    (compute R H w m v).map Entry.key = TreeBudgetSubtreeInteger.compute R H w m v := by
  rw [compute, node_keys, TreeBudgetSubtreeInteger.compute]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro u _
  exact compute_keys R H w m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem roots_keys (ts : List (List (Entry N m))) :
    (roots ts).map Root.key =
      TreeBudgetSubtreeInteger.rootFold (ts.map (List.map Entry.key)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hf (xs : List (Root N m)) :
        (xs.filter fun r => TreeBudgetSubtreeInteger.cap r.key).map Root.key =
          (xs.map Root.key).filter TreeBudgetSubtreeInteger.cap := by
      rw [List.filter_map]
      rfl
    simp only [roots, TreeBudgetSubtreeInteger.rootFold, List.map_cons,
      TreeBudgetSubtreeWitness.dedupKey_map, hf]
    congr 1
    congr 1
    rw [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    intro e _
    rw [List.map_map, ← ih, List.map_map]
    rfl

theorem insideR_keyStats (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) :
    (insideR a base ts).keyStats =
      (TreeBudgetSubtreeInteger.insideMeasured a base (ts.map (List.map Entry.key))).stats := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hraw : (((t.filter fun e => subsetB e.key.active a).flatMap fun e =>
        (inside a base ts).map fun r =>
          (⟨TreeBudgetSubtreeInteger.add e.key.cost r.cost, e :: r.picks⟩ : Inside N m)).map
            Inside.cost) =
        (((t.map Entry.key).filter fun e => subsetB e.active a).flatMap fun e =>
          (TreeBudgetSubtreeInteger.inside a base (ts.map (List.map Entry.key))).map
            (TreeBudgetSubtreeInteger.add e.cost)) := by
      simp only [List.map_flatMap, List.filter_map, List.flatMap_map, List.map_map,
        Function.comp_def]
      apply List.flatMap_congr
      intro e _
      rw [← inside_keys, List.map_map]
      rfl
    simp only [insideR, TreeBudgetSubtreeInteger.insideMeasured, List.map_cons,
      insideR_erase, TreeBudgetSubtreeInteger.insideMeasured_erase,
      dedupResource_keyStats, dedupStats_count, ih, List.length_map]
    rw [← hraw, List.length_map]

theorem nodeR_keyStats (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) :
    (nodeR R H w m v ts).keyStats =
      (TreeBudgetSubtreeInteger.nodeMeasured R H w m v (ts.map (List.map Entry.key))).stats := by
  simp only [nodeR, TreeBudgetSubtreeInteger.nodeMeasured, List.map_map,
    Function.comp_def, insideR_keyStats, dedupResource_keyStats, dedupStats_count,
    insideR_erase, TreeBudgetSubtreeInteger.insideMeasured_erase, List.flatMap_map]
  congr 2
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  rw [List.map_map, ← inside_keys, List.map_map]
  rfl

theorem computeR_keyStats (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) :
    (computeR R H w m v).keyStats =
      (TreeBudgetSubtreeInteger.computeMeasured R H w m v).stats := by
  rw [computeR, TreeBudgetSubtreeInteger.computeMeasured]
  simp only [collectR, collect, List.map_map, Function.comp_def, computeR_erase,
    TreeBudgetSubtreeInteger.computeMeasured_erase]
  have ht : ((childrenList R v).attach.map fun u => TreeBudgetSubtreeInteger.compute R H w m u.val) =
      ((childrenList R v).attach.map fun u => compute R H w m u.val).map (List.map Entry.key) := by
    simp only [List.map_map, Function.comp_def, compute_keys]
  rw [ht, ← nodeR_keyStats]
  congr 3
  apply List.map_congr_left
  intro u _
  exact computeR_keyStats R H w m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem rootsR_keyStats (ts : List (List (Entry N m))) :
    (rootsR ts).keyStats =
      (TreeBudgetSubtreeInteger.rootMeasured (ts.map (List.map Entry.key))).stats := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hraw : ((t.flatMap fun e => (roots ts).map fun r =>
        (⟨TreeBudgetSubtreeInteger.rootAdd r.key e.key, e :: r.picks⟩ : Root N m)).map Root.key) =
        ((t.map Entry.key).flatMap fun e =>
          (TreeBudgetSubtreeInteger.rootFold (ts.map (List.map Entry.key))).map fun r =>
            TreeBudgetSubtreeInteger.rootAdd r e) := by
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro e _
      rw [List.map_map, ← roots_keys, List.map_map]
      rfl
    simp only [rootsR, TreeBudgetSubtreeInteger.rootMeasured, List.map_cons,
      rootsR_erase, TreeBudgetSubtreeInteger.rootMeasured_erase, dedupResource_keyStats,
      dedupStats_count, ih]
    rw [← hraw, List.filter_map, List.length_map, List.length_map]
    rfl

theorem solveR_keyStats (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) : (solveR R H w m B).keyStats =
      (TreeBudgetSubtreeInteger.checkMeasured R H w m B).stats := by
  simp only [solveR, TreeBudgetSubtreeInteger.checkMeasured, collectR, collect,
    List.map_map, Function.comp_def, computeR_erase, computeR_keyStats,
    TreeBudgetSubtreeInteger.computeMeasured_erase, rootsR_erase,
    TreeBudgetSubtreeInteger.rootMeasured_erase, findCounted_count_eq_any]
  have ht : (childrenList R R.root).map (TreeBudgetSubtreeInteger.compute R H w m) =
      ((childrenList R R.root).map (compute R H w m)).map (List.map Entry.key) := by
    simp only [List.map_map, Function.comp_def, compute_keys]
  rw [ht, ← rootsR_keyStats, ← roots_keys, TreeBudgetSubtreeInteger.anyCounted_map]

theorem solveAutoR_keyStats (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    (solveAutoR R H s m T).keyStats = (checkCompactStats R H s m T).stats := by
  simp only [solveAutoR, solveR_keyStats, TreeBudgetSubtreeAutoScaleSeed.prepare_budget]
  exact TreeBudgetSubtreeInteger.checkMeasured_count
    (TreeBudgetSubtreeAutoScaleSeed.prepare_pos R s T) R H s _ m T
    (TreeBudgetSubtreeAutoScaleSeed.prepare_weight R s T)

end UAVProof.TreeBudgetSubtreeResourceSeed
