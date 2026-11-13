import LeanCompletion.UAV.TreeBudgetSubtreeStatsPrimitives

/-! The instrumented baseline preserves exact list order, including work on
empty-prefix folds and arithmetic on subsequently rejected root pairs. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
variable {N m : Nat}

def compositionsStats : (m : Nat) → Nat → Measured (List (Vector Nat m))
  | 0, h => ⟨if h = 0 then [emptyV] else [], { compositionCalls := 1 }⟩
  | m + 1, h =>
    let rs := (List.range (h + 1)).map fun a =>
      let r := compositionsStats m (h - a)
      (r.value.map (consV a), r.stats)
    ⟨rs.flatMap Prod.fst, ({ compositionCalls := 1, rangeChoices := h + 1 } : DPStats).add
      (sumStats (rs.map Prod.snd))⟩

def compositionProfile : Nat → Nat → DPStats
  | 0, _ => { compositionCalls := 1 }
  | m + 1, h => ({ compositionCalls := 1, rangeChoices := h + 1 } : DPStats).add
      (sumStats ((List.range (h + 1)).map fun a => compositionProfile m (h - a)))

@[simp] theorem compositionsStats_erase (m h : Nat) :
    (compositionsStats m h).value = compositionsV m h := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih => simp [compositionsStats, compositionsV, List.flatMap_map, ih]

@[simp] theorem compositionsStats_count (m h : Nat) :
    (compositionsStats m h).stats = compositionProfile m h := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih => simp [compositionsStats, compositionProfile, List.map_map, Function.comp_def, ih]

def localCandidatesStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (m : Nat)
    (v : Fin N) : Measured (List (Vector Nat m)) :=
  let r := compositionsStats m (H v)
  let qs := r.value.filter fun q => decide (R.parent v = R.root → ∀ i, val q i ≤ 1)
  ⟨qs, r.stats.add { columnsGenerated := r.value.length, columnsAccepted := qs.length }⟩

@[simp] theorem localCandidatesStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) :
    (localCandidatesStats R H m v).value = localCandidates R H m v := by
  simp [localCandidatesStats, localCandidates]

theorem localCandidatesStats_count (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) :
    (localCandidatesStats R H m v).stats = (compositionProfile m (H v)).add
      { columnsGenerated := (compositionsV m (H v)).length,
        columnsAccepted := (localCandidates R H m v).length } := by
  simp [localCandidatesStats, localCandidates]

def insideRaw (a : Vector Bool m) (t : List (ExecCompactState m))
    (r : List (Vector Rat m)) : List (Vector Rat m) :=
  (t.filter fun e => subsetB e.active a).flatMap fun e => r.map (addCost e.cost)

theorem length_product {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → γ) :
    (xs.flatMap fun x => ys.map (f x)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem insideRaw_length (a : Vector Bool m) (t : List (ExecCompactState m))
    (r : List (Vector Rat m)) :
    (insideRaw a t r).length = (t.filter fun e => subsetB e.active a).length * r.length :=
  length_product _ _ _

def insideStep (m checks pairs : Nat) : DPStats :=
  { subsetCalls := checks, insidePairs := pairs, ratAdds := m * pairs }

def insideCostsStats (a : Vector Bool m) (base : Vector Rat m) :
    List (List (ExecCompactState m)) → Measured (List (Vector Rat m))
  | [] => ⟨[base], { maxRawTable := 1, maxDedupTable := 1 }⟩
  | t :: ts =>
    let r := insideCostsStats a base ts
    let raw := insideRaw a t r.value
    let d := dedupStats raw
    ⟨d.value, r.stats.add ((insideStep m t.length raw.length).add d.stats)⟩

def insideProfile (a : Vector Bool m) (base : Vector Rat m) :
    List (List (ExecCompactState m)) → DPStats
  | [] => { maxRawTable := 1, maxDedupTable := 1 }
  | t :: ts =>
    let r := insideCosts a base ts
    let raw := insideRaw a t r
    (insideProfile a base ts).add
      ((insideStep m t.length ((t.filter fun e => subsetB e.active a).length * r.length)).add
        (dedupProfile raw))

@[simp] theorem insideCostsStats_erase (a : Vector Bool m) (base : Vector Rat m)
    (ts : List (List (ExecCompactState m))) :
    (insideCostsStats a base ts).value = insideCosts a base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [insideCostsStats, insideCosts, insideRaw, ih]

theorem insideCostsStats_count (a : Vector Bool m) (base : Vector Rat m)
    (ts : List (List (ExecCompactState m))) :
    (insideCostsStats a base ts).stats = insideProfile a base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [insideCostsStats, insideProfile, ih, insideRaw_length]

def rootRaw (t : List (ExecCompactState m)) (r : List (ExecRootState m)) :
    List (ExecRootState m) := t.flatMap fun e => r.map fun b => rootAdd b e

theorem rootRaw_length (t : List (ExecCompactState m)) (r : List (ExecRootState m)) :
    (rootRaw t r).length = t.length * r.length := length_product _ _ _

def rootStep (m pairs kept : Nat) : DPStats :=
  { rootPairs := pairs, rootRejected := pairs - kept, ratAdds := m * pairs,
    maxRawTable := pairs }

def rootFoldStats : List (List (ExecCompactState m)) → Measured (List (ExecRootState m))
  | [] => ⟨[rootZero m], { maxRawTable := 1, maxDedupTable := 1 }⟩
  | t :: ts =>
    let r := rootFoldStats ts
    let raw := rootRaw t r.value
    let kept := raw.filter rootCapB
    let d := dedupStats kept
    ⟨d.value, r.stats.add ((rootStep m raw.length kept.length).add d.stats)⟩

def rootProfile : List (List (ExecCompactState m)) → DPStats
  | [] => { maxRawTable := 1, maxDedupTable := 1 }
  | t :: ts =>
    let r := rootFold ts
    let kept := (rootRaw t r).filter rootCapB
    (rootProfile ts).add ((rootStep m (t.length * r.length) kept.length).add (dedupProfile kept))

@[simp] theorem rootFoldStats_erase (ts : List (List (ExecCompactState m))) :
    (rootFoldStats ts).value = rootFold ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [rootFoldStats, rootFold, rootRaw, ih]

theorem rootFoldStats_count (ts : List (List (ExecCompactState m))) :
    (rootFoldStats ts).stats = rootProfile ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [rootFoldStats, rootProfile, ih, rootRaw_length]

theorem rootStep_conservation (t : List (ExecCompactState m)) (r : List (ExecRootState m)) :
    (rootStep m (rootRaw t r).length ((rootRaw t r).filter rootCapB).length).rootRejected +
      ((rootRaw t r).filter rootCapB).length = t.length * r.length := by
  have h := List.length_filter_le rootCapB (rootRaw t r)
  simp only [rootStep]
  rw [← rootRaw_length]
  omega

def nodeTableStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (tables : List (List (ExecCompactState m))) :
    Measured (List (ExecCompactState m)) :=
  let qs := localCandidatesStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideCostsStats (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat)) tables
    (r.value.map fun b => (⟨support q, b⟩ : ExecCompactState m),
      r.stats.add { ratMuls := m })
  let d := dedupStats (rs.flatMap Prod.fst)
  ⟨d.value, qs.stats.add ((sumStats (rs.map Prod.snd)).add d.stats)⟩

@[simp] theorem nodeTableStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeTableStats R H s m v ts).value = nodeTable R H s m v ts := by
  simp [nodeTableStats, nodeTable, List.flatMap_map]

def nodeProfile (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (tables : List (List (ExecCompactState m))) : DPStats :=
  let qs := localCandidates R H m v
  let base := fun q => Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat)
  let raw := qs.flatMap fun q => (insideCosts (support q) (base q) tables).map
    fun b => (⟨support q, b⟩ : ExecCompactState m)
  ((compositionProfile m (H v)).add
    { columnsGenerated := (compositionsV m (H v)).length, columnsAccepted := qs.length }).add
    ((sumStats (qs.map fun q => (insideProfile (support q) (base q) tables).add
      { ratMuls := m })).add (dedupProfile raw))

theorem nodeTableStats_count (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeTableStats R H s m v ts).stats = nodeProfile R H s m v ts := by
  simp [nodeTableStats, nodeProfile, localCandidatesStats_count, insideCostsStats_count,
    List.map_map, List.flatMap_map, Function.comp_def]

def computeCompactStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : Measured (List (ExecCompactState m)) :=
  let cs := collect ((childrenList R v).attach.map fun u => computeCompactStats R H s m u.val)
  let r := nodeTableStats R H s m v cs.value
  ⟨r.value, ({ nodeCalls := 1 } : DPStats).add (cs.stats.add r.stats)⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeCompactStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeCompactStats R H s m v).value = computeCompact R H s m v := by
  rw [computeCompactStats, computeCompact_eq]
  simp only [collect, List.map_map, Function.comp_def, nodeTableStats_erase]
  congr 1
  rw [← List.attach_map_val (l := childrenList R v)]
  apply List.map_congr_left
  intro u _
  exact computeCompactStats_erase R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def computeProfile (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : DPStats :=
  ({ nodeCalls := 1 } : DPStats).add
    ((sumStats ((childrenList R v).attach.map fun u => computeProfile R H s m u.val)).add
      (nodeProfile R H s m v ((childrenList R v).map (computeCompact R H s m))))
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem computeCompactStats_count (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeCompactStats R H s m v).stats = computeProfile R H s m v := by
  rw [computeCompactStats, computeProfile]
  simp only [collect, List.map_map, Function.comp_def, nodeTableStats_count]
  have hv : ((childrenList R v).attach.map fun u =>
      (computeCompactStats R H s m u.val).value) =
      (childrenList R v).map (computeCompact R H s m) := by
    simp only [computeCompactStats_erase, List.attach_map_val]
  rw [hv]
  congr 3
  apply List.map_congr_left
  intro u _
  exact computeCompactStats_count R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkCompactStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) : Measured Bool :=
  let cs := collect ((childrenList R R.root).map (computeCompactStats R H s m))
  let r := rootFoldStats cs.value
  let a := anyCounted (acceptRootB T) r.value
  ⟨a.1, cs.stats.add (r.stats.add { acceptCalls := a.2 })⟩

theorem checkCompactStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkCompactStats R H s m T).value = checkCompact R H s m T := by
  simp [checkCompactStats, collect, List.map_map, Function.comp_def, checkCompact,
    (anyCounted_spec _ _).1]

theorem checkCompactStats_count (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkCompactStats R H s m T).stats =
      (sumStats ((childrenList R R.root).map (computeProfile R H s m))).add
      ((rootProfile ((childrenList R R.root).map (computeCompact R H s m))).add
        { acceptCalls := acceptComparisons (acceptRootB T)
            (rootFold ((childrenList R R.root).map (computeCompact R H s m))) }) := by
  simp [checkCompactStats, collect, List.map_map, Function.comp_def,
    rootFoldStats_count, computeCompactStats_count, (anyCounted_spec _ _).2]

end UAVProof.TreeBudgetSubtreeStats
