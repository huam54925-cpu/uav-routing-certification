import LeanCompletion.UAV.TreeBudgetSubtreeIntegerDP

/-! The integer executor's measured counterparts use the same logical field
names. `ratAdds` and `ratMuls` count corresponding integer arithmetic here;
this transport makes no assertion about arithmetic latency or bit cost. -/
namespace UAVProof.TreeBudgetSubtreeInteger
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeState
variable {N m : ℕ}

theorem scanComparisons_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    scanComparisons (f x) (xs.map f) = scanComparisons x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [scanComparisons, hf.eq_iff, ih]

theorem dedupComparisons_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    dedupComparisons (xs.map f) = dedupComparisons xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, dedupComparisons, ih, List.dedup_map_of_injective hf,
      scanComparisons_map f hf]

theorem dedupProfile_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    dedupProfile (xs.map f) = dedupProfile xs := by
  simp [dedupProfile, List.dedup_map_of_injective hf, dedupComparisons_map f hf]

def insideMeasured (a : Vector Bool m) (base : Vector ℤ m) :
    List (List (IntState m)) → Measured (List (Vector ℤ m))
  | [] => ⟨[base], { maxRawTable := 1, maxDedupTable := 1 }⟩
  | t :: ts =>
    let r := insideMeasured a base ts
    let raw := (t.filter fun e => subsetB e.active a).flatMap fun e => r.value.map (add e.cost)
    let d := dedupStats raw
    ⟨d.value, r.stats.add ((insideStep m t.length raw.length).add d.stats)⟩

@[simp] theorem insideMeasured_erase (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (IntState m))) : (insideMeasured a base ts).value = inside a base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [insideMeasured, inside, ih]

theorem insideMeasured_count {D : ℕ} (hD : 0 < D) (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (IntState m))) : (insideMeasured a base ts).stats =
      (insideCostsStats a (liftCost D base) (ts.map (List.map (liftState D)))).stats := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hraw : (((t.filter fun e => subsetB e.active a).flatMap fun e =>
        (inside a base ts).map (add e.cost)).map (liftCost D)) =
        insideRaw a (t.map (liftState D))
          (insideCosts a (liftCost D base) (ts.map (List.map (liftState D)))) := by
      simp only [insideRaw, List.map_flatMap, List.filter_map, List.flatMap_map,
        List.map_map, Function.comp_def]
      apply List.flatMap_congr
      intro e _
      rw [← inside_lift_eq hD, List.map_map]
      simp [Function.comp_def, liftState]
    simp only [insideMeasured, insideCostsStats, List.map_cons, insideMeasured_erase,
      insideCostsStats_erase, dedupStats_count, ih, List.length_map]
    rw [← hraw, List.length_map, dedupProfile_map _ (liftCost_injective hD)]

def rootMeasured : List (List (IntState m)) → Measured (List (IntRoot m))
  | [] => ⟨[rootZero m], { maxRawTable := 1, maxDedupTable := 1 }⟩
  | t :: ts =>
    let r := rootMeasured ts
    let raw := t.flatMap fun e => r.value.map fun b => rootAdd b e
    let kept := raw.filter cap
    let d := dedupStats kept
    ⟨d.value, r.stats.add ((rootStep m raw.length kept.length).add d.stats)⟩

@[simp] theorem rootMeasured_erase (ts : List (List (IntState m))) :
    (rootMeasured ts).value = rootFold ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [rootMeasured, rootFold, ih]

theorem rootMeasured_count {D : ℕ} (hD : 0 < D) (ts : List (List (IntState m))) :
    (rootMeasured ts).stats = (rootFoldStats (ts.map (List.map (liftState D)))).stats := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hraw : ((t.flatMap fun e => (rootFold ts).map fun b => rootAdd b e).map (liftRoot D)) =
        rootRaw (t.map (liftState D))
          (TreeBudgetSubtreeExecutable.rootFold (ts.map (List.map (liftState D)))) := by
      simp only [rootRaw, List.map_flatMap, List.flatMap_map, List.map_map]
      apply List.flatMap_congr
      intro e _
      rw [← rootFold_lift_eq hD, List.map_map]
      simp [Function.comp_def]
    have hfilter (xs : List (IntRoot m)) : (xs.map (liftRoot D)).filter rootCapB =
        (xs.filter cap).map (liftRoot D) := by rw [List.filter_map]; rfl
    simp only [rootMeasured, rootFoldStats, List.map_cons, rootMeasured_erase,
      rootFoldStats_erase, dedupStats_count, ih]
    rw [← hraw, hfilter, List.length_map, List.length_map,
      dedupProfile_map _ (liftRoot_injective hD)]

def nodeMeasured (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (IntState m))) : Measured (List (IntState m)) :=
  let qs := localCandidatesStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideMeasured (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts
    (r.value.map fun b => (⟨support q, b⟩ : IntState m), r.stats.add { ratMuls := m })
  let d := dedupStats (rs.flatMap Prod.fst)
  ⟨d.value, qs.stats.add ((sumStats (rs.map Prod.snd)).add d.stats)⟩

@[simp] theorem nodeMeasured_erase (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (m : ℕ) (v : Fin N) (ts : List (List (IntState m))) :
    (nodeMeasured R H w m v ts).value = node R H w m v ts := by
  simp [nodeMeasured, node, List.flatMap_map]

theorem nodeMeasured_count {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (v : Fin N)
    (hw : (w v : ℚ) = (D : ℚ) * linearWeight R s v) (ts : List (List (IntState m))) :
    (nodeMeasured R H w m v ts).stats =
      (nodeTableStats R H s m v (ts.map (List.map (liftState D)))).stats := by
  have hi (q : Vector ℕ m) := insideMeasured_count hD (support q)
    (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts
  simp only [lift_initial hD (w v) _ hw] at hi
  simp only [nodeMeasured, nodeTableStats, localCandidatesStats_erase, List.map_map,
    Function.comp_def, hi, dedupStats_count, insideMeasured_erase, insideCostsStats_erase,
    List.flatMap_map]
  congr 2
  rw [← dedupProfile_map (liftState D) (liftState_injective hD)]
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  rw [List.map_map, ← lift_initial hD (w v) _ hw q, ← inside_lift_eq hD, List.map_map]
  rfl

def computeMeasured (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) : Measured (List (IntState m)) :=
  let cs := collect ((childrenList R v).attach.map fun u => computeMeasured R H w m u.val)
  let r := nodeMeasured R H w m v cs.value
  ⟨r.value, ({ nodeCalls := 1 } : DPStats).add (cs.stats.add r.stats)⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeMeasured_erase (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (m : ℕ) (v : Fin N) :
    (computeMeasured R H w m v).value = compute R H w m v := by
  rw [computeMeasured, compute]
  simp only [collect, List.map_map, nodeMeasured_erase, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u _
  exact computeMeasured_erase R H w m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem computeMeasured_count {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (v : Fin N)
    (hv : v ≠ R.root) (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    (computeMeasured R H w m v).stats = (computeCompactStats R H s m v).stats := by
  rw [computeMeasured, computeCompactStats]
  simp only [collect, List.map_map, Function.comp_def, computeMeasured_erase,
    computeCompactStats_erase]
  have ht : ((childrenList R v).attach.map (fun u => computeCompact R H s m u.val)) =
      ((childrenList R v).attach.map (fun u => compute R H w m u.val)).map (List.map (liftState D)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro u _
    exact (compute_lift_eq hD R H s w m u.val
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp u.property)).1 hw).symm
  rw [ht, ← nodeMeasured_count hD R H s w m v (hw v hv)]
  congr 3
  apply List.map_congr_left
  intro u _
  exact computeMeasured_count hD R H s w m u.val
    ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp u.property)).1 hw
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkMeasured (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) : Measured Bool :=
  let cs := collect ((childrenList R R.root).map (computeMeasured R H w m))
  let r := rootMeasured cs.value
  let a := anyCounted (accept B) r.value
  ⟨a.1, cs.stats.add (r.stats.add { acceptCalls := a.2 })⟩

@[simp] theorem checkMeasured_erase (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (m : ℕ) (B : ℤ) : (checkMeasured R H w m B).value = check R H w m B := by
  simp [checkMeasured, check, collect, List.map_map, Function.comp_def, (anyCounted_spec _ _).1]

theorem anyCounted_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    anyCounted p (xs.map f) = anyCounted (fun x => p (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [anyCounted, ih]

theorem checkMeasured_count {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (T : ℚ)
    (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    (checkMeasured R H w m (floorBudget D T)).stats = (checkCompactStats R H s m T).stats := by
  have ht : (childrenList R R.root).map (computeCompact R H s m) =
      ((childrenList R R.root).map (compute R H w m)).map (List.map (liftState D)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro u hu
    exact (compute_lift_eq hD R H s w m u
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1 hw).symm
  have hs : (childrenList R R.root).map (fun u => (computeCompactStats R H s m u).stats) =
      (childrenList R R.root).map (fun u => (computeMeasured R H w m u).stats) := by
    apply List.map_congr_left
    intro u hu
    exact (computeMeasured_count hD R H s w m u
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1 hw).symm
  simp only [checkMeasured, checkCompactStats, collect, List.map_map, Function.comp_def,
    computeMeasured_erase, computeCompactStats_erase, rootMeasured_erase, rootFoldStats_erase]
  rw [hs, ht, ← rootMeasured_count hD, ← rootFold_lift_eq hD, anyCounted_map]
  simp only [← accept_lift_eq hD]

end UAVProof.TreeBudgetSubtreeInteger
