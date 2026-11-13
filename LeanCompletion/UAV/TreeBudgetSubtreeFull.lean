import LeanCompletion.UAV.TreeBudgetSubtreeStats

/-! A full-boundary reference retaining every top-edge multiplicity. Linear
cost coordinates keep arithmetic identical to the compact executor; together
with q they are bijective to the original (q,c) coordinates. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
variable {N m : Nat}

structure ExecFullState (m : Nat) where
  q : Vector Nat m
  cost : Vector Rat m
  deriving DecidableEq, Inhabited

def projectFull (e : ExecFullState m) : ExecCompactState m := ⟨support e.q, e.cost⟩

def originalCost (p : Rat) (e : ExecFullState m) : Vector Rat m :=
  Vector.ofFn fun i => val e.cost i - p * ((val e.q i : Nat) : Rat)

theorem originalCost_roundtrip (p : Rat) (e : ExecFullState m) (i : Fin m) :
    val (originalCost p e) i + p * ((val e.q i : Nat) : Rat) = val e.cost i := by
  simp [originalCost]

def nodeFull (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (tables : List (List (ExecFullState m))) : List (ExecFullState m) :=
  let projected := tables.map (List.map projectFull)
  ((localCandidates R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat))
      projected).map fun b => ⟨q, b⟩).dedup

def computeFull (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : List (ExecFullState m) :=
  let ts := (childrenList R v).attach.map fun u => computeFull R H s m u.val
  nodeFull R H s m v ts
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem computeFull_eq (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : computeFull R H s m v =
      nodeFull R H s m v ((childrenList R v).map (computeFull R H s m)) := by
  rw [computeFull]; simp only [List.attach_map_val]

theorem insideCosts_congr_mem {α : Type} (a : Vector Bool m) (base : Vector Rat m)
    (us : List α) (f g : α → List (ExecCompactState m))
    (h : ∀ u ∈ us, ∀ e, e ∈ f u ↔ e ∈ g u) (b : Vector Rat m) :
    b ∈ insideCosts a base (us.map f) ↔ b ∈ insideCosts a base (us.map g) := by
  induction us generalizing b with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, insideCosts, List.mem_dedup, List.mem_flatMap,
      List.mem_filter, List.mem_map]
    have ht := ih (fun x hx => h x (by simp [hx]))
    constructor
    · rintro ⟨e, ⟨he, ha⟩, r, hr, hb⟩
      exact ⟨e, ⟨(h u (by simp) e).mp he, ha⟩, r, (ht r).mp hr, hb⟩
    · rintro ⟨e, ⟨he, ha⟩, r, hr, hb⟩
      exact ⟨e, ⟨(h u (by simp) e).mpr he, ha⟩, r, (ht r).mpr hr, hb⟩

theorem nodeTable_congr_mem {α : Type} (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (v : Fin N) (us : List α) (f g : α → List (ExecCompactState m))
    (h : ∀ u ∈ us, ∀ e, e ∈ f u ↔ e ∈ g u) (e : ExecCompactState m) :
    e ∈ nodeTable R H s m v (us.map f) ↔ e ∈ nodeTable R H s m v (us.map g) := by
  simp only [nodeTable, List.mem_dedup, List.mem_flatMap, List.mem_map]
  constructor <;> rintro ⟨q, hq, b, hb, he⟩
  · exact ⟨q, hq, b, (insideCosts_congr_mem _ _ us f g h b).mp hb, he⟩
  · exact ⟨q, hq, b, (insideCosts_congr_mem _ _ us f g h b).mpr hb, he⟩

theorem nodeFull_project_mem (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (v : Fin N) (ts : List (List (ExecFullState m)))
    (e : ExecCompactState m) :
    e ∈ (nodeFull R H s m v ts).map projectFull ↔
      e ∈ nodeTable R H s m v (ts.map (List.map projectFull)) := by
  simp only [nodeFull, nodeTable, List.mem_map, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨q, hq, b, hb, rfl⟩, rfl⟩
    exact ⟨q, hq, b, hb, rfl⟩
  · rintro ⟨q, hq, b, hb, rfl⟩
    exact ⟨⟨q, b⟩, ⟨q, hq, b, hb, rfl⟩, rfl⟩

theorem computeFull_project_mem (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (e : ExecCompactState m) :
    e ∈ (computeFull R H s m v).map projectFull ↔ e ∈ computeCompact R H s m v := by
  rw [computeFull_eq, nodeFull_project_mem, computeCompact_eq]
  simp only [List.map_map, Function.comp_def]
  apply nodeTable_congr_mem
  intro u hu x
  exact computeFull_project_mem R H s m u x
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u).mp hu)

theorem rootFold_congr_mem {α : Type} (us : List α) (f g : α → List (ExecCompactState m))
    (h : ∀ u ∈ us, ∀ e, e ∈ f u ↔ e ∈ g u) (b : ExecRootState m) :
    b ∈ rootFold (us.map f) ↔ b ∈ rootFold (us.map g) := by
  induction us generalizing b with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, rootFold, List.mem_dedup, List.mem_filter,
      List.mem_flatMap, List.mem_map]
    have ht := ih (fun x hx => h x (by simp [hx]))
    constructor
    · rintro ⟨⟨e, he, r, hr, hb⟩, hc⟩
      exact ⟨⟨e, (h u (by simp) e).mp he, r, (ht r).mp hr, hb⟩, hc⟩
    · rintro ⟨⟨e, he, r, hr, hb⟩, hc⟩
      exact ⟨⟨e, (h u (by simp) e).mpr he, r, (ht r).mpr hr, hb⟩, hc⟩

def checkFull (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) : Bool :=
  (rootFold ((childrenList R R.root).map fun u =>
    (computeFull R H s m u).map projectFull)).any (acceptRootB T)

theorem checkFull_eq (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) :
    checkFull R H s m T = checkCompact R H s m T := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkFull, checkCompact, List.any_eq_true]
  have h := rootFold_congr_mem (childrenList R R.root)
    (fun u => (computeFull R H s m u).map projectFull) (computeCompact R H s m)
    (fun u _ e => computeFull_project_mem R H s m u e)
  exact exists_congr fun b => and_congr_left fun _ => h b

def nodeFullStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (ts : List (List (ExecFullState m))) :
    Measured (List (ExecFullState m)) :=
  let projected := ts.map (List.map projectFull)
  let qs := localCandidatesStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideCostsStats (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat))
      projected
    (r.value.map fun b => (⟨q, b⟩ : ExecFullState m), r.stats.add { ratMuls := m })
  let d := dedupStats (rs.flatMap Prod.fst)
  ⟨d.value, qs.stats.add ((sumStats (rs.map Prod.snd)).add d.stats)⟩

@[simp] theorem nodeFullStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (ts : List (List (ExecFullState m))) :
    (nodeFullStats R H s m v ts).value = nodeFull R H s m v ts := by
  simp [nodeFullStats, nodeFull, List.flatMap_map]

def computeFullStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : Measured (List (ExecFullState m)) :=
  let cs := collect ((childrenList R v).attach.map fun u => computeFullStats R H s m u.val)
  let r := nodeFullStats R H s m v cs.value
  ⟨r.value, ({ nodeCalls := 1 } : DPStats).add (cs.stats.add r.stats)⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeFullStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeFullStats R H s m v).value = computeFull R H s m v := by
  rw [computeFullStats, computeFull_eq]
  simp only [collect, List.map_map, Function.comp_def, nodeFullStats_erase]
  congr 1
  rw [← List.attach_map_val (l := childrenList R v)]
  apply List.map_congr_left
  intro u _
  exact computeFullStats_erase R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkFullStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) : Measured Bool :=
  let cs := collect ((childrenList R R.root).map (computeFullStats R H s m))
  let r := rootFoldStats (cs.value.map (List.map projectFull))
  let a := anyCounted (acceptRootB T) r.value
  ⟨a.1, cs.stats.add (r.stats.add { acceptCalls := a.2 })⟩

theorem checkFullStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkFullStats R H s m T).value = checkFull R H s m T := by
  simp [checkFullStats, collect, List.map_map, Function.comp_def, checkFull,
    (anyCounted_spec _ _).1]

end UAVProof.TreeBudgetSubtreeStats
