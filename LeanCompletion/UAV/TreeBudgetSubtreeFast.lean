import LeanCompletion.UAV.TreeBudgetSubtreeStats

/-! One isolated optimization: bypass the range only when the global route
dimension is one. Higher-dimensional enumeration is deliberately unchanged. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
variable {N m : Nat}

theorem compositionsV_one (h : Nat) :
    compositionsV 1 h = [Vector.ofFn (fun _ : Fin 1 => h)] := by
  have hempty : ((List.range h).flatMap fun a =>
      (compositionsV 0 (h - a)).map (consV a)) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro a ha
    have hl := List.mem_range.mp ha
    have hn : h - a ≠ 0 := by omega
    simp [compositionsV, hn]
  rw [compositionsV, List.range_succ, List.flatMap_append, hempty]
  simp only [List.nil_append, List.flatMap_singleton, Nat.sub_self, compositionsV]
  congr 1

def compositionsFast (m h : Nat) : List (Vector Nat m) :=
  if m = 1 then [Vector.ofFn (fun _ => h)] else compositionsV m h

@[simp] theorem compositionsFast_eq (m h : Nat) : compositionsFast m h = compositionsV m h := by
  by_cases hm : m = 1
  · subst m; simp [compositionsFast, compositionsV_one]
  · simp [compositionsFast, hm]

def compositionsFastStats (m h : Nat) : Measured (List (Vector Nat m)) :=
  if m = 1 then ⟨[Vector.ofFn (fun _ => h)], { compositionCalls := 1 }⟩
  else compositionsStats m h

@[simp] theorem compositionsFastStats_erase (m h : Nat) :
    (compositionsFastStats m h).value = compositionsFast m h := by
  by_cases hm : m = 1 <;> simp [compositionsFastStats, compositionsFast, hm]

theorem compositionsFastStats_one (h : Nat) :
    (compositionsFastStats 1 h).stats = { compositionCalls := 1 } := by
  simp [compositionsFastStats]

def localFast (R : RootedTree (Fin N)) (H : Fin N → Nat) (m : Nat) (v : Fin N) :
    List (Vector Nat m) :=
  (compositionsFast m (H v)).filter fun q =>
    decide (R.parent v = R.root → ∀ i, val q i ≤ 1)

@[simp] theorem localFast_eq (R : RootedTree (Fin N)) (H : Fin N → Nat) (m : Nat) (v : Fin N) :
    localFast R H m v = localCandidates R H m v := by simp [localFast, localCandidates]

def nodeFast (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (tables : List (List (ExecCompactState m))) : List (ExecCompactState m) :=
  ((localFast R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn (fun i => linearWeight R s v * ((val q i : ℕ) : ℚ))) tables).map
      (fun b => ⟨support q, b⟩)).dedup

def computeFast (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : List (ExecCompactState m) :=
  let tables := (childrenList R v).attach.map fun u => computeFast R H s m u.val
  nodeFast R H s m v tables
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkFast (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : Bool :=
  let tables := (childrenList R R.root).map (computeFast R H s m)
  (rootFold tables).any (acceptRootB T)

@[simp] theorem nodeFast_eq (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    nodeFast R H s m v ts = nodeTable R H s m v ts := by simp [nodeFast, nodeTable]

@[simp] theorem computeFast_eq (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) : computeFast R H s m v = computeCompact R H s m v := by
  rw [computeFast, computeCompact]
  rw [nodeFast_eq]
  congr 1
  apply List.map_congr_left
  intro u _
  exact computeFast_eq R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem checkFast_eq (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) : checkFast R H s m T = checkCompact R H s m T := by
  have h := funext (computeFast_eq R H s m)
  simp only [checkFast, checkCompact, h]

def localFastStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (m : Nat)
    (v : Fin N) : Measured (List (Vector Nat m)) :=
  let r := compositionsFastStats m (H v)
  let qs := r.value.filter fun q => decide (R.parent v = R.root → ∀ i, val q i ≤ 1)
  ⟨qs, r.stats.add { columnsGenerated := r.value.length, columnsAccepted := qs.length }⟩

@[simp] theorem localFastStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) :
    (localFastStats R H m v).value = localFast R H m v := by
  simp [localFastStats, localFast]

def nodeFastStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (tables : List (List (ExecCompactState m))) :
    Measured (List (ExecCompactState m)) :=
  let qs := localFastStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideCostsStats (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat)) tables
    (r.value.map fun b => (⟨support q, b⟩ : ExecCompactState m),
      r.stats.add { ratMuls := m })
  let d := dedupStats (rs.flatMap Prod.fst)
  ⟨d.value, qs.stats.add ((sumStats (rs.map Prod.snd)).add d.stats)⟩

@[simp] theorem nodeFastStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeFastStats R H s m v ts).value = nodeTable R H s m v ts := by
  simp [nodeFastStats, nodeTable, List.flatMap_map]

def computeFastStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : Measured (List (ExecCompactState m)) :=
  let cs := collect ((childrenList R v).attach.map fun u => computeFastStats R H s m u.val)
  let r := nodeFastStats R H s m v cs.value
  ⟨r.value, ({ nodeCalls := 1 } : DPStats).add (cs.stats.add r.stats)⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeFastStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeFastStats R H s m v).value = computeCompact R H s m v := by
  rw [computeFastStats, computeCompact_eq]
  simp only [collect, List.map_map, Function.comp_def, nodeFastStats_erase]
  congr 1
  rw [← List.attach_map_val (l := childrenList R v)]
  apply List.map_congr_left
  intro u _
  exact computeFastStats_erase R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkFastStats (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) : Measured Bool :=
  let cs := collect ((childrenList R R.root).map (computeFastStats R H s m))
  let r := rootFoldStats cs.value
  let a := anyCounted (acceptRootB T) r.value
  ⟨a.1, cs.stats.add (r.stats.add { acceptCalls := a.2 })⟩

theorem checkFastStats_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkFastStats R H s m T).value = checkCompact R H s m T := by
  simp [checkFastStats, collect, List.map_map, Function.comp_def, checkCompact,
    (anyCounted_spec _ _).1]

end UAVProof.TreeBudgetSubtreeStats
