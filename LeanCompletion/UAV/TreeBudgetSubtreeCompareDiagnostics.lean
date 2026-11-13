import LeanCompletion.UAV.TreeBudgetSubtreeComparePrimitives

/-! One row per dedup invocation, without saving candidate states or compared
pairs. `native=true` only labels the frozen derived-equality counters. Detailed
scans replace the comparator only at final node dedup, never inside/root. -/
namespace UAVProof.TreeBudgetSubtreeCompare
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
variable {N m : Nat}

structure Equality (α : Type) [DecidableEq α] where
  run : α → α → Compared Bool
  correct : ∀ x y, (run x y).value = decide (x = y)
  calls : ∀ x y, (run x y).counts.calls = 1

def nativeEquality (α : Type) [DecidableEq α] : Equality α :=
  ⟨fun x y => ⟨decide (x = y), { calls := 1 }⟩, fun _ _ => rfl, fun _ _ => rfl⟩

def compactEquality (native order : Bool) : Equality (ExecCompactState m) :=
  if native then nativeEquality _ else
  ⟨compactEqDetailed order, compactEqDetailed_correct order, fun _ _ => fieldsDetailed_calls ..⟩

def fullEquality (native order : Bool) : Equality (ExecFullState m) :=
  if native then nativeEquality _ else
  ⟨fullEqDetailed order, fullEqDetailed_correct order, fun _ _ => fieldsDetailed_calls ..⟩

structure StageRow where
  node : Nat
  stage : String
  position : Nat
  input : Nat
  output : Nat
  comparisons : CompareCounts
  deriving Repr

structure Diagnostic (α : Type) where
  result : Measured α
  rows : List StageRow

def collectDiagnostic {α : Type} (rs : List (Diagnostic α)) : Diagnostic (List α) :=
  ⟨collect (rs.map Diagnostic.result), rs.flatMap Diagnostic.rows⟩

def dedupDiagnostic {α : Type} [DecidableEq α] (node : Nat) (stage : String) (pos : Nat)
    (eq : Equality α) (xs : List α) : Diagnostic (List α) :=
  let d := dedupDetailed eq.run xs
  ⟨⟨d.value, { dedupInput := xs.length, dedupOutput := d.value.length,
               eqCalls := d.counts.calls, maxRawTable := xs.length,
               maxDedupTable := d.value.length }⟩,
    [⟨node, stage, pos, xs.length, d.value.length, d.counts⟩]⟩

@[simp] theorem dedupDiagnostic_collapse {α : Type} [DecidableEq α]
    (node : Nat) (stage : String) (pos : Nat) (eq : Equality α) (xs : List α) :
    (dedupDiagnostic node stage pos eq xs).result = dedupStats xs := by
  simp [dedupDiagnostic, (dedupDetailed_spec eq.run eq.correct eq.calls xs).1,
    (dedupDetailed_spec eq.run eq.correct eq.calls xs).2,
    dedupStats, dedupCounted_erase, dedupCounted_count]

theorem dedupDiagnostic_rows {α : Type} [DecidableEq α]
    (node : Nat) (stage : String) (pos : Nat) (eq : Equality α) (xs : List α) :
    ((dedupDiagnostic node stage pos eq xs).rows.map fun r => r.comparisons.calls).sum =
      (dedupStats xs).stats.eqCalls := by
  simp [dedupDiagnostic, (dedupDetailed_spec eq.run eq.correct eq.calls xs).2, dedupProfile]

def insideDiagnostic (node pos : Nat) (a : Vector Bool m) (base : Vector Rat m) :
    List (List (ExecCompactState m)) → Diagnostic (List (Vector Rat m))
  | [] => ⟨⟨[base], { maxRawTable := 1, maxDedupTable := 1 }⟩, []⟩
  | t :: ts =>
    let r := insideDiagnostic node (pos + 1) a base ts
    let raw := insideRaw a t r.result.value
    let d := dedupDiagnostic node "inside" pos (nativeEquality _) raw
    ⟨⟨d.result.value, r.result.stats.add ((insideStep m t.length raw.length).add d.result.stats)⟩,
      r.rows ++ d.rows⟩

@[simp] theorem insideDiagnostic_collapse (node pos : Nat) (a : Vector Bool m)
    (base : Vector Rat m) (ts : List (List (ExecCompactState m))) :
    (insideDiagnostic node pos a base ts).result = insideCostsStats a base ts := by
  induction ts generalizing pos with
  | nil => rfl
  | cons t ts ih => simp [insideDiagnostic, insideCostsStats, ih]

def rootDiagnostic (node pos : Nat) :
    List (List (ExecCompactState m)) → Diagnostic (List (ExecRootState m))
  | [] => ⟨⟨[rootZero m], { maxRawTable := 1, maxDedupTable := 1 }⟩, []⟩
  | t :: ts =>
    let r := rootDiagnostic node (pos + 1) ts
    let raw := rootRaw t r.result.value
    let kept := raw.filter rootCapB
    let d := dedupDiagnostic node "root" pos (nativeEquality _) kept
    ⟨⟨d.result.value, r.result.stats.add ((rootStep m raw.length kept.length).add d.result.stats)⟩,
      r.rows ++ d.rows⟩

@[simp] theorem rootDiagnostic_collapse (node pos : Nat)
    (ts : List (List (ExecCompactState m))) :
    (rootDiagnostic node pos ts).result = rootFoldStats ts := by
  induction ts generalizing pos with
  | nil => rfl
  | cons t ts ih => simp [rootDiagnostic, rootFoldStats, ih]

def nodeCompactDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (tables : List (List (ExecCompactState m))) : Diagnostic (List (ExecCompactState m)) :=
  let qs := localCandidatesStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideDiagnostic v.val 0 (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat)) tables
    (r.result.value.map fun b => (⟨support q, b⟩ : ExecCompactState m),
      r.result.stats.add { ratMuls := m }, r.rows)
  let d := dedupDiagnostic v.val "node" 0 (compactEquality native order) (rs.flatMap Prod.fst)
  ⟨⟨d.result.value, qs.stats.add ((sumStats (rs.map fun r => r.2.1)).add d.result.stats)⟩,
    (rs.flatMap fun r => r.2.2) ++ d.rows⟩

@[simp] theorem nodeCompactDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (ts : List (List (ExecCompactState m))) :
    (nodeCompactDiagnostic native order R H s m v ts).result = nodeTableStats R H s m v ts := by
  simp [nodeCompactDiagnostic, nodeTableStats, List.map_map, List.flatMap_map, Function.comp_def]

def computeCompactDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    Diagnostic (List (ExecCompactState m)) :=
  let cs := collectDiagnostic ((childrenList R v).attach.map fun u =>
    computeCompactDiagnostic native order R H s m u.val)
  let r := nodeCompactDiagnostic native order R H s m v cs.result.value
  ⟨⟨r.result.value, ({ nodeCalls := 1 } : DPStats).add (cs.result.stats.add r.result.stats)⟩,
    cs.rows ++ r.rows⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeCompactDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeCompactDiagnostic native order R H s m v).result = computeCompactStats R H s m v := by
  rw [computeCompactDiagnostic, computeCompactStats]
  simp only [collectDiagnostic, List.map_map, Function.comp_def, nodeCompactDiagnostic_collapse]
  have h : ((childrenList R v).attach.map fun u =>
      (computeCompactDiagnostic native order R H s m u.val).result) =
      (childrenList R v).attach.map (fun u => computeCompactStats R H s m u.val) := by
    apply List.map_congr_left
    intro u _
    exact computeCompactDiagnostic_collapse native order R H s m u.val
  rw [h]
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkCompactDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) : Diagnostic Bool :=
  let cs := collectDiagnostic ((childrenList R R.root).map
    (computeCompactDiagnostic native order R H s m))
  let r := rootDiagnostic R.root.val 0 cs.result.value
  let a := anyCounted (acceptRootB T) r.result.value
  ⟨⟨a.1, cs.result.stats.add (r.result.stats.add { acceptCalls := a.2 })⟩, cs.rows ++ r.rows⟩

@[simp] theorem checkCompactDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkCompactDiagnostic native order R H s m T).result = checkCompactStats R H s m T := by
  simp [checkCompactDiagnostic, checkCompactStats, collectDiagnostic,
    List.map_map, Function.comp_def]

def nodeFullDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (tables : List (List (ExecFullState m))) : Diagnostic (List (ExecFullState m)) :=
  let projected := tables.map (List.map projectFull)
  let qs := localCandidatesStats R H m v
  let rs := qs.value.map fun q =>
    let r := insideDiagnostic v.val 0 (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat)) projected
    (r.result.value.map fun b => (⟨q, b⟩ : ExecFullState m),
      r.result.stats.add { ratMuls := m }, r.rows)
  let d := dedupDiagnostic v.val "node" 0 (fullEquality native order) (rs.flatMap Prod.fst)
  ⟨⟨d.result.value, qs.stats.add ((sumStats (rs.map fun r => r.2.1)).add d.result.stats)⟩,
    (rs.flatMap fun r => r.2.2) ++ d.rows⟩

@[simp] theorem nodeFullDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (ts : List (List (ExecFullState m))) :
    (nodeFullDiagnostic native order R H s m v ts).result = nodeFullStats R H s m v ts := by
  simp [nodeFullDiagnostic, nodeFullStats, List.map_map, List.flatMap_map, Function.comp_def]

def computeFullDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    Diagnostic (List (ExecFullState m)) :=
  let cs := collectDiagnostic ((childrenList R v).attach.map fun u =>
    computeFullDiagnostic native order R H s m u.val)
  let r := nodeFullDiagnostic native order R H s m v cs.result.value
  ⟨⟨r.result.value, ({ nodeCalls := 1 } : DPStats).add (cs.result.stats.add r.result.stats)⟩,
    cs.rows ++ r.rows⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeFullDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    (computeFullDiagnostic native order R H s m v).result = computeFullStats R H s m v := by
  rw [computeFullDiagnostic, computeFullStats]
  simp only [collectDiagnostic, List.map_map, Function.comp_def, nodeFullDiagnostic_collapse]
  have h : ((childrenList R v).attach.map fun u =>
      (computeFullDiagnostic native order R H s m u.val).result) =
      (childrenList R v).attach.map (fun u => computeFullStats R H s m u.val) := by
    apply List.map_congr_left
    intro u _
    exact computeFullDiagnostic_collapse native order R H s m u.val
  rw [h]
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkFullDiagnostic (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) : Diagnostic Bool :=
  let cs := collectDiagnostic ((childrenList R R.root).map
    (computeFullDiagnostic native order R H s m))
  let r := rootDiagnostic R.root.val 0 (cs.result.value.map (List.map projectFull))
  let a := anyCounted (acceptRootB T) r.result.value
  ⟨⟨a.1, cs.result.stats.add (r.result.stats.add { acceptCalls := a.2 })⟩, cs.rows ++ r.rows⟩

@[simp] theorem checkFullDiagnostic_collapse (native order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (checkFullDiagnostic native order R H s m T).result = checkFullStats R H s m T := by
  simp [checkFullDiagnostic, checkFullStats, collectDiagnostic,
    List.map_map, Function.comp_def]

end UAVProof.TreeBudgetSubtreeCompare
