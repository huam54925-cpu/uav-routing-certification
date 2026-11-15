import LeanCompletion.UAV.TreeBudgetSubtreeResourcePrimitivesSeed
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats
import LeanCompletion.UAV.TreeBudgetSubtreeStatsGlobalBounds

/-!
Single-run executor adapted from the supplied 2026-11-15 seed package.
Run the witness computation once. In particular, do not obtain statistics by
running the key-only checker again. The fixed glue charge below defines the
paper's source-level census; it is not a trace of compiled machine operations.
The 17-field projection is proved in ResourceStats; ResourceBounds proves the
global bounds for these source-level charges.
-/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeStats TreeBudgetSubtreeIntegerWitnessSeed
variable {N m : Nat}

def resourceWork {α : Type} (r : ResourceResult α) : Nat :=
  logicalWork r.keyStats + r.payload.work

def collectR {α : Type} (xs : List (ResourceResult α)) : ResourceResult (List α) :=
  ⟨xs.map ResourceResult.value, sumStats (xs.map ResourceResult.keyStats),
    sumPayload (xs.map ResourceResult.payload)⟩

def glueCharge (N m k : Nat) : PayloadStats :=
  { matrices := 1, matrixCells := m * N, columnReads := m,
    childReads := m * (N - 1) * k, natAdds := m * (N - 1) * k,
    tempCells := m * (N - 1) * k }

def insideR (a : Vector Bool m) (base : Vector Int m) :
    List (List (Entry N m)) → ResourceResult (List (Inside N m))
  | [] => ⟨[⟨base, []⟩], { maxRawTable := 1, maxDedupTable := 1 }, {}⟩
  | t :: ts =>
    let rest := insideR a base ts
    let raw := (t.filter fun e => subsetB e.key.active a).flatMap fun e =>
      rest.value.map fun r =>
        (⟨TreeBudgetSubtreeInteger.add e.key.cost r.cost, e :: r.picks⟩ : Inside N m)
    let d := dedupResource Inside.cost raw
    ⟨d.value, rest.keyStats.add ((insideStep m t.length raw.length).add d.keyStats),
      rest.payload.add (({ pickCons := raw.length } : PayloadStats).add d.payload)⟩

@[simp] theorem insideR_erase (a : Vector Bool m) (base : Vector Int m)
    (ts : List (List (Entry N m))) :
    (insideR a base ts).value = TreeBudgetSubtreeIntegerWitnessSeed.inside a base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [insideR, TreeBudgetSubtreeIntegerWitnessSeed.inside, ih]

def nodeR (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    ResourceResult (List (Entry N m)) :=
  let qs := localCandidatesStats R H m v
  let runs := qs.value.map fun q =>
    let r := insideR (support q) (Vector.ofFn fun i => w v * ((val q i : Nat) : Int)) ts
    let es := r.value.map fun b =>
      (⟨⟨support q, b.cost⟩, TreeBudgetSubtreeIntegerWitnessSeed.glue v q b.picks⟩ : Entry N m)
    (⟨es, r.keyStats.add { ratMuls := m },
      r.payload.add (sumPayload (r.value.map fun b => glueCharge N m b.picks.length))⟩ :
        ResourceResult (List (Entry N m)))
  let d := dedupResource Entry.key (runs.flatMap ResourceResult.value)
  ⟨d.value, qs.stats.add ((sumStats (runs.map ResourceResult.keyStats)).add d.keyStats),
    (sumPayload (runs.map ResourceResult.payload)).add d.payload⟩

@[simp] theorem nodeR_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    (nodeR R H w m v ts).value = TreeBudgetSubtreeIntegerWitnessSeed.node R H w m v ts := by
  simp [nodeR, TreeBudgetSubtreeIntegerWitnessSeed.node, List.flatMap_map]

def computeR (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) : ResourceResult (List (Entry N m)) :=
  let cs := collectR ((childrenList R v).attach.map fun u => computeR R H w m u.val)
  let r := nodeR R H w m v cs.value
  ⟨r.value, ({ nodeCalls := 1 } : DPStats).add (cs.keyStats.add r.keyStats),
    cs.payload.add r.payload⟩
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

@[simp] theorem computeR_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) :
    (computeR R H w m v).value = TreeBudgetSubtreeIntegerWitnessSeed.compute R H w m v := by
  rw [computeR, TreeBudgetSubtreeIntegerWitnessSeed.compute]
  simp only [collectR, List.map_map, nodeR_erase, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u _
  exact computeR_erase R H w m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def rootsR : List (List (Entry N m)) → ResourceResult (List (Root N m))
  | [] => ⟨[⟨TreeBudgetSubtreeInteger.rootZero m, []⟩],
      { maxRawTable := 1, maxDedupTable := 1 }, {}⟩
  | t :: ts =>
    let rest := rootsR ts
    let raw := t.flatMap fun e => rest.value.map fun r =>
      (⟨TreeBudgetSubtreeInteger.rootAdd r.key e.key, e :: r.picks⟩ : Root N m)
    let kept := raw.filter fun r => TreeBudgetSubtreeInteger.cap r.key
    let d := dedupResource Root.key kept
    ⟨d.value, rest.keyStats.add ((rootStep m raw.length kept.length).add d.keyStats),
      rest.payload.add (({ pickCons := raw.length } : PayloadStats).add d.payload)⟩

@[simp] theorem rootsR_erase (ts : List (List (Entry N m))) :
    (rootsR ts).value = TreeBudgetSubtreeIntegerWitnessSeed.roots ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [rootsR, TreeBudgetSubtreeIntegerWitnessSeed.roots, ih]

def finishR (R : RootedTree (Fin N)) (r : Option (Root N m)) :
    Option (TreeBudgetCertificate.Certificate (Fin N)) × PayloadStats :=
  match r with
  | none => (none, {})
  | some x => (some (TreeBudgetSubtreeIntegerWitnessSeed.certificate R x),
      (glueCharge N m x.picks.length).add { rootZeroCells := m })

@[simp] theorem finishR_value (R : RootedTree (Fin N)) (r : Option (Root N m)) :
    (finishR R r).1 = r.map (TreeBudgetSubtreeIntegerWitnessSeed.certificate R) := by
  cases r <;> rfl

def solveR (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (B : Int) : ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N))) :=
  let cs := collectR ((childrenList R R.root).map (computeR R H w m))
  let r := rootsR cs.value
  let f := findCounted (fun x => TreeBudgetSubtreeInteger.accept B x.key) r.value
  let out := finishR R f.1
  ⟨out.1, cs.keyStats.add (r.keyStats.add { acceptCalls := f.2 }),
    cs.payload.add (r.payload.add out.2)⟩

@[simp] theorem solveR_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (B : Int) :
    (solveR R H w m B).value = TreeBudgetSubtreeIntegerWitnessSeed.solve R H w m B := by
  simp [solveR, TreeBudgetSubtreeIntegerWitnessSeed.solve, collectR,
    List.map_map, Function.comp_def, (findCounted_spec _ _).1]

/-- Preprocessing is executed, but its own costs are NOT in these DP counters. -/
def solveAutoR (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N))) :=
  let p := TreeBudgetSubtreeAutoScaleSeed.prepare R s T
  solveR R H (val p.weight) m p.budget

@[simp] theorem solveAutoR_erase (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    (solveAutoR R H s m T).value = TreeBudgetSubtreeIntegerWitnessSeed.solveAuto R H s m T := by
  simp [solveAutoR, TreeBudgetSubtreeIntegerWitnessSeed.solveAuto]

#print axioms insideR_erase
#print axioms nodeR_erase
#print axioms computeR_erase
#print axioms rootsR_erase
#print axioms solveR_erase
#print axioms solveAutoR_erase
end UAVProof.TreeBudgetSubtreeResourceSeed
