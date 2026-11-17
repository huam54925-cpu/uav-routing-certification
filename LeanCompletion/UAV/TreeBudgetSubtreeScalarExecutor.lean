import LeanCompletion.UAV.TreeBudgetSubtreeScalarCandidates

/-! Single-run I2 executor. Each recursive result, filter, candidate and matrix
is shared by value and ghost observations; no call to the old solver is made. -/
namespace UAVProof.TreeBudgetSubtreeScalar
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
open TreeBudgetSubtreeResourceSeed TreeBudgetSubtreeIntegerWitnessSeed
variable {N m : Nat}

def insidePairC (e : Entry N m) (r : Inside N m) : Counted (Inside N m) :=
  let c := addC e.key.cost r.cost
  ⟨⟨c.value, e :: r.picks⟩, c.ops + 5⟩

def insideC (a : Vector Bool m) (base : Vector Int m) :
    List (List (Entry N m)) → Counted (ResourceResult (List (Inside N m)))
  | [] => ⟨⟨[⟨base, []⟩], { maxRawTable := 1, maxDedupTable := 1 }, {}⟩, 4⟩
  | t :: ts =>
    let r := insideC a base ts
    let eligible := filterC (fun e =>
      let c := subsetC e.key.active a; ⟨c.value, c.ops+1⟩) t
    let raw := flatMapC (fun e => mapC (insidePairC e) r.value.value) eligible.value
    let d := dedupC Inside.cost vectorEqC raw.value
    ⟨⟨d.value.value, r.value.keyStats.add
      ((insideStep m t.length raw.value.length).add d.value.keyStats),
      r.value.payload.add (({ pickCons := raw.value.length } : PayloadStats).add d.value.payload)⟩,
      r.ops + eligible.ops + raw.ops + d.ops + 5⟩

@[simp] theorem insideC_value (a : Vector Bool m) (base : Vector Int m)
    (ts : List (List (Entry N m))) : (insideC a base ts).value = insideR a base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp [insideC, insideR, ih, insidePairC, dedupC_value _ _ vectorEqC_value]

def entryC (v : Fin N) (q : Vector Nat m) (b : Inside N m) : Counted (Entry N m) :=
  let a := supportC q
  let g := glueC v q b.picks
  ⟨⟨⟨a.value, b.cost⟩, g.value⟩, a.ops + g.ops + 5⟩

def nodeRunC (v : Fin N) (w : Int) (ts : List (List (Entry N m)))
    (q : Vector Nat m) : Counted (ResourceResult (List (Entry N m))) :=
  let a := supportC q
  let b := scaleC w q
  let r := insideC a.value b.value ts
  let es := mapC (entryC v q) r.value.value
  ⟨⟨es.value, r.value.keyStats.add { ratMuls := m },
    r.value.payload.add (sumPayload (r.value.value.map fun b => glueCharge N m b.picks.length))⟩,
    a.ops + b.ops + r.ops + es.ops + 4⟩

/-- List control on child/candidate runs, with the G observations aggregated as ghosts. -/
def collectC {α : Type} (rs : List (Counted (ResourceResult α))) :
    Counted (ResourceResult (List α)) :=
  ⟨collectR (rs.map Counted.value), (rs.map Counted.ops).sum + 3*rs.length+1⟩

def nodeC (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    Counted (ResourceResult (List (Entry N m))) :=
  let qs := candidatesC R H m v
  let runs := collectC (qs.value.value.map (nodeRunC v (w v) ts))
  let flat := flatMapC (fun xs => ⟨xs, 1⟩) runs.value.value
  let d := dedupC Entry.key stateEqC flat.value
  ⟨⟨d.value.value, qs.value.stats.add (runs.value.keyStats.add d.value.keyStats),
      runs.value.payload.add d.value.payload⟩,
    qs.ops + runs.ops + flat.ops + d.ops + 5⟩

@[simp] theorem nodeC_value (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    (nodeC R H w m v ts).value = nodeR R H w m v ts := by
  simp [nodeC, nodeR, nodeRunC, entryC, collectC, collectR,
    List.map_map, List.flatMap_map, Function.comp_def, dedupC_value _ _ stateEqC_value]

def computeC (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) : Counted (ResourceResult (List (Entry N m))) :=
  let ch := childrenC R v
  let cs := collectC (ch.value.attach.map fun u => computeC R H w m u.val)
  let r := nodeC R H w m v cs.value.value
  ⟨⟨r.value.value, ({ nodeCalls := 1 } : DPStats).add
      (cs.value.keyStats.add r.value.keyStats), cs.value.payload.add r.value.payload⟩,
    ch.ops + cs.ops + r.ops + 5⟩
termination_by R.rank v
decreasing_by
  apply R.child_rank
  apply (mem_childrenList R v u.val).mp
  simpa [ch] using u.property

@[simp] theorem computeC_value (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) :
    (computeC R H w m v).value = computeR R H w m v := by
  have hc : ((childrenC R v).value.attach.map fun u => (computeC R H w m u.val).value) =
      (childrenC R v).value.attach.map (fun u => computeR R H w m u.val) := by
    apply List.map_congr_left
    intro u _
    exact computeC_value R H w m u.val
  rw [computeC, computeR]
  simp only [childrenC_value, nodeC_value, collectC, List.map_map, Function.comp_def]
  rw [hc]
  simp only [List.attach_map_val, childrenC_value]
termination_by R.rank v
decreasing_by
  apply R.child_rank
  apply (mem_childrenList R v u.val).mp
  simpa using u.property

def rootPairC (e : Entry N m) (r : Root N m) : Counted (Root N m) :=
  let a := rootAddC r.key e.key
  ⟨⟨a.value, e :: r.picks⟩, a.ops + 5⟩

def rootsC : List (List (Entry N m)) → Counted (ResourceResult (List (Root N m)))
  | [] =>
    let z := tabulateC (fun _ : Fin m => (⟨0, 1⟩ : Counted Nat))
    let c := tabulateC (fun _ : Fin m => (⟨0, 1⟩ : Counted Int))
    ⟨⟨[⟨⟨z.value, c.value⟩, []⟩], { maxRawTable := 1, maxDedupTable := 1 }, {}⟩,
      z.ops + c.ops + 5⟩
  | t :: ts =>
    let r := rootsC ts
    let raw := flatMapC (fun e => mapC (rootPairC e) r.value.value) t
    let kept := filterC (fun r => let c := capC r.key; ⟨c.value, c.ops+1⟩) raw.value
    let d := dedupC Root.key rootEqC kept.value
    ⟨⟨d.value.value, r.value.keyStats.add
      ((rootStep m raw.value.length kept.value.length).add d.value.keyStats),
      r.value.payload.add (({ pickCons := raw.value.length } : PayloadStats).add d.value.payload)⟩,
      r.ops + raw.ops + kept.ops + d.ops + 5⟩

@[simp] theorem rootsC_value (ts : List (List (Entry N m))) :
    (rootsC ts).value = rootsR ts := by
  induction ts with
  | nil => simp [rootsC, rootsR, TreeBudgetSubtreeInteger.rootZero]
  | cons t ts ih =>
    simp [rootsC, rootsR, ih, rootPairC, dedupC_value _ _ rootEqC_value]

def findC {α : Type} (p : α → Counted Bool) : List α → Counted (Option α × Nat)
  | [] => ⟨(none, 0), 1⟩
  | x :: xs => let c := p x
              if c.value then ⟨(some x, 1), c.ops+4⟩
              else let r := findC p xs; ⟨(r.value.1, r.value.2+1), c.ops+r.ops+4⟩

@[simp] theorem findC_value {α : Type} (p : α → Counted Bool) (xs : List α) :
    (findC p xs).value = findCounted (fun x => (p x).value) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (p x).value <;> simp [findC, findCounted, h, ih]

def finishC (R : RootedTree (Fin N)) : Option (Root N m) →
    Counted (Option (TreeBudgetCertificate.Certificate (Fin N)) × PayloadStats)
  | none => ⟨(none, {}), 2⟩
  | some x =>
    let z := tabulateC (fun _ : Fin m => (⟨0, 1⟩ : Counted Nat))
    let g := glueC R.root z.value x.picks
    ⟨(some ⟨m, TreeBudgetSubtreeWitness.matrixVal g.value, fun _ => 1⟩,
      (glueCharge N m x.picks.length).add { rootZeroCells := m }), z.ops+g.ops+6⟩

@[simp] theorem finishC_value (R : RootedTree (Fin N)) (r : Option (Root N m)) :
    (finishC R r).value = finishR R r := by
  cases r <;> simp [finishC, finishR, certificate]

def solveC (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (B : Int) :
    Counted (ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N)))) :=
  let ch := childrenC R R.root
  let cs := collectC (ch.value.map (computeC R H w m))
  let r := rootsC cs.value.value
  let f := findC (fun x => let c := acceptC B x.key; ⟨c.value, c.ops+1⟩) r.value.value
  let out := finishC R f.value.1
  ⟨⟨out.value.1, cs.value.keyStats.add (r.value.keyStats.add { acceptCalls := f.value.2 }),
      cs.value.payload.add (r.value.payload.add out.value.2)⟩,
    ch.ops+cs.ops+r.ops+f.ops+out.ops+7⟩

/-- Whole-record equality: ordered witness, all 17 statistics, all nine payload fields. -/
@[simp] theorem solveC_value (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (B : Int) :
    (solveC R H w m B).value = solveR R H w m B := by
  simp [solveC, solveR, collectC, collectR, List.map_map, Function.comp_def]

end UAVProof.TreeBudgetSubtreeScalar
