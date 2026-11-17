import LeanCompletion.UAV.TreeBudgetSubtreePreArithmetic
import LeanCompletion.UAV.TreeBudgetSubtreeResourceBounds

/-! H0/H1: legal materialized inputs, single-run preprocessing and exact erasure.
The tree is a semantic witness. Preprocessing reads only the arrays in Input;
it never evaluates an arbitrary user parent, H or service function.
-/
namespace UAVProof.TreeBudgetSubtreePre
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeState
open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeResourceSeed
variable {N : ℕ}

structure Input (N : ℕ) where
  root : Fin N
  parent : Vector (Fin N) N
  mass : Vector ℕ N
  service : Vector ℚ N
  routes : ℕ
  budget : ℚ

def Represents (I : Input N) (R : RootedTree (Fin N)) : Prop :=
  I.root = R.root ∧ ∀ v, I.parent[v] = R.parent v

def materialize (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : Input N :=
  ⟨R.root, Vector.ofFn R.parent, Vector.ofFn H, Vector.ofFn s, m, T⟩

theorem materialize_represents (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : Represents (materialize R H s m T) R := by
  simp [Represents, materialize]

def collect {α : Type} : List (Run α) → Run (List α)
  | [] => ⟨[], 1, 1⟩
  | r :: rs =>
    let t := collect rs
    ⟨r.value :: t.value, r.ops + t.ops + 2, max r.width t.width⟩

@[simp] theorem collect_value {α : Type} (rs : List (Run α)) :
    (collect rs).value = rs.map Run.value := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [collect, ih]

theorem collect_bounds {α : Type} (rs : List (Run α)) (C W : ℕ) (hW : 1 ≤ W)
    (h : ∀ r ∈ rs, r.ops ≤ C ∧ r.width ≤ W) :
    (collect rs).ops ≤ (C+2)*rs.length+1 ∧ (collect rs).width ≤ W := by
  induction rs with
  | nil => simp [collect]; omega
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [collect, List.length_cons]
    constructor
    · nlinarith [ht.1, hr.1]
    · exact max_le hr.2 ht.2

/-- f is evaluated once into a vector of Runs. Traversing this materialized
vector to collect observations does not evaluate f again. -/
def collectV {α : Type} (f : Fin N → Run α) : Run (Vector α N) :=
  let rs := Vector.ofFn f
  let c := collect rs.toList
  ⟨rs.map Run.value, c.ops, c.width⟩

@[simp] theorem collectV_value {α : Type} (f : Fin N → Run α) :
    (collectV f).value = Vector.ofFn (fun v => (f v).value) := by
  apply Vector.ext
  intro i hi
  simp [collectV]

theorem collectV_bounds {α : Type} (f : Fin N → Run α) (C W : ℕ) (hW : 1 ≤ W)
    (h : ∀ v, (f v).ops ≤ C ∧ (f v).width ≤ W) :
    (collectV f).ops ≤ (C+2)*N+1 ∧ (collectV f).width ≤ W := by
  have hc := collect_bounds (Vector.ofFn f).toList C W hW (by
    intro r hr
    simp only [Vector.toList_ofFn, List.mem_ofFn] at hr
    obtain ⟨v, rfl⟩ := hr
    exact h v)
  simpa [collectV] using hc

def coefficientC (I : Input N) (v : Fin N) : Run ℚ :=
  if v = I.root then ⟨0, 3, max N.size 1⟩ else
    let p := I.parent[v]
    let a := I.service[v]
    let b := if p = I.root then 0 else I.service[p]
    let q := ratAddC a b
    ⟨q.value, q.ops + 10, max N.size q.width⟩

@[simp] theorem coefficientC_value (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) (v : Fin N) :
    (coefficientC I v).value = normalizedWeight R (val I.service) v := by
  by_cases hv : v = R.root <;>
    simp [coefficientC, normalizedWeight, linearWeight, parentCharge, h.1, h.2, val, hv]

def rootScan (I : Input N) : List (Fin N) → Run ℕ
  | [] => ⟨0, 1, 1⟩
  | v :: vs =>
    let r := rootScan I vs
    if v ≠ I.root ∧ I.parent[v] = I.root then
      ⟨I.mass[v] + r.value, r.ops + 12,
        max N.size (max r.width (I.mass[v].size + r.value.size + 1))⟩
    else ⟨r.value, r.ops + 8, max N.size r.width⟩

theorem rootScan_value (I : Input N) (vs : List (Fin N)) :
    (rootScan I vs).value =
      ((vs.filter fun v => decide (v ≠ I.root ∧ I.parent[v] = I.root)).map (val I.mass)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : v ≠ I.root ∧ I.parent[v] = I.root
    · have hp : I.parent[v.val] = I.root := h.2
      simp [rootScan, h.1, h.2, hp, ih, val]
    · simp only [rootScan, List.filter_cons, h, decide_false,
        Bool.false_eq_true, if_false, ih]

def rootMassC (I : Input N) : Run ℕ := rootScan I (List.finRange N)

@[simp] theorem rootMassC_value (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) :
    (rootMassC I).value = TreeBudgetSubtreeResource.rootMass R (val I.mass) := by
  simp [rootMassC, rootScan_value, TreeBudgetSubtreeResource.rootMass, childrenList, h.1, h.2]

def denLCMC : List ℚ → Run ℕ
  | [] => ⟨1, 1, 1⟩
  | a :: as =>
    let r := denLCMC as
    let d := lcmC a.den r.value
    ⟨d.value, r.ops + d.ops + 3, max r.width d.width⟩

@[simp] theorem denLCMC_value (as : List ℚ) : (denLCMC as).value = denLCM as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [denLCMC, denLCM, ih]

/-- As in prepare, coefficient evaluation occurs once for the denominator list
and once again for the integer vector. No compiler sharing is assumed. -/
def prepareC (I : Input N) : Run (Prepared N) :=
  let as := collect ((List.finRange N).map (coefficientC I))
  let d := denLCMC as.value
  let w := collectV fun v =>
    let a := coefficientC I v
    after a (scaleNumC d.value a.value)
  let t := floorBudgetC d.value I.budget
  ⟨⟨d.value, w.value, t.value⟩, as.ops + d.ops + w.ops + t.ops + 6,
    max as.width (max d.width (max w.width t.width))⟩

@[simp] theorem prepareC_value (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) :
    (prepareC I).value = prepare R (val I.service) I.budget := by
  simp [prepareC, collectV_value, after, coefficientC_value I R h,
    List.map_map, Function.comp_def, prepare, weightList, scaleNumC, scaleNum,
    floorBudgetC_value, TreeBudgetSubtreeInteger.floorBudget]

/-- One guard comparison after reading m. On rejection, no coefficient, budget
or m-dimensional vector is evaluated or allocated. -/
def guardC (I : Input N) : Run Bool :=
  let r := rootMassC I
  ⟨decide (I.routes = r.value), r.ops + 3,
    max r.width (max I.routes.size r.value.size)⟩

def execute (R : RootedTree (Fin N)) (I : Input N) :
    Run (ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N)))) :=
  let g := guardC I
  if g.value then
    let p := prepareC I
    ⟨solveR R (val I.mass) (val p.value.weight) I.routes p.value.budget,
      g.ops + p.ops + 2, max g.width p.width⟩
  else ⟨⟨none, {}, {}⟩, g.ops + 1, g.width⟩

theorem execute_resource_eq (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) :
    (execute R I).value = solveGuardedR R (val I.mass) (val I.service) I.routes I.budget := by
  by_cases hm : I.routes = TreeBudgetSubtreeResource.rootMass R (val I.mass) <;>
    simp [execute, guardC, rootMassC_value I R h, prepareC_value I R h,
      solveGuardedR, solveAutoR, hm]

theorem execute_certificate_eq (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) :
    (execute R I).value.value =
      TreeBudgetSubtreeWitness.solve R (val I.mass) (val I.service) I.routes I.budget := by
  rw [execute_resource_eq I R h, solveGuardedR_erase,
    TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_eq]

theorem execute_pass_eq (I : Input N) (R : RootedTree (Fin N)) (hr : Represents I R)
    (hm : I.routes = TreeBudgetSubtreeResource.rootMass R (val I.mass)) :
    (execute R I).value = solveAutoR R (val I.mass) (val I.service) I.routes I.budget := by
  rw [execute_resource_eq I R hr, solveGuardedR, if_pos hm]

theorem execute_pass_keyStats (I : Input N) (R : RootedTree (Fin N)) (hr : Represents I R)
    (hm : I.routes = TreeBudgetSubtreeResource.rootMass R (val I.mass)) :
    (execute R I).value.keyStats =
      (TreeBudgetSubtreeStats.checkCompactStats R (val I.mass)
        (val I.service) I.routes I.budget).stats := by
  rw [execute_pass_eq I R hr hm, solveAutoR_keyStats]

theorem execute_pass_payload (I : Input N) (R : RootedTree (Fin N)) (hr : Represents I R)
    (hm : I.routes = TreeBudgetSubtreeResource.rootMass R (val I.mass)) :
    (execute R I).value.payload =
      (solveAutoR R (val I.mass) (val I.service) I.routes I.budget).payload :=
  congrArg ResourceResult.payload (execute_pass_eq I R hr hm)

theorem execute_reject (I : Input N) (R : RootedTree (Fin N))
    (hm : I.routes ≠ (rootMassC I).value) :
    execute R I = ⟨⟨none, {}, {}⟩, (guardC I).ops + 1, (guardC I).width⟩ := by
  simp [execute, guardC, hm]

end UAVProof.TreeBudgetSubtreePre
