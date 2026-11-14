import LeanCompletion.UAV.TreeBudgetSubtreeStats

/-! A separate integer-cost entry point. Candidate order, child order,
support tests, root caps and rightmost-representative deduplication are unchanged. -/
namespace UAVProof.TreeBudgetSubtreeInteger
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
variable {N m : ℕ}

structure IntState (m : ℕ) where
  active : Vector Bool m
  cost : Vector ℤ m
  deriving DecidableEq, Inhabited

structure IntRoot (m : ℕ) where
  used : Vector ℕ m
  cost : Vector ℤ m
  deriving DecidableEq, Inhabited

def add (a b : Vector ℤ m) : Vector ℤ m := Vector.ofFn fun i => val a i + val b i

def inside (a : Vector Bool m) (base : Vector ℤ m) : List (List (IntState m)) → List (Vector ℤ m)
  | [] => [base]
  | t :: ts => ((t.filter fun e => subsetB e.active a).flatMap fun e =>
      (inside a base ts).map (add e.cost)).dedup

def node (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (IntState m))) : List (IntState m) :=
  ((localCandidates R H m v).flatMap fun q =>
    (inside (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts).map
      fun b => ⟨support q, b⟩).dedup

def compute (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) : List (IntState m) :=
  node R H w m v ((childrenList R v).attach.map fun u => compute R H w m u.val)
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def rootZero (m : ℕ) : IntRoot m := ⟨Vector.ofFn fun _ => 0, Vector.ofFn fun _ => 0⟩
def rootAdd (x : IntRoot m) (e : IntState m) : IntRoot m :=
  ⟨Vector.ofFn fun i => val x.used i + bit (val e.active i), add x.cost e.cost⟩
def cap (x : IntRoot m) : Bool := (List.finRange m).all fun i => decide (val x.used i ≤ 1)
def rootFold : List (List (IntState m)) → List (IntRoot m)
  | [] => [rootZero m]
  | t :: ts => ((t.flatMap fun e => (rootFold ts).map fun b => rootAdd b e).filter cap).dedup
def accept (B : ℤ) (b : IntRoot m) : Bool :=
  (List.finRange m).all fun i => decide (val b.used i = 1 ∧ val b.cost i ≤ B)
def check (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) : Bool :=
  (rootFold ((childrenList R R.root).map (compute R H w m))).any (accept B)

def floorBudget (D : ℕ) (T : ℚ) : ℤ := ⌊(D : ℚ) * T⌋

def liftCost (D : ℕ) (b : Vector ℤ m) : Vector ℚ m :=
  Vector.ofFn fun i => ((val b i : ℤ) : ℚ) / (D : ℚ)
def liftState (D : ℕ) (e : IntState m) : ExecCompactState m := ⟨e.active, liftCost D e.cost⟩
def liftRoot (D : ℕ) (e : IntRoot m) : ExecRootState m := ⟨e.used, liftCost D e.cost⟩

theorem liftCost_injective {D : ℕ} (hD : 0 < D) : Function.Injective (@liftCost m D) := by
  intro a b he
  apply vector_ext
  intro i
  have hi := congrArg (fun c => val c i) he
  simp only [liftCost, val_ofFn] at hi
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hh := (div_left_inj' hd).mp hi
  exact_mod_cast hh

theorem liftState_injective {D : ℕ} (hD : 0 < D) : Function.Injective (@liftState m D) := by
  intro a b he
  have ha := congrArg ExecCompactState.active he
  have hc := liftCost_injective hD (congrArg ExecCompactState.cost he)
  cases a; cases b; simp_all [liftState]

theorem liftRoot_injective {D : ℕ} (hD : 0 < D) : Function.Injective (@liftRoot m D) := by
  intro a b he
  have hu := congrArg ExecRootState.used he
  have hc := liftCost_injective hD (congrArg ExecRootState.cost he)
  cases a; cases b; simp_all [liftRoot]

@[simp] theorem lift_add (D : ℕ) (a b : Vector ℤ m) :
    liftCost D (add a b) = addCost (liftCost D a) (liftCost D b) := by
  apply vector_ext
  intro i
  simp [liftCost, add, addCost, Int.cast_add, add_div]

theorem lift_initial {D : ℕ} (hD : 0 < D) (w : ℤ) (a : ℚ)
    (hw : (w : ℚ) = (D : ℚ) * a) (q : Vector ℕ m) :
    liftCost D (Vector.ofFn fun i => w * ((val q i : ℕ) : ℤ)) =
      Vector.ofFn fun i => a * ((val q i : ℕ) : ℚ) := by
  apply vector_ext
  intro i
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [liftCost, val_ofFn, Int.cast_mul, Int.cast_natCast, hw]
  field_simp

theorem lift_budget {D : ℕ} (hD : 0 < D) (b : ℤ) (T : ℚ) :
    (b : ℚ) / (D : ℚ) ≤ T ↔ b ≤ floorBudget D T := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hd, floorBudget, Int.le_floor]
  rw [mul_comm T]

theorem inside_lift_eq {D : ℕ} (hD : 0 < D) (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (IntState m))) :
    (inside a base ts).map (liftCost D) =
      insideCosts a (liftCost D base) (ts.map (List.map (liftState D))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [inside, insideCosts, List.map_cons]
    rw [← List.dedup_map_of_injective (liftCost_injective hD)]
    congr 1
    simp only [List.map_flatMap, List.map_map, List.filter_map, List.flatMap_map, Function.comp_def]
    apply List.flatMap_congr
    intro e _
    rw [← ih, List.map_map]
    apply List.map_congr_left
    intro b _
    exact lift_add D e.cost b

@[simp] theorem lift_rootZero (D : ℕ) : liftRoot D (rootZero m) =
    TreeBudgetSubtreeExecutable.rootZero m := by
  apply rootState_ext <;> intro i <;> simp [liftRoot, liftCost, rootZero,
    TreeBudgetSubtreeExecutable.rootZero, zeroCost]

@[simp] theorem lift_rootAdd (D : ℕ) (b : IntRoot m) (e : IntState m) :
    liftRoot D (rootAdd b e) = TreeBudgetSubtreeExecutable.rootAdd (liftRoot D b) (liftState D e) := by
  apply rootState_ext <;> intro i <;> simp [liftRoot, liftState, liftCost, rootAdd,
    TreeBudgetSubtreeExecutable.rootAdd, add, addCost, add_div]

theorem rootFold_lift_eq {D : ℕ} (hD : 0 < D) (ts : List (List (IntState m))) :
    (rootFold ts).map (liftRoot D) =
      TreeBudgetSubtreeExecutable.rootFold (ts.map (List.map (liftState D))) := by
  induction ts with
  | nil => simp [rootFold, TreeBudgetSubtreeExecutable.rootFold]
  | cons t ts ih =>
    simp only [rootFold, TreeBudgetSubtreeExecutable.rootFold, List.map_cons]
    rw [← List.dedup_map_of_injective (liftRoot_injective hD)]
    have hr : ((t.flatMap fun e => (rootFold ts).map fun b => rootAdd b e).map (liftRoot D)) =
        (t.map (liftState D)).flatMap (fun e =>
          (TreeBudgetSubtreeExecutable.rootFold (ts.map (List.map (liftState D)))).map
            fun b => TreeBudgetSubtreeExecutable.rootAdd b e) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map]
      apply List.flatMap_congr
      intro e _
      rw [← ih, List.map_map]
      simp [Function.comp_def]
    congr 1
    rw [← hr, List.filter_map]
    rfl

theorem node_lift_eq {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (v : Fin N)
    (hw : (w v : ℚ) = (D : ℚ) * linearWeight R s v) (ts : List (List (IntState m))) :
    (node R H w m v ts).map (liftState D) =
      nodeTable R H s m v (ts.map (List.map (liftState D))) := by
  unfold node nodeTable
  rw [← List.dedup_map_of_injective (liftState_injective hD)]
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  rw [List.map_map, ← lift_initial hD (w v) _ hw q, ← inside_lift_eq hD,
    List.map_map]
  rfl

theorem compute_lift_eq {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (v : Fin N)
    (hv : v ≠ R.root) (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    (compute R H w m v).map (liftState D) = computeCompact R H s m v := by
  rw [compute, node_lift_eq hD R H s w m v (hw v hv), computeCompact]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro u _
  exact compute_lift_eq hD R H s w m u.val
    ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp u.property)).1 hw
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem accept_lift_eq {D : ℕ} (hD : 0 < D) (T : ℚ) (b : IntRoot m) :
    accept (floorBudget D T) b = acceptRootB T (liftRoot D b) := by
  unfold accept acceptRootB
  congr 1
  funext i
  simp only [liftRoot, liftCost, val_ofFn, lift_budget hD]

theorem check_eq {D : ℕ} (hD : 0 < D) (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ) (m : ℕ) (T : ℚ)
    (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    check R H w m (floorBudget D T) = checkCompact R H s m T := by
  unfold check checkCompact
  dsimp only
  have hc : ((childrenList R R.root).map (compute R H w m)).map (List.map (liftState D)) =
      (childrenList R R.root).map (computeCompact R H s m) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro u hu
    exact compute_lift_eq hD R H s w m u
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1 hw
  rw [← hc, ← rootFold_lift_eq hD, List.any_map]
  congr 1
  funext b
  exact accept_lift_eq hD T b

end UAVProof.TreeBudgetSubtreeInteger
