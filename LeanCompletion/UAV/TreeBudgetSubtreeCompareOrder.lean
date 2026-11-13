import LeanCompletion.UAV.TreeBudgetSubtreeCompareDiagnostics

/-! Controlled intervention: only final node dedup uses explicit comparison.
Internal cost folds and root folds remain the frozen implementations. -/
namespace UAVProof.TreeBudgetSubtreeCompare
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
variable {N m : Nat}

def nodeTableOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (tables : List (List (ExecCompactState m))) : List (ExecCompactState m) :=
  dedupWith (compactEq order) ((localCandidates R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn (fun i => linearWeight R s v * ((val q i : ℕ) : ℚ))) tables).map
      (fun b => ⟨support q, b⟩))

def computeCompactOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : List (ExecCompactState m) :=
  let tables := (childrenList R v).attach.map fun u => computeCompactOrder order R H s m u.val
  nodeTableOrder order R H s m v tables
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkCompactOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : Bool :=
  let tables := (childrenList R R.root).map (computeCompactOrder order R H s m)
  (rootFold tables).any (acceptRootB T)

@[simp] theorem nodeTableOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (ts : List (List (ExecCompactState m))) :
    nodeTableOrder order R H s m v ts = nodeTable R H s m v ts := by
  simp [nodeTableOrder, nodeTable, dedupWith_correct _ (compactEq_correct order)]

@[simp] theorem computeCompactOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    computeCompactOrder order R H s m v = computeCompact R H s m v := by
  rw [computeCompactOrder, computeCompact, nodeTableOrder_eq]
  congr 1
  apply List.map_congr_left
  intro u _
  exact computeCompactOrder_eq order R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem checkCompactOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) :
    checkCompactOrder order R H s m T = checkCompact R H s m T := by
  have h := funext (computeCompactOrder_eq order R H s m)
  simp only [checkCompactOrder, checkCompact, h]

def nodeFullOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) (tables : List (List (ExecFullState m))) : List (ExecFullState m) :=
  let projected := tables.map (List.map projectFull)
  dedupWith (fullEq order) ((localCandidates R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : Nat) : Rat))
      projected).map fun b => ⟨q, b⟩)

def computeFullOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (v : Fin N) : List (ExecFullState m) :=
  let ts := (childrenList R v).attach.map fun u => computeFullOrder order R H s m u.val
  nodeFullOrder order R H s m v ts
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def checkFullOrder (order : Bool) (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) : Bool :=
  (rootFold ((childrenList R R.root).map fun u =>
    (computeFullOrder order R H s m u).map projectFull)).any (acceptRootB T)

@[simp] theorem nodeFullOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N)
    (ts : List (List (ExecFullState m))) :
    nodeFullOrder order R H s m v ts = nodeFull R H s m v ts := by
  simp [nodeFullOrder, nodeFull, dedupWith_correct _ (fullEq_correct order)]

@[simp] theorem computeFullOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (v : Fin N) :
    computeFullOrder order R H s m v = computeFull R H s m v := by
  rw [computeFullOrder, computeFull, nodeFullOrder_eq]
  congr 1
  apply List.map_congr_left
  intro u _
  exact computeFullOrder_eq order R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem checkFullOrder_eq (order : Bool) (R : RootedTree (Fin N))
    (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) (T : Rat) :
    checkFullOrder order R H s m T = checkFull R H s m T := by
  have h := funext (computeFullOrder_eq order R H s m)
  simp only [checkFullOrder, checkFull, h]

end UAVProof.TreeBudgetSubtreeCompare
