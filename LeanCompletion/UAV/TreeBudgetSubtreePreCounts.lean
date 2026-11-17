import LeanCompletion.UAV.TreeBudgetSubtreePreExecution

/-! Independent arithmetic recurrences for the ghost counters. These are
specifications, never called by prepareC or execute to rerun preprocessing. -/
namespace UAVProof.TreeBudgetSubtreePre
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeAutoScaleSeed
variable {N : ℕ}

def euclidIterations (a b : ℕ) : ℕ :=
  if h : a = 0 then 0 else 1 + euclidIterations (b % a) a
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem euclid_ops_exact (a b : ℕ) :
    (euclid a b).ops = 4 * euclidIterations a b + 1 := by
  rw [euclid, euclidIterations]
  split
  · simp_all
  · dsimp only
    rw [euclid_ops_exact]
    ring
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

theorem euclid_iterations_le (a b : ℕ) : euclidIterations a b ≤ 2*a.size := by
  have h := euclid_ops a b
  rw [euclid_ops_exact] at h
  omega

def coefficientOps (I : Input N) (v : Fin N) : ℕ :=
  if v = I.root then 3 else
    let a := I.service[v]
    let b := if I.parent[v] = I.root then 0 else I.service[I.parent[v]]
    4 * euclidIterations (a.num * b.den + b.num * a.den).natAbs (a.den*b.den) + 23

theorem coefficient_ops_exact (I : Input N) (v : Fin N) :
    (coefficientC I v).ops = coefficientOps I v := by
  simp only [coefficientC, coefficientOps]
  split
  · rfl
  · simp [ratAddC, normalizeC, euclid_ops_exact]

def rootOps (I : Input N) : List (Fin N) → ℕ
  | [] => 1
  | v :: vs => rootOps I vs + if v ≠ I.root ∧ I.parent[v] = I.root then 12 else 8

theorem rootScan_ops_exact (I : Input N) (vs : List (Fin N)) :
    (rootScan I vs).ops = rootOps I vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [rootScan, rootOps, ih]; split <;> rfl

def denOps : List ℚ → ℕ
  | [] => 1
  | a :: as => denOps as + 4*euclidIterations a.den (denLCM as) + 7

theorem denLCMC_ops_exact (as : List ℚ) : (denLCMC as).ops = denOps as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [denLCMC, lcmC, euclid_ops_exact, ih, denOps]; ring

theorem collect_ops_exact {α : Type} (rs : List (Run α)) :
    (collect rs).ops = (rs.map Run.ops).sum + 2*rs.length + 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [collect, ih]; ring

theorem collectV_ops_exact {α : Type} (f : Fin N → Run α) :
    (collectV f).ops = ((List.finRange N).map fun v => (f v).ops).sum + 2*N+1 := by
  simp only [collectV, collect_ops_exact, Vector.toList_ofFn, List.length_ofFn]
  rw [List.ofFn_eq_map]
  simp [List.map_map, Function.comp_def]

theorem prepareC_ops_exact (I : Input N) :
    (prepareC I).ops =
      2*((List.finRange N).map (coefficientOps I)).sum +
      denOps ((List.finRange N).map fun v => (coefficientC I v).value) + 8*N+16 := by
  simp only [prepareC, collect_ops_exact, collectV_ops_exact, collect_value,
    List.map_map, Function.comp_def, List.length_map, List.length_finRange,
    after, scaleNumC, floorBudgetC, coefficient_ops_exact, denLCMC_ops_exact]
  simp only [List.sum_map_add, List.map_const', List.length_finRange,
    List.sum_replicate, smul_eq_mul]
  ring

end UAVProof.TreeBudgetSubtreePre
