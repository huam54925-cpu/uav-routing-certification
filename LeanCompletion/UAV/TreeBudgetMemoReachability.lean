import LeanCompletion.UAV.TreeBudgetMemoState

/-! States reachable by guarded row subtraction, including states whose search
eventually fails. Reachability is independent of feasibility and cache contents. -/
namespace UAVProof.TreeBudgetMemoReachability
open TreeFlowExistence TreeBudgetPatterns TreeBudgetRow TreeBudgetResidualSearch
open TreeBudgetMemoState TreeBudgetCertificate
variable {n : ℕ}

/-- The initial row count is fixed by the input. Every legal guarded transition
is admitted, regardless of whether it lies on a successful search path. -/
inductive ReachableResidual (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : ℕ → (Fin n → ℕ) → Prop
  | initial : ReachableResidual R H s T (rootCount R H) H
  | step {k : ℕ} {r p : Fin n → ℕ}
      (previous : ReachableResidual R H s T (k + 1) r)
      (row : RowValid R H s T p) (guard : p ≤ r) :
      ReachableResidual R H s T k (r - p)

theorem reachable_invariants (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) {k : ℕ} {r : Fin n → ℕ}
    (hr : ReachableResidual R H s T k r) :
    k = rootCount R r ∧ r ≤ H := by
  induction hr with
  | initial => exact ⟨rfl, le_rfl⟩
  | step previous row guard ih =>
    exact transition_invariants R H s T _ _ _ row guard ih.2 ih.1

/-- The root coordinate is unchanged even if a raw input is not normalized. -/
theorem reachable_root (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) {k : ℕ} {r : Fin n → ℕ}
    (hr : ReachableResidual R H s T k r) : r R.root = H R.root := by
  induction hr with
  | initial => rfl
  | step previous row guard ih => simpa only [Pi.sub_apply, row.1, Nat.sub_zero] using ih

theorem reachable_root_zero (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (hroot : H R.root = 0) {k : ℕ} {r : Fin n → ℕ}
    (hr : ReachableResidual R H s T k r) : r R.root = 0 :=
  (reachable_root R H s T hr).trans hroot

/-- All entries, including entries hidden by duplicate keys, have reachable keys. -/
def AllKeysReachable (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) : Prop :=
  ∀ e ∈ cache, ReachableResidual R H s T e.1.1 e.1.2

theorem allKeysReachable_empty (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : AllKeysReachable R H s T emptyCache := by
  simp [AllKeysReachable, emptyCache]

theorem allKeysReachable_insert (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) (q : Key n) (answer : Answer n)
    (hc : AllKeysReachable R H s T cache)
    (hq : ReachableResidual R H s T q.1 q.2) :
    AllKeysReachable R H s T (insert cache q answer) := by
  intro e he
  simp only [TreeBudgetMemoState.insert, List.mem_cons, List.mem_filter, decide_eq_true_eq] at he
  rcases he with rfl | he
  · exact hq
  · exact hc e he.1

end UAVProof.TreeBudgetMemoReachability

#print axioms UAVProof.TreeBudgetMemoReachability.reachable_invariants
#print axioms UAVProof.TreeBudgetMemoReachability.reachable_root
#print axioms UAVProof.TreeBudgetMemoReachability.reachable_root_zero
#print axioms UAVProof.TreeBudgetMemoReachability.allKeysReachable_empty
#print axioms UAVProof.TreeBudgetMemoReachability.allKeysReachable_insert
