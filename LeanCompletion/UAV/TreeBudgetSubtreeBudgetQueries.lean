import LeanCompletion.UAV.TreeBudgetSubtreeBudgetProfile

/-! Public multi-budget entry point. Prepare once, then query the retained root
witnesses at different rational budgets. The comparison counter measures only
threshold tests. A successful lookup builds just the selected certificate. -/
namespace UAVProof.TreeBudgetSubtreeBudgetProfile
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeAutoScaleSeed
open TreeBudgetSubtreeResource (rootMass)

variable {N : Nat}

inductive Queries (R : RootedTree (Fin N)) where
  | fixed (answer : Option (TreeBudgetCertificate.Certificate (Fin N)))
  | indexed (k scale : Nat) (entries : List (Int × Root N (k+1)))

def prepareQueries (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) :
    Queries R :=
  if m = rootMass R H then
    match m with
    | 0 => .fixed (solveAuto R H s 0 0)
    | k+1 =>
      let p := prepare R s 0
      .indexed k p.scale (buildProfile R H (val p.weight) k)
  else .fixed none

private def scanBudget {α : Type} (B : Int) : List (Int × α) → Option (Int × α) × Nat
  | [] => (none, 0)
  | e :: es =>
    if e.1 ≤ B then (some e, 1)
    else let r := scanBudget B es; (r.1, r.2+1)

private theorem scanBudget_spec {α : Type} (B : Int) (xs : List (Int × α)) :
    (scanBudget B xs).1 = query B xs ∧ (scanBudget B xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl, le_rfl⟩
  | cons e es ih =>
    by_cases he : e.1 ≤ B <;> simp [scanBudget, query, he, ih.1, ih.2]

def Queries.lookup {R : RootedTree (Fin N)} (table : Queries R) (T : Rat) :
    Option (TreeBudgetCertificate.Certificate (Fin N)) × Nat :=
  match table with
  | .fixed answer => (answer, 0)
  | .indexed _ scale entries =>
    let r := scanBudget (TreeBudgetSubtreeInteger.floorBudget scale T) entries
    ((r.1.map Prod.snd).map (certificate R), r.2)

def Queries.breakpoints {R : RootedTree (Fin N)} : Queries R → Nat
  | .fixed _ => 0
  | .indexed _ _ xs => xs.length

theorem lookup_comparisons {R : RootedTree (Fin N)} (table : Queries R) (T : Rat) :
    (table.lookup T).2 ≤ table.breakpoints := by
  cases table with
  | fixed => exact le_rfl
  | indexed k scale entries => exact (scanBudget_spec _ entries).2

/-- The check precedes automatic scaling and construction of the root table. -/
theorem prepareQueries_reject (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (hm : m ≠ rootMass R H) :
    prepareQueries R H s m = .fixed none := by simp only [prepareQueries, if_neg hm]

theorem lookup_eq_auto (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) :
    ((prepareQueries R H s m).lookup T).1 = solveAuto R H s m T := by
  by_cases hm : m = rootMass R H
  · unfold prepareQueries
    rw [if_pos hm]
    cases m with
    | zero => exact (solveAuto_zero_budget_independent R H s T).symm
    | succ k =>
      dsimp only [Queries.lookup]
      rw [(scanBudget_spec ..).1]
      exact profile_query_eq_auto R H s k T
  · rw [prepareQueries_reject R H s m hm]
    symm
    apply (solveAuto_none_iff ..).mpr
    exact fun hf => hm (TreeBudgetSubtreeResource.matrixFeasible_rootMass R H s m T hf)

end UAVProof.TreeBudgetSubtreeBudgetProfile
