import LeanCompletion.UAV.TreeBudgetBranchCertificate
import LeanCompletion.UAV.TreeBudgetChecker

/-! Search each depot branch with the existing complete reference search, then
merge the returned certificates. No local-search optimization is assumed. -/
namespace UAVProof.TreeBudgetBranchSearch
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetRootFactorization TreeBudgetBranchCertificate TreeBudgetFiniteSearch
open TreeBudgetChecker TreeBudgetCriterion
variable {n : ℕ}

def searchBranch (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) : Option (Certificate (Fin n)) :=
  search R (branchMultiplicity R h c) (h c.val) s T

theorem searchBranch_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (C : Certificate (Fin n))
    (hc : searchBranch R h s T c = some C) :
    checkCertificate R (branchMultiplicity R h c) (h c.val) s T C = true :=
  search_sound R _ _ s T C hc

theorem searchBranch_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) :
    (searchBranch R h s T c).isSome = true ↔
      MatrixFeasible R (branchMultiplicity R h c) (h c.val) s T :=
  search_correct R _ _ s T

/-- The default empty certificates have no validity claim outside the processed list. -/
def collectBranches (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : List (RootChild R) →
    Option (RootChild R → Certificate (Fin n))
  | [] => some (fun _ => ofEntries [])
  | c :: xs => (searchBranch R h s T c).bind fun C =>
      (collectBranches R h s T xs).map (fun cs => Function.update cs c C)

theorem collectBranches_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (RootChild R))
    (cs : RootChild R → Certificate (Fin n))
    (hc : collectBranches R h s T xs = some cs) :
    ∀ c ∈ xs, checkCertificate R (branchMultiplicity R h c) (h c.val) s T (cs c) = true := by
  induction xs generalizing cs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨C, hC, hs⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨ds, hds, rfl⟩ := Option.map_eq_some_iff.mp hs
    intro c hc
    by_cases he : c = a
    · subst c
      simpa using searchBranch_sound R h s T a C hC
    · have hm : c ∈ xs := by simpa [he] using hc
      simpa [Function.update_of_ne he] using ih ds hds c hm

theorem collectBranches_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (RootChild R)) :
    (collectBranches R h s T xs).isSome = true ↔
      ∀ c ∈ xs, (searchBranch R h s T c).isSome = true := by
  induction xs with
  | nil => simp [collectBranches]
  | cons c xs ih =>
    cases hb : searchBranch R h s T c with
    | none => simp [collectBranches, hb]
    | some C => simp [collectBranches, hb, ih]

def searchByRoot (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  if m = rootCount R h then
    (collectBranches R h s T (rootChildren R)).map (mergeBranches R)
  else none

theorem searchByRoot_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchByRoot R h m s T = some C) : checkCertificate R h m s T C = true := by
  have hm : m = rootCount R h := by
    by_contra hn
    simp [searchByRoot, hn] at hc
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp (by simpa [searchByRoot, hm] using hc)
  exact mergeBranches_checked R h m s T cs hm
    (fun c => collectBranches_sound R h s T _ cs hcs c (mem_rootChildren R c))

theorem searchByRoot_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRoot R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  rw [matrix_iff_branch_matrices]
  by_cases hm : m = rootCount R h
  · simp only [searchByRoot, hm, ite_true, Option.isSome_map, collectBranches_correct, true_and]
    constructor
    · intro hc c
      exact (searchBranch_correct R h s T c).mp (hc c (mem_rootChildren R c))
    · intro hc c _
      exact (searchBranch_correct R h s T c).mpr (hc c)
  · simp [searchByRoot, hm]

theorem searchByRoot_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : searchByRoot R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  rw [← searchByRoot_correct]
  cases searchByRoot R h m s T <;> simp

theorem searchByRoot_isSome_eq_search (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRoot R h m s T).isSome = (search R h m s T).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (searchByRoot_correct R h m s T).trans (search_correct R h m s T).symm

/-- Demand input retains the existing integer compatibility check before any search. -/
def solveByRoot (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  if compatible R d m then searchByRoot R (multiplicities R d) m s T else none

def checkTreeBudgetByRoot (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Bool := (solveByRoot R d m s T).isSome

theorem checkTreeBudgetByRoot_correct (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    checkTreeBudgetByRoot R d m s T = true ↔ BudgetRoutes R d m s T := by
  rw [budget_routes_iff]
  by_cases hc : compatible R d m = true
  · have hcomp := (compatible_eq_true_iff R d m).mp hc
    simp [checkTreeBudgetByRoot, solveByRoot, hc, searchByRoot_correct, multiplicities_eq, hcomp]
  · have hcomp : ¬ FlowCompatible R d m := by simpa using hc
    simp [checkTreeBudgetByRoot, solveByRoot, hc, hcomp]

theorem solveByRoot_sound (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : solveByRoot R d m s T = some C) :
    FlowCompatible R d m ∧ checkCertificate R (multiplicities R d) m s T C = true ∧
      BudgetRoutes R d m s T := by
  have ht : compatible R d m = true := by
    by_contra hn
    simp [solveByRoot, hn] at hc
  have hs : searchByRoot R (multiplicities R d) m s T = some C := by
    simpa [solveByRoot, ht] using hc
  refine ⟨(compatible_eq_true_iff ..).mp ht, searchByRoot_sound _ _ _ _ _ C hs, ?_⟩
  apply (checkTreeBudgetByRoot_correct ..).mp
  simp [checkTreeBudgetByRoot, hc]

theorem solveByRoot_none_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : solveByRoot R d m s T = none ↔ ¬ BudgetRoutes R d m s T := by
  rw [← checkTreeBudgetByRoot_correct]
  unfold checkTreeBudgetByRoot
  cases solveByRoot R d m s T <;> simp

end UAVProof.TreeBudgetBranchSearch

#print axioms UAVProof.TreeBudgetBranchSearch.collectBranches_sound
#print axioms UAVProof.TreeBudgetBranchSearch.collectBranches_correct
#print axioms UAVProof.TreeBudgetBranchSearch.searchByRoot_sound
#print axioms UAVProof.TreeBudgetBranchSearch.searchByRoot_correct
#print axioms UAVProof.TreeBudgetBranchSearch.searchByRoot_none_iff
#print axioms UAVProof.TreeBudgetBranchSearch.searchByRoot_isSome_eq_search
#print axioms UAVProof.TreeBudgetBranchSearch.checkTreeBudgetByRoot_correct
#print axioms UAVProof.TreeBudgetBranchSearch.solveByRoot_sound
#print axioms UAVProof.TreeBudgetBranchSearch.solveByRoot_none_iff
