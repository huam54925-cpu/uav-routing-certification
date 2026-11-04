import LeanCompletion.UAV.TreeBudgetMemoSearch
import LeanCompletion.UAV.TreeBudgetCertificateCompression

/-! Memoized search at the original multiplicity and demand interfaces.
Each branch starts with its own empty cache, keeping the fixed input in the
cache contract isolated. Only initial residual witnesses become certificates. -/
namespace UAVProof.TreeBudgetMemoIntegration
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetRootFactorization TreeBudgetBranchCertificate TreeBudgetResidualSearch
open TreeBudgetChecker TreeBudgetCriterion TreeBudgetMemoState TreeBudgetMemoSearch
open TreeBudgetCertificateCompression
variable {n : ℕ}

/-- Normalize the root coordinate and start an input-local cache. -/
def searchMemo (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (memoRows R (normalize R h) s T m (normalize R h) emptyCache).1.map unitCertificate

theorem searchMemo_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchMemo R h m s T = some C) : checkCertificate R h m s T C = true := by
  obtain ⟨rows, hs, rfl⟩ := Option.map_eq_some_iff.mp hc
  have hw := (memoRows_spec R (normalize R h) s T m (normalize R h) emptyCache
    (cacheValid_empty R (normalize R h) s T)).2
  rw [hs] at hw
  exact (checkCertificate_eq_true_iff ..).mpr (initial_witness_valid R h s T m rows hw)

theorem searchMemo_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchMemo R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  rw [searchMemo, Option.isSome_map,
    memoRows_correct R (normalize R h) s T m (normalize R h) emptyCache
      (cacheValid_empty R (normalize R h) s T), initial_iff_matrix]

theorem searchMemo_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    searchMemo R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  rw [← searchMemo_correct]
  cases searchMemo R h m s T <;> simp

theorem searchMemo_isSome_eq_reference (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchMemo R h m s T).isSome = (TreeBudgetResidualSearch.search R h m s T).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (searchMemo_correct ..).trans (TreeBudgetResidualSearch.search_correct ..).symm

/-- Every call to a branch solver initializes a separate cache. -/
def searchBranchMemo (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) : Option (Certificate (Fin n)) :=
  searchMemo R (branchMultiplicity R h c) (h c.val) s T

theorem searchBranchMemo_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (C : Certificate (Fin n))
    (hc : searchBranchMemo R h s T c = some C) :
    checkCertificate R (branchMultiplicity R h c) (h c.val) s T C = true :=
  searchMemo_sound R _ _ s T C hc

theorem searchBranchMemo_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) :
    (searchBranchMemo R h s T c).isSome = true ↔
      MatrixFeasible R (branchMultiplicity R h c) (h c.val) s T :=
  searchMemo_correct R _ _ s T

/-- The default empty certificates have no validity claim outside the processed list. -/
def collectBranchesMemo (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : List (RootChild R) →
    Option (RootChild R → Certificate (Fin n))
  | [] => some (fun _ => ofEntries [])
  | c :: xs => (searchBranchMemo R h s T c).bind fun C =>
      (collectBranchesMemo R h s T xs).map (fun cs => Function.update cs c C)

theorem collectBranchesMemo_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (RootChild R))
    (cs : RootChild R → Certificate (Fin n))
    (hc : collectBranchesMemo R h s T xs = some cs) :
    ∀ c ∈ xs, checkCertificate R (branchMultiplicity R h c) (h c.val) s T (cs c) = true := by
  induction xs generalizing cs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨C, hC, hs⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨ds, hds, rfl⟩ := Option.map_eq_some_iff.mp hs
    intro c hc
    by_cases he : c = a
    · subst c
      simpa using searchBranchMemo_sound R h s T a C hC
    · have hm : c ∈ xs := by simpa [he] using hc
      simpa [Function.update_of_ne he] using ih ds hds c hm

theorem collectBranchesMemo_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (RootChild R)) :
    (collectBranchesMemo R h s T xs).isSome = true ↔
      ∀ c ∈ xs, (searchBranchMemo R h s T c).isSome = true := by
  induction xs with
  | nil => simp [collectBranchesMemo]
  | cons c xs ih =>
    cases hb : searchBranchMemo R h s T c with
    | none => simp [collectBranchesMemo, hb]
    | some C => simp [collectBranchesMemo, hb, ih]

def searchByRootMemo (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  if m = rootCount R h then
    (collectBranchesMemo R h s T (rootChildren R)).map (mergeBranches R)
  else none

theorem searchByRootMemo_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchByRootMemo R h m s T = some C) : checkCertificate R h m s T C = true := by
  have hm : m = rootCount R h := by
    by_contra hn
    simp [searchByRootMemo, hn] at hc
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp (by simpa [searchByRootMemo, hm] using hc)
  exact mergeBranches_checked R h m s T cs hm
    (fun c => collectBranchesMemo_sound R h s T _ cs hcs c (mem_rootChildren R c))

theorem searchByRootMemo_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRootMemo R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  rw [matrix_iff_branch_matrices]
  by_cases hm : m = rootCount R h
  · simp only [searchByRootMemo, hm, ite_true, Option.isSome_map,
      collectBranchesMemo_correct, true_and]
    constructor
    · intro hc c
      exact (searchBranchMemo_correct R h s T c).mp (hc c (mem_rootChildren R c))
    · intro hc c _
      exact (searchBranchMemo_correct R h s T c).mpr (hc c)
  · simp [searchByRootMemo, hm]

theorem searchByRootMemo_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : searchByRootMemo R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  rw [← searchByRootMemo_correct]
  cases searchByRootMemo R h m s T <;> simp

theorem searchByRootMemo_isSome_eq_search (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRootMemo R h m s T).isSome = (searchMemo R h m s T).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (searchByRootMemo_correct R h m s T).trans (searchMemo_correct R h m s T).symm

/-- Demand input retains the existing integer compatibility check before searching. -/
def solveByRootMemo (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  if compatible R d m then searchByRootMemo R (multiplicities R d) m s T else none

def checkTreeBudgetByRootMemo (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Bool := (solveByRootMemo R d m s T).isSome

theorem checkTreeBudgetByRootMemo_correct (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    checkTreeBudgetByRootMemo R d m s T = true ↔ BudgetRoutes R d m s T := by
  rw [budget_routes_iff]
  by_cases hc : compatible R d m = true
  · have hcomp := (compatible_eq_true_iff R d m).mp hc
    simp [checkTreeBudgetByRootMemo, solveByRootMemo, hc, searchByRootMemo_correct,
      multiplicities_eq, hcomp]
  · have hcomp : ¬ FlowCompatible R d m := by simpa using hc
    simp [checkTreeBudgetByRootMemo, solveByRootMemo, hc, hcomp]

theorem solveByRootMemo_sound (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : solveByRootMemo R d m s T = some C) :
    FlowCompatible R d m ∧ checkCertificate R (multiplicities R d) m s T C = true ∧
      BudgetRoutes R d m s T := by
  have ht : compatible R d m = true := by
    by_contra hn
    simp [solveByRootMemo, hn] at hc
  have hs : searchByRootMemo R (multiplicities R d) m s T = some C := by
    simpa [solveByRootMemo, ht] using hc
  refine ⟨(compatible_eq_true_iff ..).mp ht, searchByRootMemo_sound _ _ _ _ _ C hs, ?_⟩
  apply (checkTreeBudgetByRootMemo_correct ..).mp
  simp [checkTreeBudgetByRootMemo, hc]

theorem solveByRootMemo_correct (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (solveByRootMemo R d m s T).isSome = true ↔ BudgetRoutes R d m s T :=
  checkTreeBudgetByRootMemo_correct R d m s T

theorem solveByRootMemo_none_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : solveByRootMemo R d m s T = none ↔ ¬ BudgetRoutes R d m s T := by
  rw [← checkTreeBudgetByRootMemo_correct]
  unfold checkTreeBudgetByRootMemo
  cases solveByRootMemo R d m s T <;> simp

theorem searchByRootMemo_isSome_eq_reference (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRootMemo R h m s T).isSome =
      (TreeBudgetResidualBranchSearch.searchByRoot R h m s T).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (searchByRootMemo_correct ..).trans
    (TreeBudgetResidualBranchSearch.searchByRoot_correct ..).symm

theorem checkTreeBudgetByRootMemo_eq_reference (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    checkTreeBudgetByRootMemo R d m s T =
      TreeBudgetResidualBranchSearch.checkTreeBudgetByRoot R d m s T := by
  apply Bool.eq_iff_iff.mpr
  exact (checkTreeBudgetByRootMemo_correct ..).trans
    (TreeBudgetResidualBranchSearch.checkTreeBudgetByRoot_correct ..).symm

theorem solveByRootMemo_isSome_eq_reference (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (solveByRootMemo R d m s T).isSome =
      (TreeBudgetResidualBranchSearch.solveByRoot R d m s T).isSome :=
  checkTreeBudgetByRootMemo_eq_reference R d m s T

def searchMemoCompressed (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (searchMemo R h m s T).map compressCertificate

def searchByRootMemoCompressed (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (searchByRootMemo R h m s T).map compressCertificate

def solveByRootMemoCompressed (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (solveByRootMemo R d m s T).map compressCertificate

theorem searchMemoCompressed_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchMemoCompressed R h m s T = some C) : checkCertificate R h m s T C = true := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact compress_checked R h m s T D (searchMemo_sound R h m s T D hd)

theorem searchMemoCompressed_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchMemoCompressed R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  simpa [searchMemoCompressed] using searchMemo_correct R h m s T

theorem searchMemoCompressed_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    searchMemoCompressed R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  simpa [searchMemoCompressed] using searchMemo_none_iff R h m s T

theorem searchByRootMemoCompressed_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchByRootMemoCompressed R h m s T = some C) :
    checkCertificate R h m s T C = true := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact compress_checked R h m s T D
    (searchByRootMemo_sound R h m s T D hd)

theorem searchByRootMemoCompressed_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRootMemoCompressed R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  simpa [searchByRootMemoCompressed] using searchByRootMemo_correct R h m s T

theorem searchByRootMemoCompressed_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    searchByRootMemoCompressed R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  simpa [searchByRootMemoCompressed] using
    searchByRootMemo_none_iff R h m s T

theorem solveByRootMemoCompressed_sound (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : solveByRootMemoCompressed R d m s T = some C) :
    FlowCompatible R d m ∧
      checkCertificate R (TreeBudgetChecker.multiplicities R d) m s T C = true ∧
      BudgetRoutes R d m s T := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨hcomp, hcheck, hbudget⟩ := solveByRootMemo_sound R d m s T D hd
  exact ⟨hcomp, compress_checked R _ m s T D hcheck, hbudget⟩

theorem solveByRootMemoCompressed_correct (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (solveByRootMemoCompressed R d m s T).isSome = true ↔ BudgetRoutes R d m s T := by
  simpa [solveByRootMemoCompressed, checkTreeBudgetByRootMemo] using
    checkTreeBudgetByRootMemo_correct R d m s T

theorem solveByRootMemoCompressed_none_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    solveByRootMemoCompressed R d m s T = none ↔ ¬ BudgetRoutes R d m s T := by
  simpa [solveByRootMemoCompressed] using solveByRootMemo_none_iff R d m s T

end UAVProof.TreeBudgetMemoIntegration

#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemo_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemo_none_iff
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemo_isSome_eq_reference
#print axioms UAVProof.TreeBudgetMemoIntegration.searchBranchMemo_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.searchBranchMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.collectBranchesMemo_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.collectBranchesMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemo_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemo_none_iff
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemo_isSome_eq_search
#print axioms UAVProof.TreeBudgetMemoIntegration.checkTreeBudgetByRootMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemo_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemo_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemo_none_iff
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemo_isSome_eq_reference
#print axioms UAVProof.TreeBudgetMemoIntegration.checkTreeBudgetByRootMemo_eq_reference
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemo_isSome_eq_reference
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemoCompressed_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemoCompressed_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.searchMemoCompressed_none_iff
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemoCompressed_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemoCompressed_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.searchByRootMemoCompressed_none_iff
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemoCompressed_sound
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemoCompressed_correct
#print axioms UAVProof.TreeBudgetMemoIntegration.solveByRootMemoCompressed_none_iff
