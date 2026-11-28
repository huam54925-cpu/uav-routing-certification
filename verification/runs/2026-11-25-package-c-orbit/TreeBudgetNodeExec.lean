import TreeBudgetPrefixExec
import TreeBudgetPrefixMerge

/-!
# Package C (Issue #26) — C3 Executable Complete Non-Root Node (`topRows`, `nodeExec`)

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetPrefixExec` and `TreeBudgetPrefixMerge`.

Contents:
1. Executable enumerator `topRows` (reusing `rowChoices`) and complete non-root node
   generator `nodeExec`.
2. Exact enumeration lemmas: `mem_topRows_length`, `ofFn_mem_topRows_iff`.
3. Node interface theorems: `validHistEntries_of_mem_nodeExec` and
   `exists_mem_nodeExec_iff_childHist`, chaining `exists_mem_prefixFoldExec_iff_prefixReach`
   and `childHist_iff_fullPrefixReach`.
4. Two boundary regressions:
   - `m = 0`: `d = 0 → [[]]`, `d > 0 → []`;
   - `m = 2, d = 2`: root child gets only `[[1, 1]]`, deeper node gets `[[0, 2], [1, 1], [2, 0]]`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

section NodeDefinitions

/-- Enumerate all legal top-edge count rows of length `m` summing to `d`, capping each
entry at `1` for direct children of the root and at `d` for deeper vertices. -/
def topRows (m d : ℕ) (isRootChild : Bool) : List (List ℕ) :=
  let cap := if isRootChild then 1 else d
  rowChoices d (List.replicate m (true, cap))

/-- Executable candidate table for a complete non-root vertex given its child tables. -/
def nodeExec {V : Type*} (m d : ℕ) (isRootChild : Bool) (w : ℚ)
    (tables : V → List HistEntries) (us : List V) : List HistEntries :=
  (topRows m d isRootChild).flatMap fun row =>
    let q : Fin m → ℕ := fun i => row.getD i.val 0
    prefixFoldExec tables us (seedEntries w q)

end NodeDefinitions

section TopRowsExactness

theorem forall₂_replicate_iff {α β : Type*} (R : α → β → Prop) (l : List α) (m : ℕ) (b : β) :
    List.Forall₂ R l (List.replicate m b) ↔ l.length = m ∧ ∀ x ∈ l, R x b := by
  induction m generalizing l with
  | zero =>
    simp only [List.replicate_zero, List.forall₂_nil_right_iff]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ h => (List.not_mem_nil h).elim⟩
    · rintro ⟨hlen, _⟩; exact List.eq_nil_of_length_eq_zero hlen
  | succ m ih =>
    simp only [List.replicate_succ, List.forall₂_cons_right_iff]
    constructor
    · rintro ⟨a, tail, ha, htail, rfl⟩
      obtain ⟨htlen, htm⟩ := (ih tail).mp htail
      refine ⟨by simp [htlen], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hrest
      · exact ha
      · exact htm x hrest
    · rintro ⟨hlen, hall⟩
      cases l with
      | nil => simp at hlen
      | cons a tail =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        refine ⟨a, tail, hall a (List.mem_cons_self ..), ?_, rfl⟩
        exact (ih tail).mpr ⟨hlen, fun x hx => hall x (List.mem_cons_of_mem a hx)⟩

/-- Every row emitted by `topRows m d isRootChild` has exact length `m`. -/
theorem mem_topRows_length {m d : ℕ} {isRootChild : Bool} {row : List ℕ}
    (hrow : row ∈ topRows m d isRootChild) : row.length = m := by
  unfold topRows at hrow
  obtain ⟨_, hfor⟩ := (mem_rowChoices_iff d _ row).mp hrow
  exact ((forall₂_replicate_iff _ row m _).mp hfor).1

theorem sum_ofFn_eq_fin_sum {m : ℕ} (q : Fin m → ℕ) :
    (List.ofFn q).sum = ∑ i : Fin m, q i := by
  rw [List.ofFn_eq_map]
  have huniv : (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := rfl
  change ((List.finRange m).map q).sum = ((Finset.univ : Finset (Fin m)).val.map q).sum
  rw [huniv, Multiset.map_coe, Multiset.sum_coe]

theorem ofFn_getD_eq_self {m : ℕ} (row : List ℕ) (hlen : row.length = m) :
    List.ofFn (fun i : Fin m => row.getD i.val 0) = row := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem row 0 hi2

/-- Step 1: Exactness of `topRows` against `(∑ i, q i) = H v ∧ RootChildCap R v q`. -/
theorem ofFn_mem_topRows_iff {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (v : V) (q : Fin m → ℕ) :
    List.ofFn q ∈ topRows m (H v) (decide (R.parent v = R.root)) ↔
      (∑ i : Fin m, q i) = H v ∧ RootChildCap R v q := by
  unfold topRows RootChildCap
  rw [mem_rowChoices_iff, forall₂_replicate_iff, sum_ofFn_eq_fin_sum]
  simp only [List.length_ofFn, true_and, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, Bool.true_eq_false, false_imp_iff, and_true]
  constructor
  · rintro ⟨hsum, hle⟩
    refine ⟨hsum, ?_⟩
    intro hr i
    have h1 := hle i
    simpa [hr] using h1
  · rintro ⟨hsum, hcap⟩
    refine ⟨hsum, ?_⟩
    intro i
    by_cases hr : R.parent v = R.root
    · simpa [hr] using hcap hr i
    · simp only [decide_eq_false hr, Bool.false_eq_true, ↓reduceIte]
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)

end TopRowsExactness

section NodeInterface

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem validHistEntries_of_mem_foldl_advanceExec
    (tables : V → List HistEntries) (us : List V)
    (prev : List HistEntries) (hprevV : ∀ p ∈ prev, ValidHistEntries p)
    (out : HistEntries)
    (hout : out ∈ us.foldl (fun acc u => advanceExec acc (tables u)) prev) :
    ValidHistEntries out := by
  induction us generalizing prev with
  | nil =>
    exact hprevV out hout
  | cons u us ih =>
    simp only [List.foldl_cons] at hout
    exact ih (advanceExec prev (tables u))
      (fun x hx => validHistEntries_of_mem_advanceExec prev (tables u) x hx) hout

omit [Fintype V] [DecidableEq V] in
/-- Every output emitted by `nodeExec` satisfies `ValidHistEntries`, ready for the parent layer. -/
theorem validHistEntries_of_mem_nodeExec (m d : ℕ) (isRootChild : Bool) (w : ℚ)
    (tables : V → List HistEntries) (us : List V)
    (out : HistEntries) (hout : out ∈ nodeExec m d isRootChild w tables us) :
    ValidHistEntries out := by
  unfold nodeExec at hout
  rcases List.mem_flatMap.mp hout with ⟨row, _, hfold⟩
  apply validHistEntries_of_mem_foldl_advanceExec tables us _ _ out hfold
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact validHistEntries_seedEntries w (fun i => row.getD i.val 0)

/-- Step 2 (Main Node Interface Theorem):
For any non-root vertex `v` and duplicate-free list `us` covering `R.children v`,
given valid child candidate tables covering `ChildHist`, `nodeExec` denotes exactly
`ChildHist R H m s v`. -/
theorem exists_mem_nodeExec_iff_childHist
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (hv : v ≠ R.root) (tables : V → List HistEntries) (us : List V)
    (hd : us.Nodup) (hcover : us.toFinset = R.children v)
    (htablesV : ∀ u ∈ us, ∀ c ∈ tables u, ValidHistEntries c)
    (htables : ∀ u ∈ us, ∀ h, (∃ c ∈ tables u, denoteHist c = h) ↔ ChildHist R H m s u h)
    (h : OrbitHist) :
    (∃ out ∈ nodeExec m (H v) (decide (R.parent v = R.root)) (linearWeight R s v) tables us,
      denoteHist out = h) ↔
      ChildHist R H m s v h := by
  rw [childHist_iff_fullPrefixReach R H s v hv us hd hcover h]
  unfold nodeExec
  constructor
  · rintro ⟨out, hout, rfl⟩
    rcases List.mem_flatMap.mp hout with ⟨row, hrow, hfold⟩
    let q : Fin m → ℕ := fun i => row.getD i.val 0
    have hlen : row.length = m := mem_topRows_length hrow
    have hqMem : List.ofFn q ∈ topRows m (H v) (decide (R.parent v = R.root)) := by
      rwa [ofFn_getD_eq_self row hlen]
    obtain ⟨hsum, hcap⟩ := (ofFn_mem_topRows_iff R H v q).mp hqMem
    refine ⟨q, hsum, hcap, ?_⟩
    exact (exists_mem_prefixFoldExec_iff_prefixReach R H s v q tables us htablesV htables _).mp
      ⟨out, hfold, rfl⟩
  · rintro ⟨q, hsum, hcap, hreach⟩
    have hqMem : List.ofFn q ∈ topRows m (H v) (decide (R.parent v = R.root)) :=
      (ofFn_mem_topRows_iff R H v q).mpr ⟨hsum, hcap⟩
    obtain ⟨out, hfold, hout⟩ :=
      (exists_mem_prefixFoldExec_iff_prefixReach R H s v q tables us htablesV htables h).mpr hreach
    have hqEq : (fun i : Fin m => (List.ofFn q).getD i.val 0) = q := by
      funext i
      have hi : i.val < (List.ofFn q).length := by simp
      rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
    refine ⟨out, ?_, hout⟩
    apply List.mem_flatMap.mpr
    refine ⟨List.ofFn q, hqMem, ?_⟩
    simpa only [hqEq] using hfold

end NodeInterface

section BoundaryRegressions

/-! ### Regression 1: `m = 0` (`d = 0 → [[]]`, `d > 0 → []`) -/

theorem exTopRows_m0_d0 (isRootChild : Bool) :
    topRows 0 0 isRootChild = [[]] := by
  cases isRootChild <;> decide

theorem exTopRows_m0_dpos (d : ℕ) (hd : 0 < d) (isRootChild : Bool) :
    topRows 0 d isRootChild = [] := by
  unfold topRows
  simp [rowChoices, Nat.ne_of_gt hd]

/-! ### Regression 2: `m = 2, d = 2` (root child vs deeper vertex) -/

theorem exTopRows_m2_d2_rootChild :
    topRows 2 2 true = [[1, 1]] := by
  decide

theorem exTopRows_m2_d2_deeper :
    topRows 2 2 false = [[0, 2], [1, 1], [2, 0]] := by
  decide

end BoundaryRegressions

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.mem_topRows_length
#print axioms UAVProof.TreeBudgetOrbitPrototype.ofFn_mem_topRows_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.validHistEntries_of_mem_nodeExec
#print axioms UAVProof.TreeBudgetOrbitPrototype.exists_mem_nodeExec_iff_childHist
#print axioms UAVProof.TreeBudgetOrbitPrototype.exTopRows_m0_d0
#print axioms UAVProof.TreeBudgetOrbitPrototype.exTopRows_m0_dpos
#print axioms UAVProof.TreeBudgetOrbitPrototype.exTopRows_m2_d2_rootChild
#print axioms UAVProof.TreeBudgetOrbitPrototype.exTopRows_m2_d2_deeper
