import LeanCompletion.UAV.TreeBudgetFiniteSearch
import LeanCompletion.UAV.TreeBudgetBranchCertificate

/-! Uncached residual search. Row legality always refers to the fixed input H;
intermediate witnesses cover only r. Candidates are reused at every depth. -/
namespace UAVProof.TreeBudgetResidualSearch
open TreeFlowExistence TreeBudgetRow TreeBudgetPatterns TreeBudgetMatrix
open TreeBudgetCertificate TreeBudgetBranchCertificate
variable {n : ℕ}

def ResidualWitness (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (rows : List (Fin n → ℕ)) : Prop :=
  rows.length = k ∧ (∀ p ∈ rows, RowValid R H s T p) ∧
    ∀ v, (rows.map (fun p => p v)).sum = r v

def ResidualFeasible (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) : Prop :=
  ∃ rows, ResidualWitness R H s T k r rows

theorem residualFeasible_zero_iff (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (r : Fin n → ℕ) :
    ResidualFeasible R H s T 0 r ↔ r = 0 := by
  constructor
  · rintro ⟨rows, hl, _, hc⟩
    have he : rows = [] := List.length_eq_zero_iff.mp hl
    subst rows
    funext v
    simpa using (hc v).symm
  · rintro rfl
    exact ⟨[], by simp [ResidualWitness]⟩

theorem residualWitness_cons_iff (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r p : Fin n → ℕ)
    (rows : List (Fin n → ℕ)) :
    ResidualWitness R H s T (k + 1) r (p :: rows) ↔
      RowValid R H s T p ∧ p ≤ r ∧
        ResidualWitness R H s T k (r - p) rows := by
  constructor
  · rintro ⟨hl, hp, hc⟩
    refine ⟨hp p (by simp), ?_, ?_, ?_, ?_⟩
    · intro v
      have hv := hc v
      simp only [List.map_cons, List.sum_cons] at hv
      change p v ≤ r v
      omega
    · simpa using hl
    · intro q hq; exact hp q (by simp [hq])
    · intro v
      have hv := hc v
      simp only [List.map_cons, List.sum_cons] at hv
      change (rows.map (fun q => q v)).sum = r v - p v
      omega
  · rintro ⟨hp, hle, hl, hrows, hc⟩
    refine ⟨by simp [hl], ?_, ?_⟩
    · simpa using And.intro hp hrows
    · intro v
      simp only [List.map_cons, List.sum_cons, hc, Pi.sub_apply]
      exact Nat.add_sub_of_le (hle v)

theorem residualFeasible_succ_iff (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) :
    ResidualFeasible R H s T (k + 1) r ↔
      ∃ p, RowValid R H s T p ∧ p ≤ r ∧ ResidualFeasible R H s T k (r - p) := by
  constructor
  · rintro ⟨rows, hw⟩
    cases rows with
    | nil => simp [ResidualWitness] at hw
    | cons p rows =>
      obtain ⟨hp, hle, ht⟩ := (residualWitness_cons_iff ..).mp hw
      exact ⟨p, hp, hle, rows, ht⟩
  · rintro ⟨p, hp, hle, rows, ht⟩
    exact ⟨p :: rows, (residualWitness_cons_iff ..).mpr ⟨hp, hle, ht⟩⟩

theorem residualFeasible_succ_pattern_iff (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) :
    ResidualFeasible R H s T (k + 1) r ↔
      ∃ p : Pattern R H s T, values p.val ≤ r ∧
        ResidualFeasible R H s T k (r - values p.val) := by
  rw [residualFeasible_succ_iff]
  constructor
  · rintro ⟨p, hp, hle, ht⟩
    obtain ⟨q, hq⟩ := rowValid_exists_pattern R H s T p hp
    exact ⟨q, hq ▸ hle, hq ▸ ht⟩
  · rintro ⟨p, hle, ht⟩
    exact ⟨values p.val, ⟨values_root _, fun _ hv => values_le _ hv, p.property⟩, hle, ht⟩

theorem rootCount_list_sum (R : RootedTree (Fin n)) (rows : List (Fin n → ℕ)) :
    rootCount R (fun v => (rows.map (fun p => p v)).sum) =
      (rows.map (rootCount R)).sum := by
  induction rows with
  | nil => simp [rootCount]
  | cons p rows ih =>
    simp only [List.map_cons, List.sum_cons]
    change (∑ w ∈ children R R.root, (p w + (rows.map (fun q => q w)).sum)) = _
    rw [Finset.sum_add_distrib]
    exact congrArg (rootCount R p + ·) ih

theorem residualWitness_rootCount (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (rows : List (Fin n → ℕ)) (hw : ResidualWitness R H s T k r rows) :
    k = rootCount R r := by
  have he : (rows.map (rootCount R)).sum = rows.length := by
    have hm : rows.map (rootCount R) = rows.map (fun _ => 1) := by
      apply List.map_congr_left
      intro p hp
      exact (hw.2.1 p hp).2.2.1
    rw [hm]
    simp
  rw [← hw.1, ← he, ← rootCount_list_sum, funext hw.2.2]

/-- Count and upper-bound invariants survive every guarded transition, even
when that transition eventually leads to a dead end. -/
theorem transition_invariants (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r p : Fin n → ℕ)
    (hp : RowValid R H s T p) (hle : p ≤ r) (hr : r ≤ H)
    (hk : k + 1 = rootCount R r) :
    k = rootCount R (r - p) ∧ r - p ≤ H := by
  have he : rootCount R p + rootCount R (r - p) = rootCount R r := by
    rw [rootCount, rootCount, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact Nat.add_sub_of_le (hle v)
  rw [hp.2.2.1] at he
  exact ⟨by omega, fun v => (Nat.sub_le _ _).trans (hr v)⟩

@[simp] theorem rowValid_normalize_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (p : Fin n → ℕ) :
    RowValid R (normalize R h) s T p ↔ RowValid R h s T p := by
  constructor <;> rintro ⟨hroot, hb, ht⟩ <;> refine ⟨hroot, ?_, ht⟩
  · intro v hv
    simpa only [normalize_nonroot R h hv] using hb v hv
  · intro v hv
    simpa only [normalize_nonroot R h hv] using hb v hv

def unitCertificate (rows : List (Fin n → ℕ)) : Certificate (Fin n) :=
  ofEntries (rows.map (fun p => (p, 1)))

theorem initial_witness_valid (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (m : ℕ) (rows : List (Fin n → ℕ))
    (hw : ResidualWitness R (normalize R h) s T m (normalize R h) rows) :
    Valid R h m s T (unitCertificate rows) := by
  rw [unitCertificate, valid_ofEntries_iff]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hw.2.1
  · simpa [Function.comp_def] using hw.1
  · intro v hv
    simpa [Function.comp_def, TreeBudgetPatterns.normalize, hv] using hw.2.2 v

theorem initial_iff_matrix (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (m : ℕ) :
    ResidualFeasible R (normalize R h) s T m (normalize R h) ↔
      MatrixFeasible R h m s T := by
  constructor
  · rintro ⟨rows, hw⟩
    exact valid_implies_matrix R h m s T _ (initial_witness_valid R h s T m rows hw)
  · intro hm
    obtain ⟨f, hf⟩ := (matrix_iff_pattern_rows R h m s T).mp hm
    refine ⟨List.ofFn (fun i => values (f i).val), by simp, ?_, ?_⟩
    · simp only [List.forall_mem_ofFn_iff, rowValid_normalize_iff]
      intro i
      exact ⟨values_root _, fun _ hv => values_le _ hv, (f i).property⟩
    · intro v
      by_cases hv : v = R.root
      · simp [hv, Function.comp_def]
      · simpa [List.map_ofFn, List.sum_ofFn, TreeBudgetPatterns.normalize, hv] using hf v hv

/-- Evaluate candidates one at a time, stopping at the first successful result. -/
def firstSuccess {A B : Type*} (f : A → Option B) : List A → Option B
  | [] => none
  | a :: xs => match f a with
    | some b => some b
    | none => firstSuccess f xs

theorem firstSuccess_sound {A B : Type*} (f : A → Option B) (xs : List A) (b : B)
    (hb : firstSuccess f xs = some b) : ∃ a ∈ xs, f a = some b := by
  induction xs with
  | nil => simp [firstSuccess] at hb
  | cons a xs ih =>
    cases he : f a with
    | none =>
      obtain ⟨c, hc, hf⟩ := ih (by simpa [firstSuccess, he] using hb)
      exact ⟨c, by simp [hc], hf⟩
    | some c =>
      have hcb : c = b := by simpa [firstSuccess, he] using hb
      exact ⟨a, by simp, hcb ▸ he⟩

theorem firstSuccess_isSome_iff {A B : Type*} (f : A → Option B) (xs : List A) :
    (firstSuccess f xs).isSome = true ↔ ∃ a ∈ xs, (f a).isSome = true := by
  induction xs with
  | nil => simp [firstSuccess]
  | cons a xs ih =>
    cases he : f a <;> simp [firstSuccess, he, ih]

/-- The complete fixed list ps is passed to every recursive call, including
after choosing a row already used earlier. Subtraction is guarded coordinatewise. -/
def searchRowsWith (ps : List (Fin n → ℕ)) : ℕ → (Fin n → ℕ) → Option (List (Fin n → ℕ))
  | 0, r => if r = 0 then some [] else none
  | k + 1, r => firstSuccess (fun p =>
      if ∀ v, p v ≤ r v then (searchRowsWith ps k (r - p)).map (p :: ·) else none) ps

def searchRows (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ)
    (k : ℕ) (r : Fin n → ℕ) : Option (List (Fin n → ℕ)) :=
  searchRowsWith (TreeBudgetFiniteSearch.candidates R H s T) k r

theorem searchRowsWith_sound (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (ps : List (Fin n → ℕ))
    (hp : ∀ p ∈ ps, RowValid R H s T p) (k : ℕ) (r : Fin n → ℕ)
    (rows : List (Fin n → ℕ)) (hs : searchRowsWith ps k r = some rows) :
    ResidualWitness R H s T k r rows := by
  induction k generalizing r rows with
  | zero =>
    by_cases hr : r = 0
    · have he : rows = [] := by simpa [searchRowsWith, hr] using hs.symm
      simp [ResidualWitness, he, hr]
    · simp [searchRowsWith, hr] at hs
  | succ k ih =>
    obtain ⟨p, hmem, hs⟩ := firstSuccess_sound _ ps rows hs
    split_ifs at hs with hle
    · obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact (residualWitness_cons_iff ..).mpr ⟨hp p hmem, hle, ih _ _ ht⟩

theorem searchRowsWith_complete (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (ps : List (Fin n → ℕ))
    (hp : ∀ p, RowValid R H s T p → p ∈ ps) (k : ℕ) (r : Fin n → ℕ)
    (hf : ResidualFeasible R H s T k r) : (searchRowsWith ps k r).isSome = true := by
  induction k generalizing r with
  | zero =>
    have hr := (residualFeasible_zero_iff ..).mp hf
    simp [searchRowsWith, hr]
  | succ k ih =>
    obtain ⟨p, hv, hle, ht⟩ := (residualFeasible_succ_iff ..).mp hf
    have hle' : ∀ v, p v ≤ r v := hle
    apply (firstSuccess_isSome_iff _ ps).mpr
    exact ⟨p, hp p hv, by simp [hle', ih _ ht]⟩

theorem searchRows_sound (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (rows : List (Fin n → ℕ)) (hs : searchRows R H s T k r = some rows) :
    ResidualWitness R H s T k r rows :=
  searchRowsWith_sound R H s T _
    (fun _ hp => (TreeBudgetFiniteSearch.mem_candidates ..).mp hp) k r rows hs

theorem searchRows_correct (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) :
    (searchRows R H s T k r).isSome = true ↔ ResidualFeasible R H s T k r := by
  constructor
  · intro hs
    cases he : searchRows R H s T k r with
    | none => simp [he] at hs
    | some rows => exact ⟨rows, searchRows_sound R H s T k r rows he⟩
  · exact searchRowsWith_complete R H s T _
      (fun _ hp => (TreeBudgetFiniteSearch.mem_candidates ..).mpr hp) k r

/-- Only this initial-state wrapper claims to cover the original input. -/
def search (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (searchRows R (normalize R h) s T m (normalize R h)).map unitCertificate

theorem search_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : search R h m s T = some C) : checkCertificate R h m s T C = true := by
  obtain ⟨rows, hs, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact (checkCertificate_eq_true_iff ..).mpr
    (initial_witness_valid R h s T m rows (searchRows_sound R _ s T m _ rows hs))

theorem search_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (search R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  simp only [search, Option.isSome_map, searchRows_correct, initial_iff_matrix]

theorem search_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : search R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  rw [← search_correct]
  cases search R h m s T <;> simp

theorem search_isSome_eq_reference (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (search R h m s T).isSome = (TreeBudgetFiniteSearch.search R h m s T).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (search_correct ..).trans (TreeBudgetFiniteSearch.search_correct ..).symm

end UAVProof.TreeBudgetResidualSearch

#print axioms UAVProof.TreeBudgetResidualSearch.residualFeasible_zero_iff
#print axioms UAVProof.TreeBudgetResidualSearch.residualFeasible_succ_iff
#print axioms UAVProof.TreeBudgetResidualSearch.residualFeasible_succ_pattern_iff
#print axioms UAVProof.TreeBudgetResidualSearch.initial_iff_matrix
#print axioms UAVProof.TreeBudgetResidualSearch.searchRows_sound
#print axioms UAVProof.TreeBudgetResidualSearch.searchRows_correct
#print axioms UAVProof.TreeBudgetResidualSearch.search_sound
#print axioms UAVProof.TreeBudgetResidualSearch.search_correct
#print axioms UAVProof.TreeBudgetResidualSearch.search_none_iff
#print axioms UAVProof.TreeBudgetResidualSearch.search_isSome_eq_reference
