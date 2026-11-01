import LeanCompletion.UAV.TreeBudgetCertificate

/-! A deliberately exhaustive executable reference search on numbered vertices.
It enumerates bounded rows and then finite families of valid rows. No memoization
or polynomial-time claim is made. Successful output is a checkable certificate. -/
namespace UAVProof.TreeBudgetFiniteSearch

open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetPatterns TreeBudgetCertificate

def boundedVectors : (n : ℕ) → (Fin n → ℕ) → List (Fin n → ℕ)
  | 0, _ => [Fin.elim0]
  | n + 1, b => (List.range (b 0 + 1)).flatMap fun a =>
      (boundedVectors n (fun i => b i.succ)).map (Fin.cons a)

theorem mem_boundedVectors (n : ℕ) (b f : Fin n → ℕ) :
    f ∈ boundedVectors n b ↔ ∀ i, f i ≤ b i := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [boundedVectors, hf]
  | succ n ih =>
    simp only [boundedVectors, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using Nat.le_of_lt_succ ha
      · simpa using (ih _ g).mp hg j
    · intro hf
      refine ⟨f 0, Nat.lt_succ_of_le (hf 0), fun i => f i.succ,
        (ih _ _).mpr (fun i => hf i.succ), ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def families {A : Type*} (xs : List A) : (m : ℕ) → List (Fin m → A)
  | 0 => [Fin.elim0]
  | m + 1 => xs.flatMap fun a => (families xs m).map (Fin.cons a)

theorem mem_families {A : Type*} (xs : List A) (m : ℕ) (f : Fin m → A) :
    f ∈ families xs m ↔ ∀ i, f i ∈ xs := by
  induction m with
  | zero =>
    have hf : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [families, hf]
  | succ m ih =>
    simp only [families, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa using (ih g).mp hg j
    · intro hf
      refine ⟨f 0, hf 0, fun i => f i.succ, (ih _).mpr (fun i => hf i.succ), ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

variable {n : ℕ}

def candidates (R : RootedTree (Fin n)) (h : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) :
    List (Fin n → ℕ) :=
  (boundedVectors n (bound R h)).filter (fun p => decide (RowValid R h s T p))

@[simp] theorem mem_candidates (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (p : Fin n → ℕ) :
    p ∈ candidates R h s T ↔ RowValid R h s T p := by
  simp only [candidates, List.mem_filter, mem_boundedVectors, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_, hp⟩
    intro v
    by_cases hv : v = R.root
    · simpa [bound, hv] using hp.1.le
    · simpa [bound, hv] using hp.2.1 v hv

def searchRows (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Fin m → Fin n → ℕ) :=
  (families (candidates R h s T) m).find?
    (fun f => decide (∀ v, v ≠ R.root → ∑ r, f r v = h v))

def unitCertificate (m : ℕ) (f : Fin m → Fin n → ℕ) : Certificate (Fin n) :=
  ⟨m, f, fun _ => 1⟩

def search (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (searchRows R h m s T).map (unitCertificate m)

theorem searchRows_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (f : Fin m → Fin n → ℕ)
    (hf : searchRows R h m s T = some f) :
    Valid R h m s T (unitCertificate m f) := by
  have hm := List.mem_of_find?_eq_some hf
  have hc := List.find?_some hf
  change f ∈ families (candidates R h s T) m at hm
  have hp := (mem_families _ _ _).mp hm
  refine ⟨fun r => (mem_candidates ..).mp (hp r),
    ?_, ?_⟩
  · change (∑ _ : Fin m, (1 : ℕ)) = m
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact Fintype.card_fin m
  · simpa [unitCertificate] using hc

theorem searchRows_complete (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (hm : MatrixFeasible R h m s T) :
    (searchRows R h m s T).isSome = true := by
  obtain ⟨f, hf⟩ := (matrix_iff_pattern_rows R h m s T).mp hm
  rw [searchRows, List.find?_isSome]
  refine ⟨fun r => values (f r).val, (mem_families _ _ _).mpr ?_, ?_⟩
  · intro r
    apply (mem_candidates ..).mpr
    exact ⟨values_root _, fun _ hv => values_le _ hv, (f r).property⟩
  · simpa using hf

theorem search_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : Certificate (Fin n))
    (hc : search R h m s T = some c) : checkCertificate R h m s T c = true := by
  cases he : searchRows R h m s T with
  | none => simp [search, he] at hc
  | some f =>
    have hcf : unitCertificate m f = c := by simpa [search, he] using hc
    subst c
    exact (checkCertificate_eq_true_iff ..).mpr (searchRows_sound R h m s T f he)

theorem search_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (search R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  constructor
  · intro hs
    cases he : search R h m s T with
    | none => simp [he] at hs
    | some c =>
      exact valid_implies_matrix R h m s T c
        ((checkCertificate_eq_true_iff ..).mp (search_sound R h m s T c he))
  · intro hm
    simpa [search] using searchRows_complete R h m s T hm

theorem search_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    search R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  rw [← search_correct]
  cases search R h m s T <;> simp

end UAVProof.TreeBudgetFiniteSearch

#print axioms UAVProof.TreeBudgetFiniteSearch.search_sound
#print axioms UAVProof.TreeBudgetFiniteSearch.search_correct
#print axioms UAVProof.TreeBudgetFiniteSearch.search_none_iff
