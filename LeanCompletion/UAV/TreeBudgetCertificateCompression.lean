import LeanCompletion.UAV.TreeBudgetResidualBranchSearch

/-! Stable compression of certificate entries by equality of complete row vectors.
Zero counts are removed. Valid inputs stay valid; arbitrary checker results need
not be preserved, because even zero-count rows are checked by the original checker. -/
namespace UAVProof.TreeBudgetCertificateCompression
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetBranchCertificate TreeBudgetCriterion
variable {n : ℕ}

/-- Add a positive count to the first identical row, or append a new row. -/
def insertCount (p : Fin n → ℕ) (a : ℕ) : List (Entry n) → List (Entry n)
  | [] => [(p, a)]
  | e :: xs => if e.1 = p then (p, e.2 + a) :: xs else e :: insertCount p a xs

def addEntry (acc : List (Entry n)) (e : Entry n) : List (Entry n) :=
  if e.2 = 0 then acc else insertCount e.1 e.2 acc

def compressEntries (xs : List (Entry n)) : List (Entry n) := xs.foldl addEntry []

def compressCertificate (C : Certificate (Fin n)) : Certificate (Fin n) :=
  ofEntries (compressEntries (entries C))

def weightedSum (xs : List (Entry n)) (f : (Fin n → ℕ) → ℕ) : ℕ :=
  (xs.map (fun e => e.2 * f e.1)).sum

def patternCount (xs : List (Entry n)) (p : Fin n → ℕ) : ℕ :=
  weightedSum xs (fun q => if q = p then 1 else 0)

def Reduced (xs : List (Entry n)) : Prop :=
  (∀ e ∈ xs, 0 < e.2) ∧ (xs.map Prod.fst).Nodup

theorem weightedSum_insertCount (p : Fin n → ℕ) (a : ℕ) (xs : List (Entry n))
    (f : (Fin n → ℕ) → ℕ) :
    weightedSum (insertCount p a xs) f = weightedSum xs f + a * f p := by
  induction xs with
  | nil => simp [insertCount, weightedSum]
  | cons e xs ih =>
    by_cases he : e.1 = p
    · simp [insertCount, he, weightedSum, Nat.add_mul, Nat.add_assoc, Nat.add_comm]
    · simp [insertCount, he, weightedSum] at ih ⊢
      omega

theorem weightedSum_addEntry (acc : List (Entry n)) (e : Entry n)
    (f : (Fin n → ℕ) → ℕ) :
    weightedSum (addEntry acc e) f = weightedSum acc f + e.2 * f e.1 := by
  by_cases he : e.2 = 0
  · simp [addEntry, he]
  · simp [addEntry, he, weightedSum_insertCount]

theorem weightedSum_foldl (xs acc : List (Entry n)) (f : (Fin n → ℕ) → ℕ) :
    weightedSum (xs.foldl addEntry acc) f = weightedSum acc f + weightedSum xs f := by
  induction xs generalizing acc with
  | nil => simp [weightedSum]
  | cons e xs ih =>
    simp only [List.foldl_cons, ih, weightedSum_addEntry]
    simp [weightedSum, Nat.add_assoc]

theorem compress_weightedSum (xs : List (Entry n)) (f : (Fin n → ℕ) → ℕ) :
    weightedSum (compressEntries xs) f = weightedSum xs f := by
  simpa [compressEntries, weightedSum] using weightedSum_foldl xs [] f

theorem compress_patternCount (xs : List (Entry n)) (p : Fin n → ℕ) :
    patternCount (compressEntries xs) p = patternCount xs p :=
  compress_weightedSum xs _

theorem compress_total (xs : List (Entry n)) :
    ((compressEntries xs).map Prod.snd).sum = (xs.map Prod.snd).sum := by
  simpa [weightedSum] using compress_weightedSum xs (fun _ => 1)

theorem compress_column (xs : List (Entry n)) (v : Fin n) :
    ((compressEntries xs).map (fun e => e.2 * e.1 v)).sum =
      (xs.map (fun e => e.2 * e.1 v)).sum := compress_weightedSum xs (fun p => p v)

theorem rows_insertCount (p : Fin n → ℕ) (a : ℕ) (xs : List (Entry n)) :
    (insertCount p a xs).map Prod.fst =
      if p ∈ xs.map Prod.fst then xs.map Prod.fst else xs.map Prod.fst ++ [p] := by
  induction xs with
  | nil => simp [insertCount]
  | cons e xs ih =>
    by_cases he : e.1 = p
    · simp [insertCount, he]
    · by_cases hp : p ∈ xs.map Prod.fst <;>
        simp [insertCount, he, Ne.symm he, ih, hp]

theorem insertCount_reduced (p : Fin n → ℕ) (a : ℕ) (xs : List (Entry n))
    (ha : 0 < a) (hx : Reduced xs) : Reduced (insertCount p a xs) := by
  refine ⟨?_, ?_⟩
  · induction xs with
    | nil => simpa [insertCount] using ha
    | cons e xs ih =>
      have ht : Reduced xs := ⟨fun q hq => hx.1 q (by simp [hq]),
        (List.nodup_cons.mp hx.2).2⟩
      by_cases he : e.1 = p
      · simp only [insertCount, he, ite_true, List.mem_cons, Prod.forall]
        rintro q b (hqb | hqb)
        · cases hqb; omega
        · exact hx.1 (q, b) (by simp [hqb])
      · simpa [insertCount, he] using And.intro (hx.1 e (by simp)) (ih ht)
  · rw [rows_insertCount]
    split_ifs with hp
    · exact hx.2
    · simpa using hx.2.concat hp

theorem addEntry_reduced (acc : List (Entry n)) (e : Entry n) (ha : Reduced acc) :
    Reduced (addEntry acc e) := by
  by_cases he : e.2 = 0
  · simpa [addEntry, he] using ha
  · simpa [addEntry, he] using insertCount_reduced e.1 e.2 acc (Nat.pos_of_ne_zero he) ha

theorem foldl_reduced (xs acc : List (Entry n)) (ha : Reduced acc) :
    Reduced (xs.foldl addEntry acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons e xs ih => exact ih _ (addEntry_reduced acc e ha)

theorem compress_reduced (xs : List (Entry n)) : Reduced (compressEntries xs) :=
  foldl_reduced xs [] (by simp [Reduced])

theorem insertCount_rows_valid (P : (Fin n → ℕ) → Prop) (p : Fin n → ℕ) (a : ℕ)
    (xs : List (Entry n)) (hp : P p) (hx : ∀ e ∈ xs, P e.1) :
    ∀ e ∈ insertCount p a xs, P e.1 := by
  induction xs with
  | nil => simpa [insertCount] using hp
  | cons e xs ih =>
    have ht : ∀ q ∈ xs, P q.1 := fun q hq => hx q (by simp [hq])
    by_cases he : e.1 = p
    · simpa [insertCount, he] using And.intro hp ht
    · simpa [insertCount, he] using And.intro (hx e (by simp)) (ih ht)

theorem foldl_rows_valid (P : (Fin n → ℕ) → Prop) (xs acc : List (Entry n))
    (hx : ∀ e ∈ xs, 0 < e.2 → P e.1) (ha : ∀ e ∈ acc, P e.1) :
    ∀ e ∈ xs.foldl addEntry acc, P e.1 := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons e xs ih =>
    apply ih _ (fun q hq => hx q (by simp [hq]))
    by_cases he : e.2 = 0
    · simpa [addEntry, he] using ha
    · simpa [addEntry, he] using insertCount_rows_valid P e.1 e.2 acc
        (hx e (by simp) (Nat.pos_of_ne_zero he)) ha

theorem compress_origin (xs : List (Entry n)) (e : Entry n)
    (he : e ∈ compressEntries xs) : ∃ a, (e.1, a) ∈ xs ∧ 0 < a := by
  have h := foldl_rows_valid (fun p => ∃ a, (p, a) ∈ xs ∧ 0 < a) xs []
    (fun q hq hpos => ⟨q.2, hq, hpos⟩) (by simp)
  exact h e he

/-- This fold records first positive occurrences without sorting the rows. -/
theorem foldl_row_order (xs acc : List (Entry n)) :
    (xs.foldl addEntry acc).map Prod.fst =
      xs.foldl (fun seen e => if e.2 = 0 ∨ e.1 ∈ seen then seen else seen ++ [e.1])
        (acc.map Prod.fst) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    by_cases he : e.2 = 0
    · simp [addEntry, he]
    · simp only [addEntry, he, if_false, rows_insertCount, false_or]

theorem compress_row_order (xs : List (Entry n)) :
    (compressEntries xs).map Prod.fst =
      xs.foldl (fun seen e => if e.2 = 0 ∨ e.1 ∈ seen then seen else seen ++ [e.1]) [] :=
  foldl_row_order xs []

theorem insertCount_of_fresh (p : Fin n → ℕ) (a : ℕ) (xs : List (Entry n))
    (hp : p ∉ xs.map Prod.fst) : insertCount p a xs = xs ++ [(p, a)] := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp [insertCount, Ne.symm hp.1, ih hp.2]

theorem foldl_eq_append (xs acc : List (Entry n)) (h : Reduced (acc ++ xs)) :
    xs.foldl addEntry acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    have he : 0 < e.2 := h.1 e (by simp)
    have hf : e.1 ∉ acc.map Prod.fst := by
      have hd := List.disjoint_of_nodup_append (by simpa using h.2)
      exact fun hm => List.disjoint_left.mp hd hm (by simp)
    have ha : addEntry acc e = acc ++ [e] := by
      simp [addEntry, Nat.ne_of_gt he, insertCount_of_fresh _ _ _ hf]
    simpa [List.foldl_cons, ha, List.append_assoc] using
      ih (acc ++ [e]) (by simpa [List.append_assoc] using h)

theorem compress_of_reduced (xs : List (Entry n)) (hx : Reduced xs) :
    compressEntries xs = xs := by
  simpa [compressEntries] using foldl_eq_append xs [] (by simpa using hx)

theorem compress_idempotent (xs : List (Entry n)) :
    compressEntries (compressEntries xs) = compressEntries xs :=
  compress_of_reduced _ (compress_reduced xs)

theorem length_insertCount_le (p : Fin n → ℕ) (a : ℕ) (xs : List (Entry n)) :
    (insertCount p a xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insertCount]
  | cons e xs ih =>
    by_cases he : e.1 = p
    · simp [insertCount, he]
    · simp [insertCount, he]; omega

theorem length_foldl_le (xs acc : List (Entry n)) :
    (xs.foldl addEntry acc).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    have hb : (addEntry acc e).length ≤ acc.length + 1 := by
      by_cases he : e.2 = 0
      · simp [addEntry, he]
      · simpa [addEntry, he] using length_insertCount_le e.1 e.2 acc
    have ht := ih (addEntry acc e)
    simpa only [List.foldl_cons, List.length_cons] using (by omega :
      (xs.foldl addEntry (addEntry acc e)).length ≤ acc.length + (xs.length + 1))

theorem compress_length_le (xs : List (Entry n)) :
    (compressEntries xs).length ≤ xs.length := by
  simpa [compressEntries] using length_foldl_le xs []

theorem length_le_total_of_positive (xs : List (Entry n))
    (hx : ∀ e ∈ xs, 0 < e.2) : xs.length ≤ (xs.map Prod.snd).sum := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have he := hx e (by simp)
    have ht := ih (fun q hq => hx q (by simp [hq]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem compress_validEntries (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (Entry n)) (hx : ValidEntries R h m s T xs) :
    ValidEntries R h m s T (compressEntries xs) := by
  refine ⟨?_, (compress_total xs).trans hx.2.1, ?_⟩
  · intro e he
    obtain ⟨a, ha, _⟩ := compress_origin xs e he
    exact hx.1 (e.1, a) ha
  · intro v hv
    exact (compress_column xs v).trans (hx.2.2 v hv)

theorem compress_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) (hC : Valid R h m s T C) :
    Valid R h m s T (compressCertificate C) := by
  rw [compressCertificate, valid_ofEntries_iff]
  exact compress_validEntries R h m s T _ ((valid_iff_entries ..).mp hC)

theorem compress_checked (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hC : checkCertificate R h m s T C = true) :
    checkCertificate R h m s T (compressCertificate C) = true :=
  (checkCertificate_eq_true_iff ..).mpr
    (compress_sound R h m s T C ((checkCertificate_eq_true_iff ..).mp hC))

theorem compressCertificate_idempotent (C : Certificate (Fin n)) :
    compressCertificate (compressCertificate C) = compressCertificate C := by
  simp [compressCertificate, compress_idempotent]

theorem compress_size_le (C : Certificate (Fin n)) :
    (compressCertificate C).size ≤ C.size := by
  simpa [compressCertificate, ofEntries, entries] using compress_length_le (entries C)

theorem compress_size_le_fleet (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) (hC : Valid R h m s T C) :
    (compressCertificate C).size ≤ m := by
  have ht := (valid_iff_entries R h m s T C).mp hC
  have hl := length_le_total_of_positive _ (compress_reduced (entries C)).1
  simpa [compress_total, ht.2.1, compressCertificate, ofEntries] using hl

/-- Compression changes only successful output representation. -/
theorem map_compress_isSome (result : Option (Certificate (Fin n))) :
    (result.map compressCertificate).isSome = result.isSome := by simp

theorem map_compress_none_iff (result : Option (Certificate (Fin n))) :
    result.map compressCertificate = none ↔ result = none := by simp

def searchCompressed (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (TreeBudgetResidualSearch.search R h m s T).map compressCertificate

def searchByRootCompressed (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (TreeBudgetResidualBranchSearch.searchByRoot R h m s T).map compressCertificate

def solveByRootCompressed (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  (TreeBudgetResidualBranchSearch.solveByRoot R d m s T).map compressCertificate

theorem searchCompressed_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchCompressed R h m s T = some C) : checkCertificate R h m s T C = true := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact compress_checked R h m s T D (TreeBudgetResidualSearch.search_sound R h m s T D hd)

theorem searchCompressed_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchCompressed R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  simpa [searchCompressed] using TreeBudgetResidualSearch.search_correct R h m s T

theorem searchCompressed_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    searchCompressed R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  simpa [searchCompressed] using TreeBudgetResidualSearch.search_none_iff R h m s T

theorem searchByRootCompressed_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : searchByRootCompressed R h m s T = some C) :
    checkCertificate R h m s T C = true := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact compress_checked R h m s T D
    (TreeBudgetResidualBranchSearch.searchByRoot_sound R h m s T D hd)

theorem searchByRootCompressed_correct (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (searchByRootCompressed R h m s T).isSome = true ↔ MatrixFeasible R h m s T := by
  simpa [searchByRootCompressed] using TreeBudgetResidualBranchSearch.searchByRoot_correct R h m s T

theorem searchByRootCompressed_none_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    searchByRootCompressed R h m s T = none ↔ ¬ MatrixFeasible R h m s T := by
  simpa [searchByRootCompressed] using
    TreeBudgetResidualBranchSearch.searchByRoot_none_iff R h m s T

theorem solveByRootCompressed_sound (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : solveByRootCompressed R d m s T = some C) :
    FlowCompatible R d m ∧
      checkCertificate R (TreeBudgetChecker.multiplicities R d) m s T C = true ∧
      BudgetRoutes R d m s T := by
  obtain ⟨D, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨hcomp, hcheck, hbudget⟩ := TreeBudgetResidualBranchSearch.solveByRoot_sound R d m s T D hd
  exact ⟨hcomp, compress_checked R _ m s T D hcheck, hbudget⟩

theorem solveByRootCompressed_correct (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (solveByRootCompressed R d m s T).isSome = true ↔ BudgetRoutes R d m s T := by
  simpa [solveByRootCompressed, TreeBudgetResidualBranchSearch.checkTreeBudgetByRoot] using
    TreeBudgetResidualBranchSearch.checkTreeBudgetByRoot_correct R d m s T

theorem solveByRootCompressed_none_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    solveByRootCompressed R d m s T = none ↔ ¬ BudgetRoutes R d m s T := by
  simpa [solveByRootCompressed] using TreeBudgetResidualBranchSearch.solveByRoot_none_iff R d m s T

end UAVProof.TreeBudgetCertificateCompression

#print axioms UAVProof.TreeBudgetCertificateCompression.compress_patternCount
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_total
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_column
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_reduced
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_origin
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_row_order
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_idempotent
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_sound
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_checked
#print axioms UAVProof.TreeBudgetCertificateCompression.compressCertificate_idempotent
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_size_le
#print axioms UAVProof.TreeBudgetCertificateCompression.compress_size_le_fleet
#print axioms UAVProof.TreeBudgetCertificateCompression.searchCompressed_sound
#print axioms UAVProof.TreeBudgetCertificateCompression.searchCompressed_correct
#print axioms UAVProof.TreeBudgetCertificateCompression.searchByRootCompressed_sound
#print axioms UAVProof.TreeBudgetCertificateCompression.searchByRootCompressed_correct
#print axioms UAVProof.TreeBudgetCertificateCompression.solveByRootCompressed_sound
#print axioms UAVProof.TreeBudgetCertificateCompression.solveByRootCompressed_correct
