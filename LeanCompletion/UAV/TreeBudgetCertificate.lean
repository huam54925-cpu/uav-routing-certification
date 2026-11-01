import LeanCompletion.UAV.TreeBudgetPatterns

/-! Executable verification of compressed pattern certificates. Multiplicities
are summed directly; validation never expands a pattern into repeated rows. -/
namespace UAVProof.TreeBudgetCertificate

open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetPatterns
variable {V : Type*} [Fintype V] [DecidableEq V]

def RowValid (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : V → ℕ) : Prop :=
  p R.root = 0 ∧ (∀ v, v ≠ R.root → p v ≤ h v) ∧
    rootCount R p = 1 ∧ AncestorClosed R p ∧ cost R p s ≤ T

instance (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ) (p : V → ℕ) :
    Decidable (RowValid R h s T p) := by
  unfold RowValid AncestorClosed
  infer_instance

structure Certificate (V : Type*) where
  size : ℕ
  row : Fin size → V → ℕ
  count : Fin size → ℕ

def Valid (R : RootedTree V) (h : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ)
    (c : Certificate V) : Prop :=
  (∀ i, RowValid R h s T (c.row i)) ∧ (∑ i, c.count i) = m ∧
    ∀ v, v ≠ R.root → ∑ i, c.count i * c.row i v = h v

instance (R : RootedTree V) (h : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ)
    (c : Certificate V) : Decidable (Valid R h m s T c) := by
  unfold Valid
  infer_instance

def checkCertificate (R : RootedTree V) (h : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ)
    (c : Certificate V) : Bool := decide (Valid R h m s T c)

@[simp] theorem checkCertificate_eq_true_iff (R : RootedTree V) (h : V → ℕ)
    (m : ℕ) (s : V → ℚ) (T : ℚ) (c : Certificate V) :
    checkCertificate R h m s T c = true ↔ Valid R h m s T c := by
  simp [checkCertificate]

theorem valid_implies_matrix (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (c : Certificate V) (hc : Valid R h m s T c) :
    MatrixFeasible R h m s T := by
  classical
  let I := (i : Fin c.size) × Fin (c.count i)
  have hcard : Fintype.card I = m := by simp [I, hc.2.1]
  let e : Fin m ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  refine ⟨fun r => c.row (e r).1, ?_, ?_, ?_, ?_⟩
  · intro v hv
    calc
      ∑ r, c.row (e r).1 v = ∑ i : I, c.row i.1 v :=
        Equiv.sum_comp e (fun i : I => c.row i.1 v)
      _ = ∑ i, c.count i * c.row i v := by rw [Fintype.sum_sigma]; simp
      _ = h v := hc.2.2 v hv
  · intro r
    rw [← rootCount_eq]
    exact (hc.1 (e r).1).2.2.1
  · intro r; exact (hc.1 (e r).1).2.2.2.1
  · intro r
    rw [← cost_eq]
    exact (hc.1 (e r).1).2.2.2.2

theorem matrix_iff_exists_certificate (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R h m s T ↔
      ∃ c : Certificate V, checkCertificate R h m s T c = true := by
  constructor
  · intro hm
    obtain ⟨f, hf⟩ := (matrix_iff_pattern_rows R h m s T).mp hm
    refine ⟨⟨m, fun r => values (f r).val, fun _ => 1⟩, ?_⟩
    rw [checkCertificate_eq_true_iff]
    refine ⟨fun r => ?_, by simp, ?_⟩
    · exact ⟨values_root _, fun _ hv => values_le _ hv, (f r).property⟩
    · simpa using hf
  · rintro ⟨c, hc⟩
    exact valid_implies_matrix R h m s T c ((checkCertificate_eq_true_iff ..).mp hc)

theorem pattern_counts_iff_certificate (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hm : m = rootCount R h) :
    PatternCountsFeasible R h s T ↔
      ∃ c : Certificate V, checkCertificate R h m s T c = true :=
  (matrix_iff_pattern_counts R h m s T hm).symm.trans
    (matrix_iff_exists_certificate R h m s T)

end UAVProof.TreeBudgetCertificate

#print axioms UAVProof.TreeBudgetCertificate.checkCertificate_eq_true_iff
#print axioms UAVProof.TreeBudgetCertificate.matrix_iff_exists_certificate
#print axioms UAVProof.TreeBudgetCertificate.pattern_counts_iff_certificate
