import LeanCompletion.UAV.HubThreePartition

/-!
# Assignment certificates for the canonical strict-hub target

The checker verifies a supplied assignment, without searching for one.
It does not require the three-partition source assumptions: zero fees,
zero budgets, empty rows and the empty fleet are included.
Raw certificates are lists of natural route labels, not binary strings.
-/

namespace UAVProof.HubAssignmentChecker

open HubThreePartition HubThreePartitionArithmetic

def assignmentLoad {m : ℕ} (a : Item m → ℕ) (q : Item m → Fin m) (r : Fin m) : ℕ :=
  ∑ i ∈ group q r, a i

def AssignmentValid {m : ℕ} (a : Item m → ℕ) (B : ℕ) (q : Item m → Fin m) : Prop :=
  ∀ r, assignmentLoad a q r ≤ B

def checkAssignment {m : ℕ} (a : Item m → ℕ) (B : ℕ) (q : Item m → Fin m) : Bool :=
  decide (∀ r, assignmentLoad a q r ≤ B)

theorem assignmentLoad_eq_sum {m : ℕ} (a : Item m → ℕ) (q : Item m → Fin m)
    (r : Fin m) : assignmentLoad a q r = ∑ i, if q i = r then a i else 0 := by
  simp [assignmentLoad, group, Finset.sum_filter]

theorem checkAssignment_eq_true_iff {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (q : Item m → Fin m) :
    checkAssignment a B q = true ↔ AssignmentValid a B q := by
  simp [checkAssignment, AssignmentValid]

theorem unitMatrix_iff_exists_valid_assignment {m : ℕ} (a : Item m → ℕ) (B : ℕ) :
    UnitMatrixFeasible a B ↔ ∃ q, AssignmentValid a B q := by
  constructor
  · rintro ⟨n, hcol, hbudget⟩
    obtain ⟨q, hq⟩ := unit_column_assignment n hcol
    refine ⟨q, fun r => ?_⟩
    change (∑ i ∈ group q r, a i) ≤ B
    rw [← row_load_eq_group_sum a n q hq r]
    exact hbudget r
  · rintro ⟨q, hq⟩
    let n : Fin m → Item m → ℕ := fun r i => if q i = r then 1 else 0
    refine ⟨n, ?_, ?_⟩
    · intro i
      simp [n]
    · intro r
      rw [row_load_eq_group_sum a n q (fun _ _ => rfl) r]
      exact hq r

theorem routing_iff_exists_accepted_assignment {m : ℕ} (a : Item m → ℕ) (B : ℕ) :
    RoutingFeasible a B ↔ ∃ q, checkAssignment a B q = true := by
  rw [routing_iff_unitMatrix, unitMatrix_iff_exists_valid_assignment]
  simp only [checkAssignment_eq_true_iff]

/-- Encode labels in item-index order; this does not encode binary integers. -/
def encodeAssignment {m : ℕ} (q : Item m → Fin m) : List ℕ :=
  List.ofFn (fun i => (q i).val)

/-- Length and label range are checked before constructing a typed assignment. -/
def decodeAssignment (m : ℕ) (c : List ℕ) : Option (Item m → Fin m) :=
  if hlen : c.length = 3 * m then
    if hbound : ∀ r ∈ c, r < m then
      some (fun i =>
        ⟨c.get ⟨i.val, by omega⟩,
          hbound _ (List.get_mem _ _)⟩)
    else none
  else none

@[simp] theorem encodeAssignment_length {m : ℕ} (q : Item m → Fin m) :
    (encodeAssignment q).length = 3 * m := by
  simp [encodeAssignment]

theorem encodeAssignment_range {m : ℕ} (q : Item m → Fin m) :
    ∀ r ∈ encodeAssignment q, r < m := by
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact (q i).isLt

theorem decodeAssignment_encode {m : ℕ} (q : Item m → Fin m) :
    decodeAssignment m (encodeAssignment q) = some q := by
  rw [decodeAssignment, dif_pos (encodeAssignment_length q),
    dif_pos (encodeAssignment_range q)]
  congr 1
  funext i
  apply Fin.ext
  simp [encodeAssignment]

theorem decodeAssignment_some_spec {m : ℕ} (c : List ℕ) (q : Item m → Fin m)
    (h : decodeAssignment m c = some q) :
    c.length = 3 * m ∧ (∀ r ∈ c, r < m) := by
  unfold decodeAssignment at h
  split at h
  · rename_i hlen
    split at h
    · rename_i hbound
      exact ⟨hlen, hbound⟩
    · contradiction
  · contradiction

/-- Successful decoding preserves the actual list, including its ordering. -/
theorem encodeAssignment_of_decode {m : ℕ} (c : List ℕ) (q : Item m → Fin m)
    (h : decodeAssignment m c = some q) : encodeAssignment q = c := by
  unfold decodeAssignment at h
  split at h
  · rename_i hlen
    split at h
    · rename_i hbound
      cases Option.some.inj h
      apply List.ext_getElem
      · simp [encodeAssignment, hlen]
      · intro i hi hi'
        simp [encodeAssignment]
    · contradiction
  · contradiction

theorem decodeAssignment_eq_some_iff {m : ℕ} (c : List ℕ) (q : Item m → Fin m) :
    decodeAssignment m c = some q ↔ encodeAssignment q = c := by
  constructor
  · exact encodeAssignment_of_decode c q
  · intro h
    rw [← h, decodeAssignment_encode]

def checkAssignmentList {m : ℕ} (a : Item m → ℕ) (B : ℕ) (c : List ℕ) : Bool :=
  match decodeAssignment m c with
  | none => false
  | some q => checkAssignment a B q

theorem checkAssignmentList_eq_true_iff {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (c : List ℕ) :
    checkAssignmentList a B c = true ↔
      ∃ q, decodeAssignment m c = some q ∧ AssignmentValid a B q := by
  unfold checkAssignmentList
  cases h : decodeAssignment m c with
  | none => simp
  | some q => simp [checkAssignment_eq_true_iff]

theorem routing_iff_exists_accepted_list {m : ℕ} (a : Item m → ℕ) (B : ℕ) :
    RoutingFeasible a B ↔ ∃ c, checkAssignmentList a B c = true := by
  rw [routing_iff_exists_accepted_assignment]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨encodeAssignment q, ?_⟩
    simp [checkAssignmentList, decodeAssignment_encode, hq]
  · rintro ⟨c, hc⟩
    obtain ⟨q, _, hq⟩ := (checkAssignmentList_eq_true_iff a B c).mp hc
    exact ⟨q, (checkAssignment_eq_true_iff a B q).mpr hq⟩

end UAVProof.HubAssignmentChecker
