import LeanCompletion.UAV.HubThreePartitionArithmetic

/-!
# Strict-hub exact routing and finite three-partition

This package proves a semantic equivalence for natural-number source weights.
It reuses the existing route/matrix equivalence; no encoding-time bound,
hardness classification, or general subtree interface is asserted.
The zero-fleet case is included without introducing an empty individual route.
-/

namespace UAVProof.HubThreePartition

open HubSpokeSupportExact SupportExactFeasibility
open HubThreePartitionArithmetic

abbrev Item (m : ℕ) := Fin (3 * m)

/-- Strict fractional bounds are expressed without truncated natural division.
Positivity of each item follows from the lower bound and positive budget. -/
def ValidInput {m : ℕ} (a : Item m → ℕ) (B : ℕ) : Prop :=
  0 < B ∧ (∀ i, B < 4 * a i ∧ 2 * a i < B) ∧ ∑ i, a i = m * B

/-- Assignment fibers give disjoint groups covering every item, including
when both the item type and route type are empty. -/
def group {m : ℕ} (assignment : Item m → Fin m) (r : Fin m) : Finset (Item m) :=
  Finset.univ.filter (fun i => assignment i = r)

def ThreePartition {m : ℕ} (a : Item m → ℕ) (B : ℕ) : Prop :=
  ∃ assignment : Item m → Fin m,
    ∀ r, (group assignment r).card = 3 ∧ ∑ i ∈ group assignment r, a i = B

/-- Zero depot/hub fee and the natural item weights as rational leaf fees. -/
def service {m : ℕ} (a : Item m → ℕ) : Node (Item m) → ℚ
  | none => 0
  | some none => 0
  | some (some i) => a i

/-- Unit leaf multiplicities, m depot-hub round trips, and exact hub demand.
The underlying predicate uses Fin m routes and ignores the depot demand. -/
def RoutingFeasible {m : ℕ} (a : Item m → ℕ) (B : ℕ) : Prop :=
  ExactFeasible depot (canonicalFlow m (fun _ : Item m => 1))
    (required m (fun _ : Item m => 1)) m (service a) (B : ℚ)

def UnitMatrixFeasible {m : ℕ} (a : Item m → ℕ) (B : ℕ) : Prop :=
  ∃ n : Fin m → Item m → ℕ,
    (∀ i, ∑ r, n r i = 1) ∧ ∀ r, ∑ i, a i * n r i ≤ B

theorem input_item_pos {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ValidInput a B) (i : Item m) : 0 < a i := by
  have hi := (h.2.1 i).1
  omega

/-- The integer inequalities are exactly the intended rational strict bounds. -/
theorem strict_bounds_iff (a B : ℕ) :
    (B < 4 * a ∧ 2 * a < B) ↔
      ((B : ℚ) / 4 < (a : ℚ) ∧ (a : ℚ) < (B : ℚ) / 2) := by
  constructor
  · rintro ⟨hl, hu⟩
    have hlq : (B : ℚ) < 4 * (a : ℚ) := by exact_mod_cast hl
    have huq : 2 * (a : ℚ) < (B : ℚ) := by exact_mod_cast hu
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    have hlq : (B : ℚ) < 4 * (a : ℚ) := by linarith
    have huq : 2 * (a : ℚ) < (B : ℚ) := by linarith
    constructor
    · exact_mod_cast hlq
    · exact_mod_cast huq

@[simp] theorem mem_group {m : ℕ} (assignment : Item m → Fin m)
    (r : Fin m) (i : Item m) : i ∈ group assignment r ↔ assignment i = r := by
  simp [group]

theorem groups_disjoint {m : ℕ} (assignment : Item m → Fin m)
    {r t : Fin m} (hrt : r ≠ t) : Disjoint (group assignment r) (group assignment t) := by
  apply Finset.disjoint_left.mpr
  intro i hir hit
  exact hrt (((mem_group assignment r i).mp hir).symm.trans
    ((mem_group assignment t i).mp hit))

theorem item_in_unique_group {m : ℕ} (assignment : Item m → Fin m) (i : Item m) :
    ∃! r, i ∈ group assignment r := by
  refine ⟨assignment i, by simp, ?_⟩
  intro r hr
  exact ((mem_group assignment r i).mp hr).symm

/-- Each leaf has demand one, and every subsequent hub return is counted. -/
theorem required_hub_eq {m : ℕ} :
    required m (fun _ : Item m => 1) hub = 4 * m := by
  simp [required, hub, Item]
  omega

theorem matrix_iff_unitMatrix {m : ℕ} (a : Item m → ℕ) (B : ℕ) :
    HubSpokePacking.MatrixFeasible m (fun _ : Item m => 1) (service a) (B : ℚ) ↔
      UnitMatrixFeasible a B := by
  constructor
  · rintro ⟨n, hcol, hbudget⟩
    refine ⟨n, hcol, fun r => ?_⟩
    have hq : (∑ i, (a i : ℚ) * (n r i : ℚ)) ≤ (B : ℚ) := by
      simpa [service, hub, satellite] using hbudget r
    exact_mod_cast hq
  · rintro ⟨n, hcol, hbudget⟩
    refine ⟨n, hcol, fun r => ?_⟩
    have hq : (∑ i, (a i : ℚ) * (n r i : ℚ)) ≤ (B : ℚ) := by
      exact_mod_cast hbudget r
    simpa [service, hub, satellite] using hq

/-- The route/matrix bridge itself does not require a valid source instance. -/
theorem routing_iff_unitMatrix {m : ℕ} (a : Item m → ℕ) (B : ℕ) :
    RoutingFeasible a B ↔ UnitMatrixFeasible a B := by
  unfold RoutingFeasible
  exact (HubSpokePacking.exact_iff_matrix m (fun _ : Item m => 1) (service a) (B : ℚ)).trans
    (matrix_iff_unitMatrix a B)

theorem row_load_eq_group_sum {m : ℕ} (a : Item m → ℕ)
    (n : Fin m → Item m → ℕ) (assignment : Item m → Fin m)
    (hn : ∀ r i, n r i = if assignment i = r then 1 else 0) (r : Fin m) :
    (∑ i, a i * n r i) = ∑ i ∈ group assignment r, a i := by
  simp [hn, group, Finset.sum_filter, mul_ite]

/-- Unit columns, saturation, and the strict bounds force exactly three items
per row. Zero rows are excluded by the proof, not by the routing model. -/
theorem unitMatrix_implies_threePartition {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ValidInput a B) (hm : UnitMatrixFeasible a B) : ThreePartition a B := by
  obtain ⟨n, hcol, hbudget⟩ := hm
  obtain ⟨assignment, hn⟩ := unit_column_assignment n hcol
  have hsat := row_loads_saturate n a B hcol (by simpa using h.2.2) hbudget
  refine ⟨assignment, fun r => ?_⟩
  have hsum : ∑ i ∈ group assignment r, a i = B :=
    (row_load_eq_group_sum a n assignment hn r).symm.trans (hsat r)
  exact ⟨card_eq_three_of_sum_eq a B h.1 (fun i => (h.2.1 i).1)
    (fun i => (h.2.1 i).2) (group assignment r) hsum, hsum⟩

/-- Every assignment partition supplies a unit-column matrix. This direction
does not need positive weights, strict bounds, or the total-weight hypothesis. -/
theorem threePartition_implies_unitMatrix {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ThreePartition a B) : UnitMatrixFeasible a B := by
  obtain ⟨assignment, hg⟩ := h
  let n : Fin m → Item m → ℕ := fun r i => if assignment i = r then 1 else 0
  refine ⟨n, ?_, ?_⟩
  · intro i
    simp [n]
  · intro r
    exact le_of_eq ((row_load_eq_group_sum a n assignment (fun _ _ => rfl) r).trans
      (hg r).2)

theorem unitMatrix_iff_threePartition {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ValidInput a B) : UnitMatrixFeasible a B ↔ ThreePartition a B :=
  ⟨unitMatrix_implies_threePartition a B h, threePartition_implies_unitMatrix a B⟩

/-- Semantic iff only: this does not assert a polynomial-time reduction,
strong NP-hardness, or NP membership. The empty fleet m=0 is included. -/
theorem exact_iff_threePartition {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ValidInput a B) : RoutingFeasible a B ↔ ThreePartition a B := by
  exact (routing_iff_unitMatrix a B).trans (unitMatrix_iff_threePartition a B h)

end UAVProof.HubThreePartition

#print axioms UAVProof.HubThreePartition.input_item_pos
#print axioms UAVProof.HubThreePartition.strict_bounds_iff
#print axioms UAVProof.HubThreePartition.mem_group
#print axioms UAVProof.HubThreePartition.groups_disjoint
#print axioms UAVProof.HubThreePartition.item_in_unique_group
#print axioms UAVProof.HubThreePartition.required_hub_eq
#print axioms UAVProof.HubThreePartition.matrix_iff_unitMatrix
#print axioms UAVProof.HubThreePartition.routing_iff_unitMatrix
#print axioms UAVProof.HubThreePartition.row_load_eq_group_sum
#print axioms UAVProof.HubThreePartition.unitMatrix_implies_threePartition
#print axioms UAVProof.HubThreePartition.threePartition_implies_unitMatrix
#print axioms UAVProof.HubThreePartition.unitMatrix_iff_threePartition
#print axioms UAVProof.HubThreePartition.exact_iff_threePartition
