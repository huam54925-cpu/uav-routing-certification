import LeanCompletion.UAV.ResourceCuts
import Mathlib.Tactic

/-!
# Large-service counting and insufficiency of rounded capacity cuts

Target: Lean 4.30.0-rc2, mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Verification: checked locally on 2026-10-23 with Lean 4.30.0-rc2.
See docs/SERVICE_CUTS_VERIFICATION.md for commands and cache limitations.
Place this file at LeanCompletion/UAV/LargeServiceCuts.lean in the existing project.
No modification of ResourceCuts.lean is required. The newer ceiling lemmas there
are not required: this module uses the earlier service definitions directly.

Every occurrence in a visit list is one indivisible service. Costs are rational.
The generic lemmas have no graph assumptions. The family below has zero travel
cost and tau = 0, and verifies ALL depot-free sets symbolically in m >= 2.
-/

namespace UAVProof.LargeServiceCuts

open ResourceCuts

section Counting

variable {V ι : Type*}

/-- If every selected service costs more than T/(k+1), at most k occurrences
fit in budget T. The scaled hypothesis avoids division in the proof. -/
theorem count_le_of_large
    (H : Finset V) (count : V → ℕ) (service : V → ℚ)
    (T : ℚ) (k : ℕ)
    (hT : 0 ≤ T)
    (hlarge : ∀ i ∈ H, T < ((k : ℚ) + 1) * service i)
    (hbudget : (∑ i ∈ H, service i * (count i : ℚ)) ≤ T) :
    (∑ i ∈ H, count i) ≤ k := by
  classical
  by_contra hnot
  have hcount : k + 1 ≤ ∑ i ∈ H, count i := by omega
  have hpos : 0 < ∑ i ∈ H, count i := by omega
  obtain ⟨j, hj, hjpos⟩ := Finset.sum_pos_iff.mp hpos
  have hterms : ∀ i ∈ H,
      T * (count i : ℚ) ≤
        ((k : ℚ) + 1) * (service i * (count i : ℚ)) := by
    intro i hi
    have hi' := mul_le_mul_of_nonneg_right
      (le_of_lt (hlarge i hi)) (Nat.cast_nonneg (count i) : (0 : ℚ) ≤ count i)
    nlinarith
  have hjcast : (0 : ℚ) < count j := by exact_mod_cast hjpos
  have hjstrict : T * (count j : ℚ) <
      ((k : ℚ) + 1) * (service j * (count j : ℚ)) := by
    have h := mul_lt_mul_of_pos_right (hlarge j hj) hjcast
    nlinarith
  have hsum := Finset.sum_lt_sum hterms ⟨j, hj, hjstrict⟩
  have hstrict :
      T * ((∑ i ∈ H, count i : ℕ) : ℚ) <
        ((k : ℚ) + 1) * (∑ i ∈ H, service i * (count i : ℚ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum] using hsum
  have hcountQ : (k : ℚ) + 1 ≤ ((∑ i ∈ H, count i : ℕ) : ℚ) := by
    exact_mod_cast hcount
  have hlower := mul_le_mul_of_nonneg_left hcountQ hT
  have hupper := mul_le_mul_of_nonneg_left hbudget
    (show (0 : ℚ) ≤ (k : ℚ) + 1 by positivity)
  nlinarith

/-- Division-form interface for the same graph-independent theorem. -/
theorem count_le_of_threshold
    (H : Finset V) (count : V → ℕ) (service : V → ℚ)
    (T : ℚ) (k : ℕ)
    (hT : 0 ≤ T)
    (hlarge : ∀ i ∈ H, T / ((k : ℚ) + 1) < service i)
    (hbudget : (∑ i ∈ H, service i * (count i : ℚ)) ≤ T) :
    (∑ i ∈ H, count i) ≤ k := by
  apply count_le_of_large H count service T k hT
  · intro i hi
    have h := (div_lt_iff₀
      (show (0 : ℚ) < (k : ℚ) + 1 by positivity)).mp (hlarge i hi)
    nlinarith
  · exact hbudget

/-- Exact coverage transfers per-container counting bounds to total demand. -/
theorem demand_count_le_fleet_capacity
    (ks : Finset ι) (H : Finset V)
    (count : ι → V → ℕ) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) (k : ℕ)
    (hT : 0 ≤ T)
    (hlarge : ∀ i ∈ H, T < ((k : ℚ) + 1) * service i)
    (hcover : ∀ i ∈ H, (∑ r ∈ ks, count r i) = required i)
    (hbudget : ∀ r ∈ ks, (∑ i ∈ H, service i * (count r i : ℚ)) ≤ T) :
    (∑ i ∈ H, required i) ≤ k * ks.card := by
  classical
  calc
    (∑ i ∈ H, required i) = ∑ i ∈ H, ∑ r ∈ ks, count r i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hcover i hi).symm
    _ = ∑ r ∈ ks, ∑ i ∈ H, count r i := Finset.sum_comm
    _ ≤ ∑ _r ∈ ks, k := by
      apply Finset.sum_le_sum
      intro r hr
      exact count_le_of_large H (count r) service T k hT hlarge (hbudget r hr)
    _ = k * ks.card := by simp [Nat.mul_comm]

end Counting

section Routes

variable {V ι : Type*} [DecidableEq V] {depot : V}

/-- Nonnegative costs let a full task-set budget bound any subset's service. -/
theorem routeServiceIn_mono
    (r : LegalRoute depot) (H tasks : Finset V) (service : V → ℚ)
    (hsub : H ⊆ tasks) (hservice : ∀ i ∈ tasks, 0 ≤ service i) :
    routeServiceIn r H service ≤ routeServiceIn r tasks service := by
  unfold routeServiceIn
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro i hi _
  exact mul_nonneg (hservice i hi) (Nat.cast_nonneg _)

/-- Actual visit lists and exact coverage imply the large-service demand bound.
Only the task-set service budget is needed; any extra nonnegative travel costs
may be discarded when deriving this premise from a full route budget. -/
theorem required_large_count_le
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks H : Finset V) (service : V → ℚ) (required : V → ℕ)
    (T : ℚ) (k : ℕ)
    (hdepot : depot ∉ H) (hsub : H ⊆ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hT : 0 ≤ T)
    (hlarge : ∀ i ∈ H, T < ((k : ℚ) + 1) * service i)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (∑ i ∈ H, required i) ≤ k * ks.card := by
  apply demand_count_le_fleet_capacity ks H
    (fun r i => (routes r).visits.count i) required service T k hT hlarge
  · intro i hi
    have hidepot : i ≠ depot := by
      intro heq
      subst i
      exact hdepot hi
    simpa only [totalVisitCount] using hvisits i hidepot
  · intro r hr
    exact (routeServiceIn_mono (routes r) H tasks service hsub hservice).trans
      (hbudget r hr)

/-- Direct H_k = {i in tasks | service i > T/(k+1)} interface. -/
theorem required_threshold_count_le
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (required : V → ℕ)
    (T : ℚ) (k : ℕ)
    (hdepot : depot ∉ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i) (hT : 0 ≤ T)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (∑ i ∈ tasks.filter (fun i => T / ((k : ℚ) + 1) < service i),
      required i) ≤ k * ks.card := by
  classical
  apply required_large_count_le ks routes tasks
    (tasks.filter (fun i => T / ((k : ℚ) + 1) < service i))
    service required T k
  · intro hmem
    exact hdepot (Finset.mem_filter.mp hmem).1
  · exact Finset.filter_subset _ _
  · exact hservice
  · exact hT
  · intro i hi
    have h := (div_lt_iff₀
      (show (0 : ℚ) < (k : ℚ) + 1 by positivity)).mp
        (Finset.mem_filter.mp hi).2
    nlinarith
  · exact hvisits
  · exact hbudget

end Routes

namespace Family

abbrev Node := Fin 3

def tasks : Finset Node := {1, 2}
def required (m : ℕ) (i : Node) : ℕ :=
  if i = 1 then m else if i = 2 then 1 else 0
def service (m : ℕ) (_i : Node) : ℚ := m
def capacity (m : ℕ) : ℚ := (m : ℚ) + 1
def degree (m : ℕ) (i : Node) : ℕ :=
  if i = 0 then m else required m i

/-- m departures to a, m-1 direct returns, and one a-b-depot path. -/
def witnessFlow (m : ℕ) : Node → Node → ℕ :=
  ![![0, m, 0], ![m - 1, 0, 1], ![1, 0, 0]]

theorem witness_out_degrees (m : ℕ) (hm : 2 ≤ m) (i : Node) :
    outFlow Finset.univ (witnessFlow m) i = degree m i := by
  fin_cases i <;>
    simp [outFlow, witnessFlow, degree, required, Fin.sum_univ_succ] <;> omega

theorem witness_in_degrees (m : ℕ) (hm : 2 ≤ m) (i : Node) :
    inFlow Finset.univ (witnessFlow m) i = degree m i := by
  fin_cases i <;>
    simp [inFlow, witnessFlow, degree, required, Fin.sum_univ_succ] <;> omega

theorem witness_no_diagonal (m : ℕ) (i : Node) : witnessFlow m i i = 0 := by
  fin_cases i <;> simp [witnessFlow]

/-- Classification of ALL depot-free sets; no route enumeration is used. -/
theorem depot_free_sets (S : Finset Node) (hdepot : (0 : Node) ∉ S) :
    S = ∅ ∨ S = {1} ∨ S = {2} ∨ S = tasks := by
  by_cases h1 : (1 : Node) ∈ S
  · by_cases h2 : (2 : Node) ∈ S
    · right; right; right
      ext i
      fin_cases i <;> simp_all [tasks]
    · right; left
      ext i
      fin_cases i <;> simp_all
  · by_cases h2 : (2 : Node) ∈ S
    · right; right; left
      ext i
      fin_cases i <;> simp_all
    · left
      ext i
      fin_cases i <;> simp_all

theorem cut_a (m : ℕ) (hm : 2 ≤ m) :
    outCutFlow ({1} : Finset Node) (witnessFlow m) = m := by
  simp [outCutFlow, witnessFlow, Finset.sum_filter, Fin.sum_univ_succ] <;> omega

theorem cut_b (m : ℕ) :
    outCutFlow ({2} : Finset Node) (witnessFlow m) = 1 := by
  simp [outCutFlow, witnessFlow, Finset.sum_filter, Fin.sum_univ_succ]

theorem cut_tasks (m : ℕ) (hm : 2 ≤ m) :
    outCutFlow tasks (witnessFlow m) = m := by
  simp [tasks, outCutFlow, witnessFlow, Finset.sum_filter, Fin.sum_univ_succ] <;> omega

theorem work_a (m : ℕ) :
    requiredServiceIn ({1} : Finset Node) (service m) (required m) =
      (m : ℚ) * (m : ℚ) := by
  simp [requiredServiceIn, service, required]

theorem work_b (m : ℕ) :
    requiredServiceIn ({2} : Finset Node) (service m) (required m) = (m : ℚ) := by
  simp [requiredServiceIn, service, required]

theorem total_budget_equality (m : ℕ) :
    requiredServiceIn tasks (service m) (required m) = (m : ℚ) * capacity m := by
  simp [tasks, requiredServiceIn, service, required, capacity] <;> ring

theorem witness_connected (m : ℕ) (hm : 2 ≤ m)
    (S : Finset Node) (hne : S.Nonempty) (hdepot : (0 : Node) ∉ S) :
    1 ≤ outCutFlow S (witnessFlow m) := by
  rcases depot_free_sets S hdepot with h | h | h | h
  · subst S
    simp at hne
  · subst S
    rw [cut_a m hm]
    omega
  · subst S
    exact (cut_b m).ge
  · subst S
    rw [cut_tasks m hm]
    omega

theorem witness_capacity (m : ℕ) (hm : 2 ≤ m)
    (S : Finset Node) (hdepot : (0 : Node) ∉ S) :
    requiredServiceIn S (service m) (required m) ≤
      (outCutFlow S (witnessFlow m) : ℚ) * capacity m := by
  rcases depot_free_sets S hdepot with h | h | h | h
  · subst S
    simp [requiredServiceIn, outCutFlow]
  · subst S
    rw [work_a, cut_a m hm]
    have hnonneg : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    unfold capacity
    nlinarith
  · subst S
    rw [work_b, cut_b]
    norm_num [capacity] <;> linarith
  · subst S
    simpa only [total_budget_equality, cut_tasks m hm] using
      (le_refl ((m : ℚ) * capacity m))

/-- All integer rounded capacity cuts, including the empty set. -/
theorem witness_all_rounded_cuts (m : ℕ) (hm : 2 ≤ m)
    (S : Finset Node) (hdepot : (0 : Node) ∉ S) :
    Int.ceil (requiredServiceIn S (service m) (required m) / capacity m) ≤
      (outCutFlow S (witnessFlow m) : ℤ) := by
  have hcap : (0 : ℚ) < capacity m := by unfold capacity; positivity
  have hdiv : requiredServiceIn S (service m) (required m) / capacity m ≤
      (outCutFlow S (witnessFlow m) : ℚ) :=
    (div_le_iff₀ hcap).2 (witness_capacity m hm S hdepot)
  apply Int.ceil_le.mpr
  exact_mod_cast hdiv

/-- The full set of aggregate necessary conditions under discussion. -/
structure AggregateConditions (m : ℕ) (x : Node → Node → ℕ) : Prop where
  outgoing : ∀ i, outFlow Finset.univ x i = degree m i
  incoming : ∀ i, inFlow Finset.univ x i = degree m i
  noDiagonal : ∀ i, x i i = 0
  arcBounds : ∀ i j, 0 ≤ x i j ∧ x i j ≤ min (degree m i) (degree m j)
  connected : ∀ S : Finset Node, S.Nonempty → (0 : Node) ∉ S → 1 ≤ outCutFlow S x
  totalBudget : requiredServiceIn tasks (service m) (required m) ≤ (m : ℚ) * capacity m
  roundedCuts : ∀ S : Finset Node, (0 : Node) ∉ S →
    Int.ceil (requiredServiceIn S (service m) (required m) / capacity m) ≤
      (outCutFlow S x : ℤ)

theorem witness_aggregate_conditions (m : ℕ) (hm : 2 ≤ m) :
    AggregateConditions m (witnessFlow m) where
  outgoing := witness_out_degrees m hm
  incoming := witness_in_degrees m hm
  noDiagonal := witness_no_diagonal m
  arcBounds := flow_bounds_of_degrees (witnessFlow m) (degree m)
    (witness_out_degrees m hm) (witness_in_degrees m hm)
  connected := witness_connected m hm
  totalBudget := (total_budget_equality m).le
  roundedCuts := witness_all_rounded_cuts m hm

/-- k=1 excludes ANY fleet with exact coverage, not just one decomposition. -/
theorem no_budget_cover (m : ℕ) (hm : 2 ≤ m)
    {ι : Type*} (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hcard : ks.card = m)
    (hvisits : ∀ i, i ≠ (0 : Node) → totalVisitCount ks routes i = required m i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks (service m) ≤ capacity m) :
    False := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have h := required_large_count_le ks routes tasks tasks
    (service m) (required m) (capacity m) 1
    (by simp [tasks])
    (by intro i hi; exact hi)
    (by intro i _; exact Nat.cast_nonneg m)
    (by unfold capacity; positivity)
    (by intro i _; dsimp [capacity, service]; norm_num; linarith)
    hvisits hbudget
  have hrequired : (∑ i ∈ tasks, required m i) = m + 1 := by
    simp [tasks, required]
  rw [hrequired, hcard] at h
  omega

/-- Exact edge-flow recovery implies exact coverage by the existing flow bridge. -/
theorem no_exact_decomposition (m : ℕ) (hm : 2 ≤ m)
    {ι : Type*} (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hcard : ks.card = m)
    (hflow : totalRouteFlow ks routes = witnessFlow m)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks (service m) ≤ capacity m) :
    False := by
  apply no_budget_cover m hm ks routes hcard
  · intro i hi
    calc
      totalVisitCount ks routes i = outFlow Finset.univ (totalRouteFlow ks routes) i :=
        (total_outFlow_eq_visit_count ks routes i hi).symm
      _ = outFlow Finset.univ (witnessFlow m) i := by rw [hflow]
      _ = degree m i := witness_out_degrees m hm i
      _ = required m i := by simp [degree, hi]
  · exact hbudget

/-- Parameterized insufficiency theorem for every m >= 2. -/
theorem rounded_cuts_not_sufficient (m : ℕ) (hm : 2 ≤ m) :
    AggregateConditions m (witnessFlow m) ∧
      ¬ ∃ routes : Fin m → LegalRoute (0 : Node),
        totalRouteFlow Finset.univ routes = witnessFlow m ∧
        (∀ r, routeServiceIn (routes r) tasks (service m) ≤ capacity m) := by
  refine ⟨witness_aggregate_conditions m hm, ?_⟩
  rintro ⟨routes, hflow, hbudget⟩
  exact no_exact_decomposition m hm Finset.univ routes
    (by simp) hflow (fun r _ => hbudget r)

end Family

#print axioms count_le_of_large
#print axioms count_le_of_threshold
#print axioms demand_count_le_fleet_capacity
#print axioms required_large_count_le
#print axioms required_threshold_count_le
#print axioms Family.witness_aggregate_conditions
#print axioms Family.no_budget_cover
#print axioms Family.no_exact_decomposition
#print axioms Family.rounded_cuts_not_sufficient

end UAVProof.LargeServiceCuts
