import LeanCompletion.UAV.TreeBudgetSubtreeRoot

/-! Support/linear-cost states. Root children retain the necessary top-edge
cap. This is a semantic compression theorem, not a runtime bound. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence TreeBudgetRow
variable {V : Type*} [Fintype V] [DecidableEq V]

def parentCharge (R : RootedTree V) (s : V → ℚ) (v : V) : ℚ :=
  if R.parent v = R.root then 0 else s (R.parent v)

def linearWeight (R : RootedTree V) (s : V → ℚ) (v : V) : ℚ :=
  s v + parentCharge R s v

noncomputable def subtreeLinearCost (R : RootedTree V) (s : V → ℚ)
    (v : V) (n : V → ℕ) : ℚ :=
  ∑ x ∈ subtree R v, linearWeight R s x * (n x : ℚ)

theorem subtreeLinearCost_eq (R : RootedTree V) (s : V → ℚ) (v : V)
    (hv : v ≠ R.root) (n : V → ℕ) :
    subtreeLinearCost R s v n = subtreeCost R s v n + parentCharge R s v * (n v : ℚ) := by
  classical
  rw [subtreeLinearCost, sum_subtree, subtreeCost_split]
  have hc : (∑ u ∈ R.children v, ∑ x ∈ subtree R u, linearWeight R s x * (n x : ℚ)) =
      (∑ u ∈ R.children v, subtreeCost R s u n) +
        s v * ∑ u ∈ R.children v, (n u : ℚ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hus := (R.mem_children v u).mp hu
    simpa only [parentCharge, hus.2, if_neg hv] using
      subtreeLinearCost_eq R s u hus.1 n
  rw [hc]
  simp only [linearWeight, Nat.cast_add, Nat.cast_sum]
  ring
termination_by R.rank v
decreasing_by exact R.child_rank hu

structure CompactState (m : ℕ) where
  active : Finset (Fin m)
  cost : Fin m → ℚ
  deriving Inhabited

def RootChildCap (R : RootedTree V) {m : ℕ} (v : V) (q : Fin m → ℕ) : Prop :=
  R.parent v = R.root → ∀ i, q i ≤ 1

def CompactRep (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ)
    (v : V) (z : CompactState m) : Prop :=
  ∃ n, PartialValid R H m v n ∧ RootChildCap R v (fun i => n i v) ∧
    (∀ i, i ∈ z.active ↔ 0 < n i v) ∧
    ∀ i, subtreeLinearCost R s v (n i) = z.cost i

theorem compactRep_iff_partialRep (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (v : V) (hv : v ≠ R.root) (z : CompactState m) :
    CompactRep R H m s v z ↔ ∃ full : BoundaryState m,
      PartialRep R H m s v full ∧ RootChildCap R v full.q ∧
      (∀ i, i ∈ z.active ↔ 0 < full.q i) ∧
      ∀ i, z.cost i = full.cost i + parentCharge R s v * (full.q i : ℚ) := by
  constructor
  · rintro ⟨n, hn, hcap, ha, hc⟩
    exact ⟨⟨fun i => n i v, fun i => subtreeCost R s v (n i)⟩,
      ⟨n, hn, fun _ => rfl, fun _ => rfl⟩, hcap, ha,
      fun i => (hc i).symm.trans (subtreeLinearCost_eq R s v hv (n i))⟩
  · rintro ⟨full, ⟨n, hn, hq, hc⟩, hcap, ha, hz⟩
    refine ⟨n, hn, ?_, ?_, ?_⟩
    · simpa only [hq] using hcap
    · simpa only [hq] using ha
    · intro i
      rw [subtreeLinearCost_eq R s v hv, hq i, hc i, hz i]

theorem compactRep_merge_iff (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (v : V) (hv : v ≠ R.root) (z : CompactState m) :
    CompactRep R H m s v z ↔ ∃ q : Fin m → ℕ,
      (∑ i, q i) = H v ∧ RootChildCap R v q ∧
      (∀ i, i ∈ z.active ↔ 0 < q i) ∧ ∃ zs : V → CompactState m,
        (∀ u ∈ R.children v, CompactRep R H m s u (zs u)) ∧
        (∀ u ∈ R.children v, (zs u).active ⊆ z.active) ∧
        ∀ i, z.cost i = linearWeight R s v * (q i : ℚ) +
          ∑ u ∈ R.children v, (zs u).cost i := by
  classical
  constructor
  · rintro ⟨n, hn, hcap, ha, hc⟩
    refine ⟨fun i => n i v, hn.column v .self, hcap, ha,
      fun u => ⟨Finset.univ.filter (fun i => 0 < n i u),
        fun i => subtreeLinearCost R s u (n i)⟩, ?_, ?_, ?_⟩
    · intro u hu
      refine ⟨restrictMatrix R u n, partial_restrict_valid hn hu, ?_, ?_, ?_⟩
      · intro hp
        exact (hv (((R.mem_children v u).mp hu).2.symm.trans hp)).elim
      · intro i; simp [restrictMatrix_eq n i InSubtree.self]
      · intro i
        apply Finset.sum_congr rfl
        intro x hx
        rw [restrictMatrix_eq n i ((mem_subtree _ _ _).mp hx)]
    · intro u hu i hi
      apply (ha i).mpr
      have hp : 0 < n i u := (Finset.mem_filter.mp hi).2
      exact hn.positive_top i (child_mem_subtree hu) hp
    · intro i
      rw [← hc i, subtreeLinearCost, sum_subtree]
      rfl
  · rintro ⟨q, hq, hcap, ha, zs, hz, hs, hc⟩
    have hw : ∀ u, ∃ n : Fin m → V → ℕ, u ∈ R.children v →
        PartialValid R H m u n ∧ RootChildCap R u (fun i => n i u) ∧
          (∀ i, i ∈ (zs u).active ↔ 0 < n i u) ∧
          ∀ i, subtreeLinearCost R s u (n i) = (zs u).cost i := by
      intro u
      by_cases hu : u ∈ R.children v
      · obtain ⟨n, hn⟩ := hz u hu
        exact ⟨n, fun _ => hn⟩
      · exact ⟨fun _ _ => 0, fun h => (hu h).elim⟩
    choose ns hn using hw
    have hvalid := fun u hu => (hn u hu).1
    refine ⟨glueMatrix R v q ns, partial_glue_valid hq hvalid ?_, ?_, ?_, ?_⟩
    · intro u hu i hp
      exact (ha i).mp (hs u hu ((hn u hu).2.2.1 i |>.mpr hp))
    · simpa only [glueMatrix_top] using hcap
    · simpa only [glueMatrix_top] using ha
    · intro i
      rw [subtreeLinearCost, sum_subtree, glueMatrix_top, hc i]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      calc
        (∑ x ∈ subtree R u, linearWeight R s x * (glueMatrix R v q ns i x : ℚ)) =
            subtreeLinearCost R s u (ns u i) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [glueMatrix_child q hvalid hu ((mem_subtree _ _ _).mp hx)]
        _ = (zs u).cost i := (hn u hu).2.2.2 i

/-- Each route belongs to exactly one root-child support. The sum counts set
membership, not boundary multiplicities; `CompactRep` supplies the cap. -/
def CompactRootAccept (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ zs : V → CompactState m,
    (∀ u ∈ R.children R.root, CompactRep R H m s u (zs u)) ∧
    (∀ i, (∑ u ∈ R.children R.root, if i ∈ (zs u).active then (1 : ℕ) else 0) = 1) ∧
    ∀ i, (∑ u ∈ R.children R.root, (zs u).cost i) ≤ T

theorem capped_eq_indicator {m : ℕ} (q : Fin m → ℕ) (A : Finset (Fin m))
    (hcap : ∀ i, q i ≤ 1) (ha : ∀ i, i ∈ A ↔ 0 < q i) (i : Fin m) :
    q i = if i ∈ A then 1 else 0 := by
  split_ifs with hi
  · have := (ha i).mp hi; have := hcap i; omega
  · have : ¬ 0 < q i := mt (ha i).mpr hi
    omega

theorem compactRootAccept_iff_matrixFeasible (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) :
    CompactRootAccept R H m s T ↔ TreeBudgetMatrix.MatrixFeasible R H m s T := by
  classical
  rw [← rootAccept_iff_matrixFeasible]
  constructor
  · rintro ⟨zs, hz, hdegree, hbudget⟩
    have hw : ∀ u, ∃ full : BoundaryState m, u ∈ R.children R.root →
        PartialRep R H m s u full ∧ RootChildCap R u full.q ∧
        (∀ i, i ∈ (zs u).active ↔ 0 < full.q i) ∧
        ∀ i, (zs u).cost i = full.cost i + parentCharge R s u * (full.q i : ℚ) := by
      intro u
      by_cases hu : u ∈ R.children R.root
      · obtain ⟨full, hf⟩ := (compactRep_iff_partialRep R H m s u
          ((R.mem_children _ _).mp hu).1 (zs u)).mp (hz u hu)
        exact ⟨full, fun _ => hf⟩
      · exact ⟨⟨fun _ => 0, fun _ => 0⟩, fun h => (hu h).elim⟩
    choose full hf using hw
    refine ⟨full, fun u hu => (hf u hu).1, ?_, ?_⟩
    · intro i
      convert hdegree i using 1
      apply Finset.sum_congr rfl
      intro u hu
      exact capped_eq_indicator _ _ ((hf u hu).2.1 ((R.mem_children _ _).mp hu).2)
        (hf u hu).2.2.1 i
    · intro i
      convert hbudget i using 1
      apply Finset.sum_congr rfl
      intro u hu
      simpa [parentCharge, ((R.mem_children _ _).mp hu).2] using ((hf u hu).2.2.2 i).symm
  · rintro ⟨full, hf, hdegree, hbudget⟩
    have hcap : ∀ u ∈ R.children R.root, ∀ i, (full u).q i ≤ 1 := by
      intro u hu i
      rw [← hdegree i]
      exact Finset.single_le_sum (fun w _ => Nat.zero_le ((full w).q i)) hu
    let zs : V → CompactState m := fun u =>
      ⟨Finset.univ.filter (fun i => 0 < (full u).q i), (full u).cost⟩
    have ha : ∀ u i, i ∈ (zs u).active ↔ 0 < (full u).q i := by
      intro u i; simp [zs]
    refine ⟨zs, ?_, ?_, hbudget⟩
    · intro u hu
      apply (compactRep_iff_partialRep R H m s u ((R.mem_children _ _).mp hu).1 (zs u)).mpr
      refine ⟨full u, hf u hu, fun _ => hcap u hu, ha u, ?_⟩
      intro i
      simp [zs, parentCharge, ((R.mem_children _ _).mp hu).2]
    · intro i
      convert hdegree i using 1
      apply Finset.sum_congr rfl
      intro u hu
      exact (capped_eq_indicator _ _ (hcap u hu) (ha u) i).symm

end UAVProof.TreeBudgetSubtreeState

#print axioms UAVProof.TreeBudgetSubtreeState.subtreeLinearCost_eq
#print axioms UAVProof.TreeBudgetSubtreeState.compactRep_iff_partialRep
#print axioms UAVProof.TreeBudgetSubtreeState.compactRep_merge_iff
#print axioms UAVProof.TreeBudgetSubtreeState.compactRootAccept_iff_matrixFeasible
