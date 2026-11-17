import LeanCompletion.UAV.TreeBudgetSubtreeScalarControls

/-! H/I composition under one padded arithmetic model. The H portion is
repriced at the common maximum width when the guard passes. -/
namespace UAVProof.TreeBudgetSubtreeScalar
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeState TreeBudgetSubtreeAutoScaleSeed
open TreeBudgetSubtreePre (Input Represents Run guardC prepareC bitWork serviceBits massBits)
variable {N : Nat}

def executeC (R : RootedTree (Fin N)) (I : Input N) :
    Run (ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N)))) :=
  let g := guardC I
  if g.value then
    let p := prepareC I
    let r := solveC R (val I.mass) (val p.value.weight) I.routes p.value.budget
    ⟨r.value, g.ops+p.ops+r.ops+8,
      max g.width (max p.width (dpWidth N I.routes (serviceBits I) (massBits I) r.ops))⟩
  else ⟨⟨none, {}, {}⟩, g.ops+1, g.width⟩

/-- Entire return record, not just feasibility or an abstract equivalent witness. -/
theorem executeC_pre_value (R : RootedTree (Fin N)) (I : Input N) :
    (executeC R I).value = (TreeBudgetSubtreePre.execute R I).value := by
  simp only [executeC, TreeBudgetSubtreePre.execute]
  split <;> simp

theorem executeC_pass_ops (R : RootedTree (Fin N)) (I : Input N)
    (hg : (guardC I).value = true) :
    (executeC R I).ops = (TreeBudgetSubtreePre.execute R I).ops +
      (solveC R (val I.mass) (val (prepareC I).value.weight) I.routes
        (prepareC I).value.budget).ops+6 := by
  simp only [executeC, TreeBudgetSubtreePre.execute, hg, ↓reduceIte]
  omega

theorem executeC_pass_width (R : RootedTree (Fin N)) (I : Input N)
    (hg : (guardC I).value = true) :
    (executeC R I).width = max (TreeBudgetSubtreePre.execute R I).width
      (dpWidth N I.routes (serviceBits I) (massBits I)
        (solveC R (val I.mass) (val (prepareC I).value.weight) I.routes
          (prepareC I).value.budget).ops) := by
  simp only [executeC, TreeBudgetSubtreePre.execute, hg, ↓reduceIte]
  exact (max_assoc _ _ _).symm

theorem executeC_resource_eq (R : RootedTree (Fin N)) (I : Input N) (hr : Represents I R) :
    (executeC R I).value = solveGuardedR R (val I.mass) (val I.service) I.routes I.budget :=
  (executeC_pre_value R I).trans (TreeBudgetSubtreePre.execute_resource_eq I R hr)

theorem executeC_certificate_eq (R : RootedTree (Fin N)) (I : Input N)
    (hr : Represents I R) : (executeC R I).value.value =
      TreeBudgetSubtreeWitness.solve R (val I.mass) (val I.service) I.routes I.budget := by
  rw [executeC_pre_value]
  exact TreeBudgetSubtreePre.execute_certificate_eq I R hr

noncomputable def inputDPUpper (R : RootedTree (Fin N)) (I : Input N) : Nat :=
  dpUpper N I.routes (totalMass R (val I.mass)) (globalProduct R (val I.mass) I.routes)

noncomputable def commonWidth (R : RootedTree (Fin N)) (I : Input N) : Nat :=
  max (TreeBudgetSubtreePre.inputWidth N (serviceBits I) (massBits I) I.routes.size)
    (dpWidth N I.routes (serviceBits I) (massBits I) (inputDPUpper R I))

theorem prepared_solveC_bound (R : RootedTree (Fin N)) (I : Input N) (hr : Represents I R) :
    (solveC R (val I.mass) (val (prepareC I).value.weight) I.routes (prepareC I).value.budget).ops ≤
      inputDPUpper R I := by
  rw [TreeBudgetSubtreePre.prepareC_value I R hr]
  apply solveC_auto_bound
  intro v hv
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩)

theorem executeC_bounds (R : RootedTree (Fin N)) (I : Input N) (hr : Represents I R) :
    (executeC R I).ops ≤ 128*(N+1)*(serviceBits I+1)+inputDPUpper R I+6 ∧
    (executeC R I).width ≤ commonWidth R I := by
  have hp := TreeBudgetSubtreePre.execute_bounds I R _ _ _
    (TreeBudgetSubtreePre.inputFits_canonical I)
  have hd := prepared_solveC_bound R I hr
  have hpre := le_max_left
    (TreeBudgetSubtreePre.inputWidth N (serviceBits I) (massBits I) I.routes.size)
    (dpWidth N I.routes (serviceBits I) (massBits I) (inputDPUpper R I))
  have hdp := le_max_right
    (TreeBudgetSubtreePre.inputWidth N (serviceBits I) (massBits I) I.routes.size)
    (dpWidth N I.routes (serviceBits I) (massBits I) (inputDPUpper R I))
  dsimp only [executeC, TreeBudgetSubtreePre.execute] at *
  split
  · rename_i hg
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at hp
    constructor
    · dsimp only at *; omega
    · apply max_le
      · exact (le_max_left _ _).trans (hp.2.trans hpre)
      · apply max_le
        · exact (le_max_right _ _).trans (hp.2.trans hpre)
        · apply le_trans _ hdp
          unfold dpWidth
          omega
  · rename_i hg
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at hp
    exact ⟨by dsimp only at *; omega, hp.2.trans hpre⟩

/-- One uniform bit tariff for the complete passing execution, including the
six additional interface reads/control instructions. No total-cost hypothesis. -/
theorem executeC_bitWork_le (R : RootedTree (Fin N)) (I : Input N) (hr : Represents I R) :
    bitWork (executeC R I) ≤ 32*(commonWidth R I+1)^2*
      (128*(N+1)*(serviceBits I+1)+inputDPUpper R I+6) :=
  TreeBudgetSubtreePre.bitWork_le _ _ _ (executeC_bounds R I hr).2 (executeC_bounds R I hr).1

theorem executeC_reject_eq (R : RootedTree (Fin N)) (I : Input N)
    (hbad : I.routes ≠ (TreeBudgetSubtreePre.rootMassC I).value) :
    executeC R I = TreeBudgetSubtreePre.execute R I := by
  simp [executeC, TreeBudgetSubtreePre.execute, guardC, hbad]

/-- No m-dimensional object is created on rejection; only m's bit length enters. -/
theorem executeC_reject_bitWork_le (R : RootedTree (Fin N)) (I : Input N)
    (hbad : I.routes ≠ (TreeBudgetSubtreePre.rootMassC I).value) :
    bitWork (executeC R I) ≤
      32*(TreeBudgetSubtreePre.guardWidth N (massBits I) I.routes.size+1)^2*(12*N+5) := by
  rw [executeC_reject_eq R I hbad]
  exact TreeBudgetSubtreePre.execute_reject_bitWork_le I R _ _
    (TreeBudgetSubtreePre.inputFits_canonical I).2.2.2.1 le_rfl hbad


/-- A cursor into any executed descendant table fits the actual uniform run.
The only premises identify that table and its prefix/suffix position. -/
theorem executeC_table_cursor_fits (R : RootedTree (Fin N)) (I : Input N)
    (hg : (guardC I).value = true) (u v : Fin N)
    (hu : u ∈ (childrenC R R.root).value)
    (hv : Relation.ReflTransGen (fun x y => y ∈ (childrenC R x).value) u v)
    (k : Nat) (hk : k ≤ (computeC R (val I.mass) (val (prepareC I).value.weight) I.routes v).value.value.length) :
    k.size+1 ≤ (executeC R I).width := by
  have hc := solveC_descendant_cursor R (val I.mass) (val (prepareC I).value.weight)
    I.routes (prepareC I).value.budget u v hu hv k hk
  rw [executeC_pass_width R I hg]
  apply le_trans _ (le_max_right _ _)
  unfold dpWidth
  omega

end UAVProof.TreeBudgetSubtreeScalar
