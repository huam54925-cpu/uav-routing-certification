import LeanCompletion.UAV.TreeBudgetSubtreePreExecution

/-! H2/H3/H4: bounds on the actual counted run, including rejected inputs.
No bound on m's numeric value is used by the preprocessing proof. -/
namespace UAVProof.TreeBudgetSubtreePre
open TreeFlowExistence TreeBudgetSubtreeExecutable TreeBudgetSubtreeState
open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeResourceSeed
variable {N : ℕ}

def InputFits (I : Input N) (b h mu : ℕ) : Prop :=
  1 ≤ b ∧ (∀ v : Fin N, RatFits I.service[v] b) ∧ RatFits I.budget b ∧
    (∀ v : Fin N, I.mass[v].size ≤ h) ∧ I.routes.size ≤ mu

/-- Analysis parameters only: execute does not compute these maxima before
the guard. Including root service bits gives a simple total input convention. -/
def serviceBits (I : Input N) : ℕ :=
  max 1 (max (max I.budget.num.natAbs.size I.budget.den.size)
    (Finset.univ.sup fun v : Fin N => max I.service[v].num.natAbs.size I.service[v].den.size))

def massBits (I : Input N) : ℕ := Finset.univ.sup fun v : Fin N => I.mass[v].size

theorem inputFits_canonical (I : Input N) :
    InputFits I (serviceBits I) (massBits I) I.routes.size := by
  have hs (v : Fin N) : max I.service[v].num.natAbs.size I.service[v].den.size ≤
      Finset.univ.sup (fun v : Fin N => max I.service[v].num.natAbs.size I.service[v].den.size) :=
    Finset.le_sup (f := fun v : Fin N => max I.service[v].num.natAbs.size I.service[v].den.size)
      (Finset.mem_univ v)
  refine ⟨by unfold serviceBits; omega, ?_, ?_, ?_, le_rfl⟩
  · intro v
    have hv := hs v
    dsimp [RatFits, serviceBits]
    simp only [Fin.getElem_fin] at hv ⊢
    omega
  · dsimp [RatFits, serviceBits]
    omega
  · intro v
    exact Finset.le_sup (f := fun v : Fin N => I.mass[v].size) (Finset.mem_univ v)

theorem coefficientC_bounds (I : Input N) (b : ℕ) (hb : 1 ≤ b)
    (hs : ∀ v : Fin N, RatFits I.service[v] b) (v : Fin N) :
    (coefficientC I v).ops ≤ 16*b+31 ∧
    (coefficientC I v).width ≤ N+2*b+2 ∧ RatFits (coefficientC I v).value (2*b+1) := by
  have hn := size_self_le N
  have hz : RatFits 0 b := by simp [RatFits]; omega
  have ha := ratAddC_bounds I.service[v]
    (if I.parent[v] = I.root then 0 else I.service[I.parent[v]]) b (hs v)
    (by split <;> simp_all)
  unfold coefficientC
  split
  · simp [RatFits]; omega
  · dsimp only
    exact ⟨by omega, by omega, ha.2.2⟩

theorem rootScan_bounds (I : Input N) (h : ℕ) (hH : ∀ v : Fin N, I.mass[v].size ≤ h)
    (vs : List (Fin N)) :
    (rootScan I vs).ops ≤ 12*vs.length+1 ∧
    (rootScan I vs).width ≤ N+vs.length*(h+1)+1 ∧
    (rootScan I vs).value.size ≤ vs.length*(h+1) := by
  have hn := size_self_le N
  induction vs with
  | nil => simp [rootScan]
  | cons v vs ih =>
    have hv := hH v
    have ha := size_add I.mass[v] (rootScan I vs).value
    simp only [rootScan, List.length_cons]
    split
    · dsimp only
      constructor
      · nlinarith [ih.1]
      constructor
      · apply max_le
        · nlinarith
        · apply max_le
          · nlinarith [ih.2.1]
          · nlinarith [ih.2.2]
      · have hh : max I.mass[v].size (rootScan I vs).value.size ≤
            I.mass[v].size + (rootScan I vs).value.size := by omega
        nlinarith [ih.2.2]
    · dsimp only
      exact ⟨by nlinarith [ih.1], max_le (by nlinarith) (by nlinarith [ih.2.1]),
        by nlinarith [ih.2.2]⟩

theorem rootMassC_bounds (I : Input N) (h : ℕ) (hH : ∀ v : Fin N, I.mass[v].size ≤ h) :
    (rootMassC I).ops ≤ 12*N+1 ∧ (rootMassC I).width ≤ N+N*(h+1)+1 ∧
    (rootMassC I).value.size ≤ N*(h+1) := by
  simpa [rootMassC] using rootScan_bounds I h hH (List.finRange N)

theorem rootScan_partial_le (I : Input N) (R : RootedTree (Fin N))
    (h : Represents I R) (vs : List (Fin N)) (hv : vs.Sublist (List.finRange N)) :
    (rootScan I vs).value ≤ totalMass R (val I.mass) := by
  have hh : (rootScan I vs).value ≤ (rootMassC I).value := by
    rw [rootScan_value, rootMassC, rootScan_value]
    apply List.Sublist.sum_le_sum
    · exact (hv.filter _).map _
    · intro a ha; exact Nat.zero_le _
  rw [rootMassC_value I R h] at hh
  exact hh.trans (TreeBudgetSubtreeResource.rootMass_le_totalMass R (val I.mass))

theorem denLCMC_bounds (as : List ℚ) (c : ℕ) (h : ∀ a ∈ as, a.den.size ≤ c) :
    (denLCMC as).ops ≤ (8*c+7)*as.length+1 ∧
    (denLCMC as).width ≤ as.length*c+1 ∧
    (denLCMC as).value.size ≤ as.length*c+1 := by
  induction as with
  | nil => simp [denLCMC]
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    have hd := lcmC_bounds a.den (denLCMC as).value
    simp only [denLCMC, List.length_cons]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [ht.1, hd.1]
    · rw [hd.2.1]
      apply max_le <;> nlinarith [ht.2.1, ht.2.2]
    · nlinarith [hd.2.2, ht.2.2]

/-- Covers every prefix, suffix and other sublist in the LCM computation. -/
theorem denLCMC_sublist_dvd (as bs : List ℚ) (h : as.Sublist bs) :
    (denLCMC as).value ∣ (denLCMC bs).value := by
  simp only [denLCMC_value]
  apply (TreeBudgetSubtreeResource.denLCM_dvd_iff _ _).2
  intro a ha
  exact den_dvd_denLCM (h.subset ha)

def prepWidth (N b : ℕ) : ℕ := N+(N+1)*(2*b+2)+b+2
def guardWidth (N h mu : ℕ) : ℕ := N+N*(h+1)+mu+1
def inputWidth (N b h mu : ℕ) : ℕ := (N+2)*(2*b+h+mu+4)

theorem prepareC_bounds (I : Input N) (b : ℕ) (hb : 1 ≤ b)
    (hs : ∀ v : Fin N, RatFits I.service[v] b) (hT : RatFits I.budget b) :
    (prepareC I).ops ≤ (48*b+85)*N+17 ∧ (prepareC I).width ≤ prepWidth N b := by
  let as := collect ((List.finRange N).map (coefficientC I))
  let d := denLCMC as.value
  have hc := coefficientC_bounds I b hb hs
  have ha : as.ops ≤ (16*b+33)*N+1 ∧ as.width ≤ N+2*b+2 := by
    have hh := collect_bounds ((List.finRange N).map (coefficientC I))
      (16*b+31) (N+2*b+2) (by omega) (by
        intro r hr
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
        exact ⟨(hc v).1, (hc v).2.1⟩)
    simpa [as] using hh
  have hlen : as.value.length = N := by simp [as]
  have hd := denLCMC_bounds as.value (2*b+1) (by
    intro a ha
    simp only [as, collect_value, List.map_map, Function.comp_def] at ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact (hc v).2.2.2)
  rw [hlen] at hd
  change d.ops ≤ _ ∧ d.width ≤ _ ∧ d.value.size ≤ _ at hd
  have hw := collectV_bounds (fun v => after (coefficientC I v)
      (scaleNumC d.value (coefficientC I v).value)) (16*b+35) (prepWidth N b)
    (by unfold prepWidth; omega) (by
      intro v
      have hv := hc v
      dsimp only [after, scaleNumC]
      constructor
      · omega
      · apply max_le
        · unfold prepWidth; nlinarith [hv.2.1]
        · apply max_le
          · unfold prepWidth; nlinarith [hd.2.2, hv.2.2.1]
          · unfold prepWidth; nlinarith [hv.2.2.2])
  have htw : (floorBudgetC d.value I.budget).width ≤ prepWidth N b := by
    dsimp [floorBudgetC, prepWidth]
    dsimp [RatFits] at hT
    apply max_le <;> nlinarith [hd.2.2, hT.1, hT.2]
  change as.ops + d.ops + (collectV _).ops + 8 + 6 ≤ _ ∧
    max as.width (max d.width (max (collectV _).width (floorBudgetC d.value I.budget).width)) ≤ _
  constructor
  · nlinarith [ha.1, hd.1, hw.1]
  · exact max_le (by unfold prepWidth; nlinarith [ha.2])
      (max_le (by unfold prepWidth; nlinarith [hd.2.1]) (max_le hw.2 htw))

theorem guardC_bounds (I : Input N) (h mu : ℕ)
    (hH : ∀ v : Fin N, I.mass[v].size ≤ h) (hm : I.routes.size ≤ mu) :
    (guardC I).ops ≤ 12*N+4 ∧ (guardC I).width ≤ guardWidth N h mu := by
  have hr := rootMassC_bounds I h hH
  dsimp only [guardC, guardWidth]
  constructor
  · omega
  · exact max_le (by omega) (max_le (by omega) (by omega))

set_option maxRecDepth 4096 in
theorem execute_bounds (I : Input N) (R : RootedTree (Fin N)) (b h mu : ℕ)
    (hf : InputFits I b h mu) :
    (execute R I).ops ≤ 128*(N+1)*(b+1) ∧
    (execute R I).width ≤ inputWidth N b h mu := by
  obtain ⟨hb, hs, hT, hH, hm⟩ := hf
  have hg := guardC_bounds I h mu hH hm
  have hp := prepareC_bounds I b hb hs hT
  have hgw : guardWidth N h mu ≤ inputWidth N b h mu := by
    unfold guardWidth inputWidth; nlinarith
  have hpw : prepWidth N b ≤ inputWidth N b h mu := by
    unfold prepWidth inputWidth; nlinarith
  unfold execute
  dsimp only
  split
  · dsimp only
    exact ⟨by nlinarith [hg.1, hp.1], max_le (hg.2.trans hgw) (hp.2.trans hpw)⟩
  · dsimp only
    exact ⟨by nlinarith [hg.1], hg.2.trans hgw⟩

/-- Explicit degree-six polynomial for the padded mathematical bit model. -/
def prePolynomial (N b h mu : ℕ) : ℕ :=
  4096*(N+1)*(b+1)*(inputWidth N b h mu+1)^2

theorem execute_preBitWork_le (I : Input N) (R : RootedTree (Fin N))
    (b h mu : ℕ) (hf : InputFits I b h mu) :
    bitWork (execute R I) ≤ prePolynomial N b h mu := by
  have he := execute_bounds I R b h mu hf
  apply (bitWork_le _ _ _ he.2 he.1).trans_eq
  unfold prePolynomial
  ring

theorem execute_preBitWork_canonical (I : Input N) (R : RootedTree (Fin N)) :
    bitWork (execute R I) ≤ prePolynomial N (serviceBits I) (massBits I) I.routes.size :=
  execute_preBitWork_le I R _ _ _ (inputFits_canonical I)

/-- Failure cost has no service/budget parameter and no dependence on m's value. -/
theorem execute_reject_bitWork_le (I : Input N) (R : RootedTree (Fin N))
    (h mu : ℕ) (hH : ∀ v : Fin N, I.mass[v].size ≤ h) (hm : I.routes.size ≤ mu)
    (hbad : I.routes ≠ (rootMassC I).value) :
    bitWork (execute R I) ≤ 32*(guardWidth N h mu+1)^2*(12*N+5) := by
  have hg := guardC_bounds I h mu hH hm
  rw [execute_reject I R hbad]
  exact bitWork_le _ _ _ hg.2 (by dsimp; omega)

/-- Both bounds are reported together without treating the mixed sum as time. -/
theorem execute_pre_and_DP_bounds (I : Input N) (R : RootedTree (Fin N))
    (hr : Represents I R) (b h mu : ℕ) (hf : InputFits I b h mu) :
    bitWork (execute R I) ≤ prePolynomial N b h mu ∧
    resourceWork (execute R I).value ≤
      64*(N+1)^2*(totalMass R (val I.mass)+1)^2*
        (max 1 (totalMass R (val I.mass)))^(2*totalMass R (val I.mass)) := by
  refine ⟨execute_preBitWork_le I R b h mu hf, ?_⟩
  rw [execute_resource_eq I R hr]
  exact solveGuardedR_resourceWork_le R (val I.mass) (val I.service) I.routes I.budget

end UAVProof.TreeBudgetSubtreePre
