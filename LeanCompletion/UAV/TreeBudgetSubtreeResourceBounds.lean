import LeanCompletion.UAV.TreeBudgetSubtreeResourceCensus
import LeanCompletion.UAV.TreeBudgetSubtreeResourceKeyMaps
import LeanCompletion.UAV.TreeBudgetSubtreeResourceGuard
import LeanCompletion.UAV.TreeBudgetSubtreeResourceWidths

/-! Global source-level resource bounds, excluding preprocessing and counter
maintenance. Matrix content capacities are not a bound on the entire heap. -/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeStats TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeAutoScaleSeed
variable {N m : ℕ}

theorem rawCount_eq_rational {D : ℕ} (hD : 0 < D)
    (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (hv : v ≠ R.root)
    (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    rawCount R H w m v =
      (nodeRaw R H s m v ((childrenList R v).map (computeCompact R H s m))).length := by
  have ht : (((childrenList R v).map (compute R H w m)).map (List.map Entry.key)).map
      (List.map (TreeBudgetSubtreeInteger.liftState D)) =
      (childrenList R v).map (computeCompact R H s m) := by
    simp only [List.map_map, Function.comp_def, compute_keys]
    apply List.map_congr_left
    intro u hu
    exact TreeBudgetSubtreeInteger.compute_lift_eq hD R H s w m u
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1 hw
  have hi (q : Vector ℕ m) :
      (inside (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ))
        ((childrenList R v).map (compute R H w m))).length =
      (insideCosts (support q) (Vector.ofFn fun i => linearWeight R s v * ((val q i : ℕ) : ℚ))
        ((childrenList R v).map (computeCompact R H s m))).length := by
    have hh := TreeBudgetSubtreeInteger.inside_lift_eq hD (support q)
      (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ))
      (((childrenList R v).map (compute R H w m)).map (List.map Entry.key))
    rw [ht, TreeBudgetSubtreeInteger.lift_initial hD (w v) _ (hw v hv), ← inside_keys] at hh
    simpa only [List.length_map] using congrArg List.length hh
  simp only [rawCount, nodeRawEntries, nodeRaw, List.length_flatMap, List.length_map, hi]

theorem auto_rawCount_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (v : Fin N) (hv : v ≠ R.root) :
    rawCount R H (val (prepare R s T).weight) m v ≤ globalProduct R H m := by
  rw [rawCount_eq_rational (prepare_pos R s T) R H s _ m v hv (prepare_weight R s T)]
  exact (nodeRaw_length_le_columnProduct R H s m v).trans
    (columnProduct_le_globalProduct R H m v hv)

theorem subtree_degrees (R : RootedTree (Fin N)) (v : Fin N) :
    (∑ x ∈ subtree R v, (childrenList R x).length) = subtreeSize R v - 1 := by
  classical
  rw [sum_subtree, ← childrenList_sum]
  have ht : ((childrenList R v).map fun u => ∑ x ∈ subtree R u, (childrenList R x).length) =
      (childrenList R v).map (fun u => subtreeSize R u - 1) := by
    apply List.map_congr_left
    intro u hu
    exact subtree_degrees R u
  rw [ht]
  have hs := subtreeSize_split R v
  have hp := sum_pred_sizes R (childrenList R v)
  omega
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp hu)

theorem sum_degrees (R : RootedTree (Fin N)) :
    (∑ x : Fin N, (childrenList R x).length) = N - 1 := by
  simpa [subtree_root, subtreeSize] using subtree_degrees R R.root

theorem total_rawCount_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    (∑ x ∈ Finset.univ.erase R.root, rawCount R H (val (prepare R s T).weight) m x) ≤
      (N - 1) * globalProduct R H m := by
  classical
  calc
    _ ≤ ∑ x ∈ Finset.univ.erase R.root, globalProduct R H m := by
      apply Finset.sum_le_sum
      intro x hx
      exact auto_rawCount_le R H s m T x (Finset.mem_erase.mp hx).1
    _ = _ := by simp

theorem weighted_rawCount_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (c : ℕ) (hc : c ≤ 1) :
    (∑ x ∈ Finset.univ.erase R.root,
      (childrenList R x).length * rawCount R H (val (prepare R s T).weight) m x) +
      c * (childrenList R R.root).length ≤ (N - 1) * globalProduct R H m := by
  classical
  have hp := globalProduct_pos R H m
  have hs : (∑ x ∈ Finset.univ.erase R.root,
      (childrenList R x).length * rawCount R H (val (prepare R s T).weight) m x) ≤
      ∑ x ∈ Finset.univ.erase R.root, (childrenList R x).length * globalProduct R H m := by
    apply Finset.sum_le_sum
    intro x hx
    exact Nat.mul_le_mul_left _ (auto_rawCount_le R H s m T x (Finset.mem_erase.mp hx).1)
  have hr := Nat.mul_le_mul_right (childrenList R R.root).length (hc.trans hp)
  have he := Finset.sum_erase_add Finset.univ (fun x => (childrenList R x).length)
    (Finset.mem_univ R.root)
  rw [sum_degrees] at he
  rw [← Finset.sum_mul] at hs
  nlinarith

theorem solveAutoR_payload_bounds (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    let p := (solveAutoR R H s m T).payload
    let P := globalProduct R H m
    p.matrices ≤ (N - 1) * P + 1 ∧
    p.matrixCells ≤ m * N * ((N - 1) * P + 1) ∧
    p.columnReads ≤ m * ((N - 1) * P + 1) ∧
    p.childReads ≤ m * (N - 1)^2 * P ∧
    p.natAdds ≤ m * (N - 1)^2 * P ∧
    p.tempCells ≤ m * (N - 1)^2 * P ∧
    p.pickCons ≤ (N - 1) * P ∧
    p.keyMapCells ≤ (N - 1) * P * (P - 1) ∧ p.rootZeroCells ≤ m := by
  classical
  have hf := solveR_charges R H (val (prepare R s T).weight) m (prepare R s T).budget
  change Charges N m (solveAutoR R H s m T).keyStats (solveAutoR R H s m T).payload _ _ _ at hf
  have hc := optionCount_le_one (solveAutoR R H s m T).value
  have ha := Nat.add_le_add (total_rawCount_le R H s m T) hc
  have hd := weighted_rawCount_le R H s m T _ hc
  have hm := Nat.mul_le_mul_left (m * (N - 1)) hd
  have hmc := Nat.mul_le_mul_left (m * N) ha
  have hcol := Nat.mul_le_mul_left m ha
  have hz := Nat.mul_le_mul_left m hc
  have hp := (checkCompactStats_bounds R H s m U T hU).2
  rw [← solveAutoR_keyStats] at hp
  have hk := solveAutoR_keyMapCells_le R H s m U T hU
  simp only [Charges] at hf
  dsimp only
  simp only [pow_two, Nat.mul_assoc] at hm ⊢
  rcases hf with ⟨hf₁, hf₂, hf₃, hf₄, hf₅, hf₆, hf₇, hf₈⟩
  dsimp only [solveAutoR] at hc ha hd hm hmc hcol hz hf₁ hf₂ hf₃ hf₄ hf₅ hf₆ hf₇ hf₈ hp hk ⊢
  simp only [Nat.mul_assoc] at *
  omega

theorem payload_envelope_le (N m U P : ℕ) (hp : 1 ≤ P) :
    ((N - 1) * P + 1) + m * N * ((N - 1) * P + 1) +
      m * (N - 1)^2 * P + m * (N - 1)^2 * P + m * (N - 1)^2 * P +
      m * ((N - 1) * P + 1) + (N - 1) * P + (N - 1) * P * (P - 1) + m ≤
      9 * (N + 1)^2 * (m + 1) * (U + 1) * P ^ 2 := by
  let K := (N + 1)^2
  let A := (m + 1) * (U + 1)
  let F := K * A * P ^ 2
  have hn : N - 1 ≤ N := Nat.sub_le _ _
  have hk : N + 1 ≤ K := by dsimp [K]; nlinarith
  have hk₁ : 1 ≤ K := by omega
  have hm : m ≤ A := by dsimp [A]; nlinarith
  have ha : 1 ≤ A := by dsimp [A]; nlinarith
  have hs : P ≤ P ^ 2 := by nlinarith
  have hb : (N - 1) * P + 1 ≤ (N + 1) * P := by nlinarith
  have hbound (a b c : ℕ) (h₁ : a ≤ K) (h₂ : b ≤ A) (h₃ : c ≤ P ^ 2) :
      a * b * c ≤ F := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
  have h₁ : (N - 1) * P + 1 ≤ F := hb.trans (by simpa using hbound (N + 1) 1 P hk ha hs)
  have h₂ : m * N * ((N - 1) * P + 1) ≤ F := by
    apply (Nat.mul_le_mul_left (m * N) hb).trans
    have hh := hbound (N * (N + 1)) m P (by dsimp [K]; nlinarith) hm hs
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
  have h₃ : m * (N - 1)^2 * P ≤ F := by
    have hh := hbound ((N - 1)^2) m P (by dsimp [K]; nlinarith) hm hs
    simpa [Nat.mul_comm, Nat.mul_left_comm] using hh
  have h₄ : m * ((N - 1) * P + 1) ≤ F := by
    apply (Nat.mul_le_mul_left m hb).trans
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound (N + 1) m P hk hm hs
  have h₅ : (N - 1) * P ≤ F := by omega
  have h₆ : (N - 1) * P * (P - 1) ≤ F := by
    have hh := hbound (N - 1) 1 (P ^ 2) (by omega) ha le_rfl
    have hsub := Nat.mul_le_mul_left ((N - 1) * P) (Nat.sub_le P 1)
    nlinarith
  have h₇ : m ≤ F := by simpa using hbound 1 m 1 hk₁ hm (by nlinarith)
  have hh : ((N - 1) * P + 1) + m * N * ((N - 1) * P + 1) +
      m * (N - 1)^2 * P + m * (N - 1)^2 * P + m * (N - 1)^2 * P +
      m * ((N - 1) * P + 1) + (N - 1) * P + (N - 1) * P * (P - 1) + m ≤ 9 * F := by omega
  simpa [F, K, A, Nat.mul_assoc] using hh

theorem solveAutoR_resourceWork_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    resourceWork (solveAutoR R H s m T) ≤
      64 * (N + 1)^2 * (m + 1) * (U + 1) * globalProduct R H m ^ 2 := by
  have hb := solveAutoR_payload_bounds R H s m U T hU
  have he := payload_envelope_le N m U (globalProduct R H m) (globalProduct_pos R H m)
  have hl := checkCompactStats_logicalWork_le R H s m U T hU
  rw [← solveAutoR_keyStats] at hl
  have hN : N ≤ (N + 1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_right ((m + 1) * (U + 1) * globalProduct R H m ^ 2)
    (Nat.mul_le_mul_left 32 hN)
  simp only [Nat.mul_assoc] at hl hh he
  dsimp only at hb
  unfold resourceWork PayloadStats.work
  simp only [Nat.mul_assoc] at hb ⊢
  omega

theorem solveAutoR_matrix_content_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    (solveAutoR R H s m T).payload.matrixCells * TreeBudgetSubtreeResource.coordBits U ≤
      m * N * ((N - 1) * globalProduct R H m + 1) * TreeBudgetSubtreeResource.coordBits U :=
  Nat.mul_le_mul_right _ (solveAutoR_payload_bounds R H s m U T hU).2.1

theorem solveAutoR_temp_content_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    (solveAutoR R H s m T).payload.tempCells * TreeBudgetSubtreeResource.coordBits U ≤
      m * (N - 1)^2 * globalProduct R H m * TreeBudgetSubtreeResource.coordBits U :=
  Nat.mul_le_mul_right _ (solveAutoR_payload_bounds R H s m U T hU).2.2.2.2.2.1

theorem guarded_resourceWork_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (hm : m = TreeBudgetSubtreeResource.rootMass R H) :
    resourceWork (solveAutoR R H s m T) ≤
      64 * (N + 1)^2 * (totalMass R H + 1)^2 * (max 1 (totalMass R H))^(2 * totalMass R H) := by
  classical
  have hU (v : Fin N) (hv : v ≠ R.root) : H v ≤ totalMass R H :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩)
  apply (solveAutoR_resourceWork_le R H s m (totalMass R H) T hU).trans
  have hr := TreeBudgetSubtreeResource.guarded_routes_le_mass R H m hm
  have hp := TreeBudgetSubtreeResource.guarded_globalProduct_le R H m hm
  calc
    _ ≤ 64 * (N + 1)^2 * (totalMass R H + 1) * (totalMass R H + 1) *
        ((max 1 (totalMass R H))^(totalMass R H))^2 := by gcongr
    _ = _ := by rw [← pow_mul]; ring

def solveGuardedR (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    ResourceResult (Option (TreeBudgetCertificate.Certificate (Fin N))) :=
  if m = TreeBudgetSubtreeResource.rootMass R H then solveAutoR R H s m T else ⟨none, {}, {}⟩

theorem solveGuardedR_erase (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    (solveGuardedR R H s m T).value = solveAuto R H s m T := by
  rw [← TreeBudgetSubtreeResource.solveGuarded_eq]
  unfold solveGuardedR TreeBudgetSubtreeResource.solveGuarded
  split <;> simp

theorem solveGuardedR_resourceWork_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    resourceWork (solveGuardedR R H s m T) ≤
      64 * (N + 1)^2 * (totalMass R H + 1)^2 * (max 1 (totalMass R H))^(2 * totalMass R H) := by
  unfold solveGuardedR
  split
  · exact guarded_resourceWork_le R H s m T (by assumption)
  · simp [resourceWork, logicalWork, PayloadStats.work]

end UAVProof.TreeBudgetSubtreeResourceSeed
