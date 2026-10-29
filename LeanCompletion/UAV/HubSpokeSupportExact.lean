import LeanCompletion.UAV.SupportExactFeasibility

/-!
# A strict hub-spoke positive baseline

New proof candidate; compilation and axiom reports are pending.
The first section proves uniqueness for any loop-free flow whose positive
edges all touch a fixed hub. The second constructs the canonical strict
depot/hub/satellite instance, including its degrees and zero-demand cases.
This is a conditional equivalence, not an existence or packing theorem.
-/

namespace UAVProof.HubSpokeSupportExact

open SupportExactFeasibility

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every non-hub vertex has only the hub as a possible successor. -/
theorem outFlow_eq_hub_entry
    (hub : V) (z : V → V → ℕ)
    (hzero : ∀ i j, i ≠ hub → j ≠ hub → z i j = 0)
    (i : V) (hi : i ≠ hub) :
    outFlow Finset.univ z i = z i hub := by
  unfold outFlow
  apply Finset.sum_eq_single hub
  · intro j _ hj
    exact hzero i j hi hj
  · intro h
    exact (h (Finset.mem_univ hub)).elim

/-- Every non-hub vertex has only the hub as a possible predecessor. -/
theorem inFlow_eq_hub_entry
    (hub : V) (z : V → V → ℕ)
    (hzero : ∀ i j, i ≠ hub → j ≠ hub → z i j = 0)
    (j : V) (hj : j ≠ hub) :
    inFlow Finset.univ z j = z hub j := by
  unfold inFlow
  apply Finset.sum_eq_single hub
  · intro i _ hi
    exact hzero i j hi hj
  · intro h
    exact (h (Finset.mem_univ hub)).elim

/-- Support and prescribed degrees determine all edge multiplicities.
Only the hub self-loop needs a separate zero assumption; all other loops
are excluded by hshape. The depot may be any vertex in this generic lemma. -/
theorem hub_support_determines_flow
    (depot hub : V) (d : V → ℕ) (m : ℕ) (x : V → V → ℕ)
    (hdegrees : HasDegrees depot d m x)
    (hloop : x hub hub = 0)
    (hshape : ∀ i j, i ≠ hub → j ≠ hub → x i j = 0) :
    SupportDeterminesFlow depot d m x := by
  intro z hsupport hzdegrees
  have hzshape : ∀ i j, i ≠ hub → j ≠ hub → z i j = 0 := by
    intro i j hi hj
    exact hsupport i j (hshape i j hi hj)
  have hzloop : z hub hub = 0 := hsupport hub hub hloop
  funext i j
  by_cases hi : i = hub
  · subst i
    by_cases hj : j = hub
    · subst j
      exact hzloop.trans hloop.symm
    · calc
        z hub j = inFlow Finset.univ z j :=
          (inFlow_eq_hub_entry hub z hzshape j hj).symm
        _ = prescribedDegree depot d m j := hzdegrees.2 j
        _ = inFlow Finset.univ x j := (hdegrees.2 j).symm
        _ = x hub j := inFlow_eq_hub_entry hub x hshape j hj
  · by_cases hj : j = hub
    · subst j
      calc
        z i hub = outFlow Finset.univ z i :=
          (outFlow_eq_hub_entry hub z hzshape i hi).symm
        _ = prescribedDegree depot d m i := hzdegrees.1 i
        _ = outFlow Finset.univ x i := (hdegrees.1 i).symm
        _ = x i hub := outFlow_eq_hub_entry hub x hshape i hi
    · exact (hzshape i j hi hj).trans (hshape i j hi hj).symm

theorem hub_support_iff_exact
    (depot hub : V) (d : V → ℕ) (m : ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hdegrees : HasDegrees depot d m x)
    (hloop : x hub hub = 0)
    (hshape : ∀ i j, i ≠ hub → j ≠ hub → x i j = 0) :
    SupportFeasible depot x d m service T ↔
      ExactFeasible depot x d m service T := by
  exact support_iff_exact_of_unique depot x d m service T
    (hub_support_determines_flow depot hub d m x hdegrees hloop hshape)

end General

section Canonical

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- none = depot; some none = hub; some (some b) = satellite b. -/
abbrev Node (B : Type*) := Option (Option B)

def depot : Node B := none
def hub : Node B := some none
def satellite (b : B) : Node B := some (some b)

/-- Coverage forces the hub demand m + sum d_b. -/
def required (m : ℕ) (d : B → ℕ) : Node B → ℕ
  | none => 0
  | some none => m + ∑ b, d b
  | some (some b) => d b

/-- The canonical flow; zero demand simply deletes the corresponding spoke. -/
def canonicalFlow (m : ℕ) (d : B → ℕ) : Node B → Node B → ℕ
  | none, some none => m
  | some none, none => m
  | some none, some (some b) => d b
  | some (some b), some none => d b
  | _, _ => 0

theorem canonicalFlow_depot_hub (m : ℕ) (d : B → ℕ) :
    canonicalFlow m d (depot : Node B) hub = m ∧
    canonicalFlow m d hub (depot : Node B) = m := by
  exact ⟨rfl, rfl⟩

theorem canonicalFlow_hub_satellite (m : ℕ) (d : B → ℕ) (b : B) :
    canonicalFlow m d hub (satellite b) = d b ∧
    canonicalFlow m d (satellite b) hub = d b := by
  exact ⟨rfl, rfl⟩

theorem canonicalFlow_no_loops (m : ℕ) (d : B → ℕ) :
    ∀ v : Node B, canonicalFlow m d v v = 0 := by
  intro v
  cases v with
  | none => rfl
  | some v =>
    cases v with
    | none => rfl
    | some b => rfl

theorem canonicalFlow_shape (m : ℕ) (d : B → ℕ) :
    ∀ i j : Node B, i ≠ hub → j ≠ hub → canonicalFlow m d i j = 0 := by
  intro i j hi hj
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      cases j with
      | none => exact (hj rfl).elim
      | some b => rfl
  | some i =>
    cases i with
    | none => exact (hi rfl).elim
    | some b =>
      cases j with
      | none => rfl
      | some j =>
        cases j with
        | none => exact (hj rfl).elim
        | some c => rfl

/-- Direct degree calculation, not an assumption of feasibility. -/
theorem canonicalFlow_has_degrees (m : ℕ) (d : B → ℕ) :
    HasDegrees (depot : Node B) (required m d) m (canonicalFlow m d) := by
  constructor
  · intro v
    cases v with
    | none =>
      simp [outFlow, prescribedDegree, depot, required, canonicalFlow,
        Fintype.sum_option]
    | some v =>
      cases v with
      | none =>
        simp [outFlow, prescribedDegree, depot, required, canonicalFlow,
          Fintype.sum_option]
      | some b =>
        simp [outFlow, prescribedDegree, depot, required, canonicalFlow,
          Fintype.sum_option]
  · intro v
    cases v with
    | none =>
      simp [inFlow, prescribedDegree, depot, required, canonicalFlow,
        Fintype.sum_option]
    | some v =>
      cases v with
      | none =>
        simp [inFlow, prescribedDegree, depot, required, canonicalFlow,
          Fintype.sum_option]
      | some b =>
        simp [inFlow, prescribedDegree, depot, required, canonicalFlow,
          Fintype.sum_option]

theorem canonical_support_determines_flow (m : ℕ) (d : B → ℕ) :
    SupportDeterminesFlow (depot : Node B) (required m d) m
      (canonicalFlow m d) := by
  exact hub_support_determines_flow depot hub (required m d) m
    (canonicalFlow m d) (canonicalFlow_has_degrees m d)
    (canonicalFlow_no_loops m d hub) (canonicalFlow_shape m d)

/-- Main strict-hub instance. This does NOT assert that either side holds. -/
theorem strict_hub_support_iff_exact
    (m : ℕ) (d : B → ℕ) (service : Node B → ℚ) (T : ℚ) :
    SupportFeasible depot (canonicalFlow m d) (required m d) m service T ↔
      ExactFeasible depot (canonicalFlow m d) (required m d) m service T := by
  exact support_iff_exact_of_unique depot (canonicalFlow m d)
    (required m d) m service T (canonical_support_determines_flow m d)

end Canonical

end UAVProof.HubSpokeSupportExact

#print axioms UAVProof.HubSpokeSupportExact.outFlow_eq_hub_entry
#print axioms UAVProof.HubSpokeSupportExact.inFlow_eq_hub_entry
#print axioms UAVProof.HubSpokeSupportExact.hub_support_determines_flow
#print axioms UAVProof.HubSpokeSupportExact.hub_support_iff_exact
#print axioms UAVProof.HubSpokeSupportExact.canonicalFlow_depot_hub
#print axioms UAVProof.HubSpokeSupportExact.canonicalFlow_hub_satellite
#print axioms UAVProof.HubSpokeSupportExact.canonicalFlow_no_loops
#print axioms UAVProof.HubSpokeSupportExact.canonicalFlow_shape
#print axioms UAVProof.HubSpokeSupportExact.canonicalFlow_has_degrees
#print axioms UAVProof.HubSpokeSupportExact.canonical_support_determines_flow
#print axioms UAVProof.HubSpokeSupportExact.strict_hub_support_iff_exact
