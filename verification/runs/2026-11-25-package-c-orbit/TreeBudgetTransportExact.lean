import LeanCompletion.UAV.TreeBudgetSubtreeCompact

/-!
# Package C (Issue #26) Prototype — C2: Exact Transport-Table Realization

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Read-only imports from `LeanCompletion.UAV.TreeBudgetSubtreeCompact`.

Proves `transport_realize_exact : TransportRealizeExactSpec` in two steps:
1. `legalTable_of_perm`: any compatible permutation `σ : Equiv.Perm (Fin m)` induces a
   `LegalTable` (row sums, column sums, and zero forbidden cells).
2. `exists_perm_of_legalTable`: any `LegalTable` is realized simultaneously on every cell
   by a single permutation `σ : Equiv.Perm (Fin m)` constructed via explicit cell slots
   `Σ a : A, Σ b : B, Fin (N a b)`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

section TransportDefs

/-- Cell counts induced by a permutation `σ : Equiv.Perm (Fin m)` on `x, y : Fin m → J`. -/
noncomputable def inducedTable {m : ℕ} {J : Type*} [DecidableEq J]
    (x y : Fin m → J) (σ : Equiv.Perm (Fin m)) (a b : J) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m)).filter (fun i => x i = a ∧ y (σ i) = b)).card

/-- Legality of a finitely supported transport table `N : A → B → ℕ` over the active
left/right type supports `A, B : Finset J` with compatibility predicate `K`. -/
def LegalTable {m : ℕ} {J : Type*} [DecidableEq J]
    (A B : Finset J) (x y : Fin m → J) (K : J → J → Prop) (N : A → B → ℕ) : Prop :=
  (∀ i, x i ∈ A) ∧
  (∀ j, y j ∈ B) ∧
  (∀ a : A, (∑ b : B, N a b) = ((Finset.univ : Finset (Fin m)).filter (fun i => x i = a.1)).card) ∧
  (∀ b : B, (∑ a : A, N a b) = ((Finset.univ : Finset (Fin m)).filter (fun j => y j = b.1)).card) ∧
  (∀ (a : A) (b : B), ¬ K a.1 b.1 → N a b = 0)

/-- Target specification for C2 (`transport_realize_exact`), matching the C0/C1 prototype. -/
def TransportRealizeExactSpec : Prop :=
  ∀ {m : ℕ} {J : Type*} [DecidableEq J]
    (A B : Finset J) (x y : Fin m → J) (K : J → J → Prop) (N : A → B → ℕ),
    LegalTable A B x y K N ↔
      (∀ i, x i ∈ A) ∧ (∀ j, y j ∈ B) ∧
      ∃ σ : Equiv.Perm (Fin m),
        (∀ i, K (x i) (y (σ i))) ∧
        ∀ (a : A) (b : B), inducedTable x y σ a.1 b.1 = N a b

end TransportDefs

section Step1PermToTable

/-- Step 1: Any compatible permutation `σ` induces a `LegalTable` with cell counts
`inducedTable x y σ`. -/
theorem legalTable_of_perm {m : ℕ} {J : Type*} [DecidableEq J]
    (A B : Finset J) (x y : Fin m → J) (K : J → J → Prop)
    (hxA : ∀ i, x i ∈ A) (hyB : ∀ j, y j ∈ B)
    (σ : Equiv.Perm (Fin m)) (hK : ∀ i, K (x i) (y (σ i))) :
    LegalTable A B x y K (fun a b => inducedTable x y σ a.1 b.1) := by
  classical
  refine ⟨hxA, hyB, ?_, ?_, ?_⟩
  · intro a
    let S : Finset (Fin m) := Finset.univ.filter (fun i => x i = a.1)
    have hsum :
        (∑ b : B, (S.filter (fun i => (⟨y (σ i), hyB (σ i)⟩ : B) = b)).card) = S.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise
        (f := fun i : Fin m => (⟨y (σ i), hyB (σ i)⟩ : B))
        (fun _ _ => Finset.mem_univ _)
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro b _
    unfold inducedTable
    apply congrArg Finset.card
    ext i
    simp [S, Subtype.ext_iff]
  · intro b
    let T : Finset (Fin m) := Finset.univ.filter (fun i => y (σ i) = b.1)
    have hsum :
        (∑ a : A, (T.filter (fun i => (⟨x i, hxA i⟩ : A) = a)).card) = T.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise
        (f := fun i : Fin m => (⟨x i, hxA i⟩ : A))
        (fun _ _ => Finset.mem_univ _)
    have hTcard : T.card = (Finset.univ.filter (fun j : Fin m => y j = b.1)).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      refine Fintype.card_congr
        { toFun := fun ⟨i, hi⟩ => ⟨σ i, hi⟩
          invFun := fun ⟨j, hj⟩ => ⟨σ.symm j, by simpa using hj⟩
          left_inv := fun ⟨i, _⟩ => by ext; simp
          right_inv := fun ⟨j, _⟩ => by ext; simp }
    rw [← hTcard, ← hsum]
    apply Finset.sum_congr rfl
    intro a _
    unfold inducedTable
    apply congrArg Finset.card
    ext i
    simp [T, Subtype.ext_iff, and_comm]
  · intro a b hnotK
    unfold inducedTable
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro i _ ⟨hxi, hyi⟩
    have hKi : K a.1 b.1 := by
      rw [← hxi, ← hyi]
      exact hK i
    exact hnotK hKi

end Step1PermToTable

section Step2TableToPerm

/-- Explicit slot swap between `(b, a, k)` and `(a, b, k)`. -/
def slotSwap {A B : Type*} {N : A → B → ℕ} :
    (Σ b : B, Σ a : A, Fin (N a b)) ≃ (Σ a : A, Σ b : B, Fin (N a b)) where
  toFun := fun ⟨b, a, k⟩ => ⟨a, b, k⟩
  invFun := fun ⟨a, b, k⟩ => ⟨b, a, k⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- Step 2: Any `LegalTable` is realized simultaneously on every cell by a single
permutation `σ : Equiv.Perm (Fin m)` constructed through cell slots `(a, b, k)`. -/
theorem exists_perm_of_legalTable {m : ℕ} {J : Type*} [DecidableEq J]
    (A B : Finset J) (x y : Fin m → J) (K : J → J → Prop) (N : A → B → ℕ)
    (hL : LegalTable A B x y K N) :
    ∃ σ : Equiv.Perm (Fin m),
      (∀ i, K (x i) (y (σ i))) ∧
      ∀ (a : A) (b : B), inducedTable x y σ a.1 b.1 = N a b := by
  classical
  rcases hL with ⟨hxA, hyB, hrow, hcol, hforb⟩
  let xA : Fin m → A := fun i => ⟨x i, hxA i⟩
  let yB : Fin m → B := fun j => ⟨y j, hyB j⟩
  -- Left fiber equivalences: `{i // xA i = a} ≃ Σ b : B, Fin (N a b)`
  have hcardL : ∀ a : A,
      Fintype.card {i : Fin m // xA i = a} = Fintype.card (Σ b : B, Fin (N a b)) := by
    intro a
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [hrow a, ← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun ⟨i, hi⟩ => ⟨i, congrArg Subtype.val hi⟩
        invFun := fun ⟨i, hi⟩ => ⟨i, Subtype.ext hi⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  let eLa : ∀ a : A, {i : Fin m // xA i = a} ≃ (Σ b : B, Fin (N a b)) :=
    fun a => Fintype.equivOfCardEq (hcardL a)
  let eL : Fin m ≃ (Σ a : A, Σ b : B, Fin (N a b)) :=
    (Equiv.sigmaFiberEquiv xA).symm.trans (Equiv.sigmaCongrRight eLa)
  -- Right fiber equivalences: `{j // yB j = b} ≃ Σ a : A, Fin (N a b)`
  have hcardR : ∀ b : B,
      Fintype.card {j : Fin m // yB j = b} = Fintype.card (Σ a : A, Fin (N a b)) := by
    intro b
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [hcol b, ← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun ⟨j, hj⟩ => ⟨j, congrArg Subtype.val hj⟩
        invFun := fun ⟨j, hj⟩ => ⟨j, Subtype.ext hj⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  let eRb : ∀ b : B, {j : Fin m // yB j = b} ≃ (Σ a : A, Fin (N a b)) :=
    fun b => Fintype.equivOfCardEq (hcardR b)
  let eR : Fin m ≃ (Σ a : A, Σ b : B, Fin (N a b)) :=
    (Equiv.sigmaFiberEquiv yB).symm.trans ((Equiv.sigmaCongrRight eRb).trans slotSwap)
  -- Coordinate preservation of `eL` and `eR`
  have heL_fst : ∀ i : Fin m, (eL i).1 = xA i := fun _ => rfl
  have heR_snd : ∀ j : Fin m, (eR j).2.1 = yB j := fun _ => rfl
  -- Global permutation pairing matching `(a, b, k)` slots
  let σ : Equiv.Perm (Fin m) := eL.trans eR.symm
  have heR_σ : ∀ i : Fin m, eR (σ i) = eL i := fun i => eR.apply_symm_apply (eL i)
  have hx_eq : ∀ i : Fin m, x i = (eL i).1.1 := fun i => (congrArg Subtype.val (heL_fst i)).symm
  have hy_eq : ∀ i : Fin m, y (σ i) = (eL i).2.1.1 := by
    intro i
    have h1 : yB (σ i) = (eL i).2.1 := (heR_snd (σ i)).symm.trans (congrArg (fun s => s.2.1) (heR_σ i))
    exact congrArg Subtype.val h1
  refine ⟨σ, ?_, ?_⟩
  · intro i
    rw [hx_eq i, hy_eq i]
    by_contra hnotK
    have hzero : N (eL i).1 (eL i).2.1 = 0 := hforb (eL i).1 (eL i).2.1 hnotK
    exact Nat.not_lt_zero (eL i).2.2.1 (hzero ▸ (eL i).2.2.2)
  · intro a b
    unfold inducedTable
    rw [← Fintype.card_subtype, ← Fintype.card_fin (N a b)]
    let f : Fin (N a b) → {i : Fin m // x i = a.1 ∧ y (σ i) = b.1} := fun k =>
      ⟨eL.symm ⟨a, b, k⟩,
        by
          constructor
          · rw [hx_eq, eL.apply_symm_apply]
          · rw [hy_eq, eL.apply_symm_apply]⟩
    have hf_bij : Function.Bijective f := by
      constructor
      · intro k₁ k₂ hk
        have hsymm : eL.symm ⟨a, b, k₁⟩ = eL.symm ⟨a, b, k₂⟩ := Subtype.mk.inj hk
        have hsig : (⟨a, b, k₁⟩ : Σ a : A, Σ b : B, Fin (N a b)) = ⟨a, b, k₂⟩ :=
          eL.symm.injective hsymm
        have h2 : (⟨b, k₁⟩ : Σ b : B, Fin (N a b)) = ⟨b, k₂⟩ := eq_of_heq (Sigma.mk.inj hsig).2
        exact eq_of_heq (Sigma.mk.inj h2).2
      · rintro ⟨i, hxi, hyi⟩
        cases h : eL i with
        | mk a' rest =>
          cases rest with
          | mk b' k =>
            have ha' : a' = a := by
              apply Subtype.ext
              have := hx_eq i
              rw [h] at this
              exact this.symm.trans hxi
            have hb' : b' = b := by
              apply Subtype.ext
              have := hy_eq i
              rw [h] at this
              exact this.symm.trans hyi
            subst ha'
            subst hb'
            refine ⟨k, Subtype.ext ?_⟩
            dsimp [f]
            rw [← h, eL.symm_apply_apply]
    exact (Fintype.card_congr (Equiv.ofBijective f hf_bij)).symm

/-- C2 Main Theorem: exact characterization of legal transport tables via single
route permutations realizing every cell count simultaneously. -/
theorem transport_realize_exact : TransportRealizeExactSpec := by
  intro m J _ A B x y K N
  constructor
  · intro hL
    exact ⟨hL.1, hL.2.1, exists_perm_of_legalTable A B x y K N hL⟩
  · rintro ⟨hxA, hyB, σ, hK, hN⟩
    have hLeg := legalTable_of_perm A B x y K hxA hyB σ hK
    have hEq : (fun a b => inducedTable x y σ a.1 b.1) = N := by
      funext a b
      exact hN a b
    simpa only [hEq] using hLeg

end Step2TableToPerm

section RegressionExamples

/-! ### Regression 1: `x = y = (false, false, true, true)` with all-ones `2 × 2` table
Forces the two identical left `false` routes to split across right `false` and right `true`. -/

def ex_split_S : Finset Bool := Finset.univ
def ex_split_x : Fin 4 → Bool := ![false, false, true, true]
def ex_split_N : ex_split_S → ex_split_S → ℕ := fun _ _ => 1

theorem ex_split_legal :
    LegalTable ex_split_S ex_split_S
      ex_split_x ex_split_x (fun _ _ => True) ex_split_N := by
  refine ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro a
    rcases a with ⟨a, _⟩
    cases a <;> decide +revert
  · intro b
    rcases b with ⟨b, _⟩
    cases b <;> decide +revert
  · intro _ _ h
    exact (h trivial).elim

theorem ex_split_exists_perm :
    ∃ σ : Equiv.Perm (Fin 4),
      (∀ _ : Fin 4, True) ∧
      ∀ (a b : ex_split_S),
        inducedTable ex_split_x ex_split_x σ a.1 b.1 = 1 :=
  ((transport_realize_exact ex_split_S ex_split_S ex_split_x ex_split_x
    (fun _ _ => True) ex_split_N).mp ex_split_legal).2.2

/-- Any realizing permutation must split the two repeated `false` routes across distinct
right types (`false` and `true`), ruling out block-copying of repeated types. -/
theorem ex_split_breaks_repeated_block :
    ∃ σ : Equiv.Perm (Fin 4),
      ∃ i j : Fin 4,
        ex_split_x i = false ∧ ex_split_x j = false ∧
        ex_split_x (σ i) ≠ ex_split_x (σ j) := by
  classical
  rcases ex_split_exists_perm with ⟨σ, _, hcell⟩
  have hff : (Finset.univ.filter (fun i : Fin 4 =>
      ex_split_x i = false ∧ ex_split_x (σ i) = false)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 := hcell ⟨false, Finset.mem_univ _⟩ ⟨false, Finset.mem_univ _⟩
    unfold inducedTable at h0
    simp [hemp] at h0
  have hft : (Finset.univ.filter (fun i : Fin 4 =>
      ex_split_x i = false ∧ ex_split_x (σ i) = true)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 := hcell ⟨false, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩
    unfold inducedTable at h0
    simp [hemp] at h0
  rcases hff with ⟨i, hi⟩
  rcases hft with ⟨j, hj⟩
  rw [Finset.mem_filter] at hi hj
  exact ⟨σ, i, j, hi.2.1, hj.2.1, by rw [hi.2.2, hj.2.2]; decide⟩

/-! ### Regression 2: `m = 0` empty route set -/

theorem ex_m_zero_transport {J : Type*} [DecidableEq J]
    (K : J → J → Prop) (N : (∅ : Finset J) → (∅ : Finset J) → ℕ) :
    ∃ σ : Equiv.Perm (Fin 0),
      (∀ i, K (Fin.elim0 i) (Fin.elim0 (σ i))) ∧
      ∀ (a b : (∅ : Finset J)), inducedTable Fin.elim0 Fin.elim0 σ a.1 b.1 = N a b := by
  have hLeg : LegalTable (∅ : Finset J) (∅ : Finset J) Fin.elim0 Fin.elim0 K N := by
    refine ⟨fun i => Fin.elim0 i, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
    · intro a; exact (Finset.notMem_empty a.1 a.2).elim
    · intro b; exact (Finset.notMem_empty b.1 b.2).elim
    · intro a; exact (Finset.notMem_empty a.1 a.2).elim
  exact ((transport_realize_exact ∅ ∅ Fin.elim0 Fin.elim0 K N).mp hLeg).2.2

/-! ### Regression 3: Internal compatibility `K_in` with forbidden cell and negative costs -/

def K_in (a b : Bool × ℚ) : Prop := b.1 = true → a.1 = true

def exC2_tT : Bool × ℚ := (true, (-3 : ℚ) / 2)
def exC2_tF : Bool × ℚ := (false, (1 : ℚ) / 2)
def exC2_A : Finset (Bool × ℚ) := {exC2_tT, exC2_tF}
def exC2_x : Fin 2 → Bool × ℚ := ![exC2_tF, exC2_tT]
def exC2_y : Fin 2 → Bool × ℚ := ![exC2_tT, exC2_tF]

/-- Only `(exC2_tT, exC2_tT)` and `(exC2_tF, exC2_tF)` get weight 1; the forbidden cell
`(exC2_tF, exC2_tT)` has weight 0. -/
def exC2_N (a b : exC2_A) : ℕ := if a = b then 1 else 0

theorem exC2_forbidden_realizable :
    ∃ σ : Equiv.Perm (Fin 2),
      (∀ i, K_in (exC2_x i) (exC2_y (σ i))) ∧
      ∀ (a b : exC2_A), inducedTable exC2_x exC2_y σ a.1 b.1 = exC2_N a b := by
  have hLeg : LegalTable exC2_A exC2_A exC2_x exC2_y K_in exC2_N := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [exC2_A, exC2_x]
    · intro j; fin_cases j <;> simp [exC2_A, exC2_y]
    · intro a
      have hL : (∑ b : exC2_A, exC2_N a b) = 1 := by simp [exC2_N]
      rw [hL]
      rcases a with ⟨a, ha⟩
      simp only [exC2_A, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · symm; exact Finset.card_eq_one.mpr ⟨1, by ext i; fin_cases i <;> simp [exC2_x, exC2_tT, exC2_tF]⟩
      · symm; exact Finset.card_eq_one.mpr ⟨0, by ext i; fin_cases i <;> simp [exC2_x, exC2_tT, exC2_tF]⟩
    · intro b
      have hR : (∑ a : exC2_A, exC2_N a b) = 1 := by simp [exC2_N]
      rw [hR]
      rcases b with ⟨b, hb⟩
      simp only [exC2_A, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · symm; exact Finset.card_eq_one.mpr ⟨0, by ext j; fin_cases j <;> simp [exC2_y, exC2_tT, exC2_tF]⟩
      · symm; exact Finset.card_eq_one.mpr ⟨1, by ext j; fin_cases j <;> simp [exC2_y, exC2_tT, exC2_tF]⟩
    · intro a b hnotK
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only [exC2_A, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exfalso; exact hnotK (fun _ => rfl)
      · simp [exC2_N, exC2_tT, exC2_tF]
      · simp [exC2_N, exC2_tT, exC2_tF]
      · exfalso; exact hnotK (fun h => by simp [exC2_tF] at h)
  exact ((transport_realize_exact exC2_A exC2_A exC2_x exC2_y K_in exC2_N).mp hLeg).2.2

end RegressionExamples

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.legalTable_of_perm
#print axioms UAVProof.TreeBudgetOrbitPrototype.exists_perm_of_legalTable
#print axioms UAVProof.TreeBudgetOrbitPrototype.transport_realize_exact
