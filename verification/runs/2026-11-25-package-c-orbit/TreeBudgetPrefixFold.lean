import TreeBudgetInsideJoin

/-!
# Package C (Issue #26) Prototype — Multi-Child Fold Step 1: Prefix Invariant & Preservation

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetInsideJoin` (which transitively imports C0/C1 and C2).

Contents:
1. `PrefixValid`: invariant for a fixed non-root vertex `v`, fixed top-edge counts `q`,
   processed child subset `S ⊆ R.children v`, and child witness family `ns`.
2. Empty prefix (`prefixValid_empty`, `parentState_empty_cost`).
3. Single-insertion preservation (`extendChild_preserves_old`, `prefixValid_insert`,
   `parentState_cost_insert`, `prefixValid_insert_of_transport`).
4. Two-child sequential insertion (`two_child_insert_preserves_first`,
   `two_child_transport_preserves_first`) proving that after inserting the second child,
   the first child's matrix is preserved row-for-row and `w_v * q_i` is counted once.
5. Concrete 4-vertex signed-cost two-child regression (`ex_two_child_hub_regression`).
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

section PrefixInvariant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Prefix invariant for folding children of a non-root vertex `v` under fixed parent
top-edge counts `q`: every processed child in `S` is a child of `v`, carries a valid
subtree matrix with top-edge cap, and satisfies row-by-row parent compatibility. -/
structure PrefixValid (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (ns : V → Fin m → V → ℕ) : Prop where
  sub_children : S ⊆ R.children v
  valid : ∀ w ∈ S, PartialValid R H m w (ns w)
  cap : ∀ w ∈ S, RootChildCap R w (fun i => ns w i w)
  compat : ∀ w ∈ S, ∀ i, 0 < ns w i w → 0 < q i

/-- Empty prefix is vacuously valid for any initial witness map `ns`. -/
theorem prefixValid_empty (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (ns : V → Fin m → V → ℕ) :
    PrefixValid R H v q ∅ ns where
  sub_children := Finset.empty_subset _
  valid := fun _ hw => (Finset.notMem_empty _ hw).elim
  cap := fun _ hw => (Finset.notMem_empty _ hw).elim
  compat := fun _ hw => (Finset.notMem_empty _ hw).elim

/-- On the empty prefix, `parentState` charges `linearWeight R s v * q i` once. -/
theorem parentState_empty_cost (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (ns : V → Fin m → V → ℕ) (i : Fin m) :
    (parentState R s v q ∅ ns).cost i = linearWeight R s v * (q i : ℚ) := by
  simp [parentState]

omit [Fintype V] in
/-- Inserting a fresh child `u ∉ S` leaves every previously processed child's matrix
untouched row-for-row. -/
theorem extendChild_preserves_old {m : ℕ} {S : Finset V} {u w : V}
    (hw : w ∈ S) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ) (nNew : Fin m → V → ℕ) :
    extendChild u ns nNew w = ns w := by
  have hwu : w ≠ u := fun h => huS (h ▸ hw)
  simp [extendChild, hwu]

/-- Inserting a fresh child `u ∉ S` adds `subtreeLinearCost R s u (nNew i)` once and
never duplicates `linearWeight R s v * q i`. -/
theorem parentState_cost_insert (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ) (nNew : Fin m → V → ℕ) (i : Fin m) :
    (parentState R s v q (insert u S) (extendChild u ns nNew)).cost i =
      (parentState R s v q S ns).cost i + subtreeLinearCost R s u (nNew i) := by
  simp only [parentState]
  rw [Finset.sum_insert huS]
  have hrest :
      (∑ w ∈ S, subtreeLinearCost R s w (extendChild u ns nNew w i)) =
        ∑ w ∈ S, subtreeLinearCost R s w (ns w i) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [extendChild_preserves_old hw huS]
  rw [hrest]
  simp only [extendChild, ↓reduceIte]
  ring

/-- Single-insertion preservation of `PrefixValid` under a compatible child permutation `σ`. -/
theorem prefixValid_insert (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V)
    (hu : u ∈ R.children v) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ) (hP : PrefixValid R H v q S ns)
    (nChild : Fin m → V → ℕ) (σ : Equiv.Perm (Fin m))
    (hChildValid : PartialValid R H m u nChild)
    (hChildCap : RootChildCap R u (fun i => nChild i u))
    (hCompat : ∀ i, 0 < reindexMatrix σ nChild i u → 0 < q i) :
    PrefixValid R H v q (insert u S) (extendChild u ns (reindexMatrix σ nChild)) where
  sub_children := Finset.insert_subset_iff.mpr ⟨hu, hP.sub_children⟩
  valid := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hwu | hwS
    · subst hwu
      simp only [extendChild, ↓reduceIte]
      exact partialValid_reindex R H w σ nChild hChildValid
    · rw [extendChild_preserves_old hwS huS]
      exact hP.valid w hwS
  cap := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hwu | hwS
    · subst hwu
      simp only [extendChild, ↓reduceIte]
      exact rootChildCap_reindex R w σ nChild hChildCap
    · rw [extendChild_preserves_old hwS huS]
      exact hP.cap w hwS
  compat := by
    intro w hw i
    rcases Finset.mem_insert.mp hw with hwu | hwS
    · subst hwu
      simp only [extendChild, ↓reduceIte]
      exact hCompat i
    · rw [extendChild_preserves_old hwS huS]
      exact hP.compat w hwS i

/-- Combining `prefixValid_insert` with `inside_join_hist_iff`: any legal transport table
for adding a fresh child `u ∈ R.children v \ S` yields a permutation `σ` preserving
`PrefixValid`, keeping all earlier children's matrices intact, and attaining histogram `h`. -/
theorem prefixValid_insert_of_transport
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V)
    (hu : u ∈ R.children v) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ) (hP : PrefixValid R H v q S ns)
    (nChild : Fin m → V → ℕ) (zChild : CompactState m)
    (hChildValid : PartialValid R H m u nChild)
    (hChildCap : RootChildCap R u (fun i => nChild i u))
    (hChildAct : ∀ i, i ∈ zChild.active ↔ 0 < nChild i u)
    (hChildCost : ∀ i, subtreeLinearCost R s u (nChild i) = zChild.cost i)
    (h : Multiset JointType)
    (hTrans :
      ∃ N : (Finset.univ.image (jointType (parentState R s v q S ns))) →
            (Finset.univ.image (jointType zChild)) → ℕ,
        LegalTable
          (Finset.univ.image (jointType (parentState R s v q S ns)))
          (Finset.univ.image (jointType zChild))
          (jointType (parentState R s v q S ns))
          (jointType zChild)
          K_in N ∧
        tablePushforwardHist N = h) :
    ∃ σ : Equiv.Perm (Fin m),
      PrefixValid R H v q (insert u S) (extendChild u ns (reindexMatrix σ nChild)) ∧
      (∀ w ∈ S, extendChild u ns (reindexMatrix σ nChild) w = ns w) ∧
      jointHist (parentState R s v q (insert u S) (extendChild u ns (reindexMatrix σ nChild))) = h := by
  rcases (inside_join_hist_iff R H s v q S u huS ns nChild zChild
    hChildValid hChildCap hChildAct hChildCost h).mp hTrans
    with ⟨σ, _, _, _, hCompat, hHist⟩
  refine ⟨σ,
    prefixValid_insert R H v q S u hu huS ns hP nChild σ hChildValid hChildCap hCompat,
    fun w hw => extendChild_preserves_old hw huS ns (reindexMatrix σ nChild),
    hHist⟩

end PrefixInvariant

section TwoChildSequential

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sequential insertion of two distinct children `u₁` then `u₂` starting from `∅`:
after inserting `u₂`, the first child `u₁`'s witness matrix is preserved row-for-row,
both children remain valid under `PrefixValid`, and `linearWeight R s v * q i` is counted once. -/
theorem two_child_insert_preserves_first
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (ns₀ : V → Fin m → V → ℕ)
    (u₁ u₂ : V) (hu₁ : u₁ ∈ R.children v) (hu₂ : u₂ ∈ R.children v) (hne : u₂ ≠ u₁)
    (n₁ n₂ : Fin m → V → ℕ) (σ₁ σ₂ : Equiv.Perm (Fin m))
    (hV₁ : PartialValid R H m u₁ n₁) (hC₁ : RootChildCap R u₁ (fun i => n₁ i u₁))
    (hCompat₁ : ∀ i, 0 < reindexMatrix σ₁ n₁ i u₁ → 0 < q i)
    (hV₂ : PartialValid R H m u₂ n₂) (hC₂ : RootChildCap R u₂ (fun i => n₂ i u₂))
    (hCompat₂ : ∀ i, 0 < reindexMatrix σ₂ n₂ i u₂ → 0 < q i) :
    let ns₁ := extendChild u₁ ns₀ (reindexMatrix σ₁ n₁)
    let ns₂ := extendChild u₂ ns₁ (reindexMatrix σ₂ n₂)
    PrefixValid R H v q {u₁} ns₁ ∧
    PrefixValid R H v q {u₂, u₁} ns₂ ∧
    ns₂ u₁ = reindexMatrix σ₁ n₁ ∧
    PartialValid R H m u₁ (ns₂ u₁) ∧
    ns₂ u₂ = reindexMatrix σ₂ n₂ ∧
    ∀ i, (parentState R s v q {u₂, u₁} ns₂).cost i =
      linearWeight R s v * (q i : ℚ) +
      subtreeLinearCost R s u₁ (reindexMatrix σ₁ n₁ i) +
      subtreeLinearCost R s u₂ (reindexMatrix σ₂ n₂ i) := by
  intro ns₁ ns₂
  have hP0 : PrefixValid R H v q ∅ ns₀ := prefixValid_empty R H v q ns₀
  have hP1 : PrefixValid R H v q (insert u₁ ∅) ns₁ :=
    prefixValid_insert R H v q ∅ u₁ hu₁ (Finset.notMem_empty u₁) ns₀ hP0 n₁ σ₁ hV₁ hC₁ hCompat₁
  have hu₂_not_in : u₂ ∉ ({u₁} : Finset V) := by
    simp [hne]
  have hP2 : PrefixValid R H v q (insert u₂ {u₁}) ns₂ :=
    prefixValid_insert R H v q {u₁} u₂ hu₂ hu₂_not_in ns₁ hP1 n₂ σ₂ hV₂ hC₂ hCompat₂
  have hkeep₁ : ns₂ u₁ = reindexMatrix σ₁ n₁ := by
    have h1 : ns₂ u₁ = ns₁ u₁ :=
      extendChild_preserves_old (Finset.mem_singleton_self u₁) hu₂_not_in ns₁ (reindexMatrix σ₂ n₂)
    rw [h1]
    simp [ns₁, extendChild]
  have hkeep₂ : ns₂ u₂ = reindexMatrix σ₂ n₂ := by
    simp [ns₂, extendChild]
  refine ⟨hP1, hP2, hkeep₁, ?_, hkeep₂, ?_⟩
  · exact hP2.valid u₁ (by simp)
  · intro i
    rw [show ({u₂, u₁} : Finset V) = insert u₂ {u₁} from rfl]
    rw [parentState_cost_insert R s v q {u₁} u₂ hu₂_not_in ns₁ (reindexMatrix σ₂ n₂) i]
    rw [show ({u₁} : Finset V) = insert u₁ ∅ from rfl]
    rw [parentState_cost_insert R s v q ∅ u₁ (Finset.notMem_empty u₁) ns₀ (reindexMatrix σ₁ n₁) i]
    rw [parentState_empty_cost]

/-- Concrete two-child sequential insertion regression on a 4-vertex hub tree
(`root = 0`, non-root hub `v = 1`, leaves `u₁ = 2` and `u₂ = 3`, `m = 2`,
signed costs `s = ![0, 2, -5, 3]`, `H = ![0, 2, 1, 1]`, `q = ![1, 1]`).
Child `2` is inserted first with `σ₁ = id`, then child `3` is inserted with `σ₂ = swap 0 1`.
Verifies `PrefixValid`, row-by-row preservation of child `2`, and exact route costs
(`-1` and `7`, with `w_1 * q_i = 2` counted once per route). -/
theorem ex_two_child_hub_regression
    (R : RootedTree (Fin 4))
    (hroot : R.root = 0)
    (hparent : R.parent = ![0, 0, 1, 1]) :
    let s : Fin 4 → ℚ := ![0, 2, -5, 3]
    let H : Fin 4 → ℕ := ![0, 2, 1, 1]
    let q : Fin 2 → ℕ := ![1, 1]
    let n₁ : Fin 2 → Fin 4 → ℕ := fun i x => if x = 2 then (if i = 0 then 1 else 0) else 0
    let n₂ : Fin 2 → Fin 4 → ℕ := fun i x => if x = 3 then (if i = 0 then 1 else 0) else 0
    let ns₀ : Fin 4 → Fin 2 → Fin 4 → ℕ := fun _ _ _ => 0
    let σ₁ : Equiv.Perm (Fin 2) := Equiv.refl (Fin 2)
    let σ₂ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
    let ns₁ := extendChild (2 : Fin 4) ns₀ (reindexMatrix σ₁ n₁)
    let ns₂ := extendChild (3 : Fin 4) ns₁ (reindexMatrix σ₂ n₂)
    PrefixValid R H 1 q {2} ns₁ ∧
    PrefixValid R H 1 q {3, 2} ns₂ ∧
    ns₂ 2 = ns₁ 2 ∧
    (parentState R s 1 q {3, 2} ns₂).cost 0 = -1 ∧
    (parentState R s 1 q {3, 2} ns₂).cost 1 = 7 := by
  intro s H q n₁ n₂ ns₀ σ₁ σ₂ ns₁ ns₂
  have h2_ch : (2 : Fin 4) ∈ R.children 1 := by
    rw [R.mem_children, hroot, hparent]
    decide
  have h3_ch : (3 : Fin 4) ∈ R.children 1 := by
    rw [R.mem_children, hroot, hparent]
    decide
  have hsub2 : ∀ x : Fin 4, InSubtree R 2 x ↔ x = 2 := by
    intro x
    constructor
    · intro hx
      cases hx with
      | self => rfl
      | step hy hp =>
        have hrank : R.rank (R.parent x) ≤ R.rank 2 := hp.rank_le
        have h2rank : R.rank 2 < R.rank 1 := by
          have := R.parent_rank 2 (by rw [hroot]; decide)
          simpa [hparent] using this
        have h1rank : R.rank 1 < R.rank 0 := by
          have := R.parent_rank 1 (by rw [hroot]; decide)
          simpa [hparent] using this
        fin_cases x
        · exact (hy hroot.symm).elim
        · rw [hparent] at hrank; simp at hrank; omega
        · rw [hparent] at hrank; simp at hrank; omega
        · rw [hparent] at hrank; simp at hrank; omega
    · rintro rfl; exact .self
  have hsub3 : ∀ x : Fin 4, InSubtree R 3 x ↔ x = 3 := by
    intro x
    constructor
    · intro hx
      cases hx with
      | self => rfl
      | step hy hp =>
        have hrank : R.rank (R.parent x) ≤ R.rank 3 := hp.rank_le
        have h3rank : R.rank 3 < R.rank 1 := by
          have := R.parent_rank 3 (by rw [hroot]; decide)
          simpa [hparent] using this
        have h1rank : R.rank 1 < R.rank 0 := by
          have := R.parent_rank 1 (by rw [hroot]; decide)
          simpa [hparent] using this
        fin_cases x
        · exact (hy hroot.symm).elim
        · rw [hparent] at hrank; simp at hrank; omega
        · rw [hparent] at hrank; simp at hrank; omega
        · rw [hparent] at hrank; simp at hrank; omega
    · rintro rfl; exact .self
  have hV₁ : PartialValid R H 2 2 n₁ := by
    constructor
    · intro i x hx
      have hne : x ≠ 2 := fun h => hx ((hsub2 x).mpr h)
      simp [n₁, hne]
    · intro x hx
      have hx2 : x = 2 := (hsub2 x).mp hx
      subst hx2
      simp [n₁, H]
    · intro i x hx hne _
      exact (hne ((hsub2 x).mp hx)).elim
  have hV₂ : PartialValid R H 2 3 n₂ := by
    constructor
    · intro i x hx
      have hne : x ≠ 3 := fun h => hx ((hsub3 x).mpr h)
      simp [n₂, hne]
    · intro x hx
      have hx3 : x = 3 := (hsub3 x).mp hx
      subst hx3
      simp [n₂, H]
    · intro i x hx hne _
      exact (hne ((hsub3 x).mp hx)).elim
  have hC₁ : RootChildCap R 2 (fun i => n₁ i 2) := by
    intro hr
    rw [hroot, hparent] at hr
    exact absurd hr (by decide)
  have hC₂ : RootChildCap R 3 (fun i => n₂ i 3) := by
    intro hr
    rw [hroot, hparent] at hr
    exact absurd hr (by decide)
  have hCompat₁ : ∀ i, 0 < reindexMatrix σ₁ n₁ i 2 → 0 < q i := by
    intro i _; fin_cases i <;> decide
  have hCompat₂ : ∀ i, 0 < reindexMatrix σ₂ n₂ i 3 → 0 < q i := by
    intro i _; fin_cases i <;> decide
  have hmain := two_child_insert_preserves_first R H s 1 q ns₀ 2 3 h2_ch h3_ch (by decide)
    n₁ n₂ σ₁ σ₂ hV₁ hC₁ hCompat₁ hV₂ hC₂ hCompat₂
  rcases hmain with ⟨hP1, hP2, hkeep₁, _, _, hcost⟩
  have hsub2_eq : subtree R 2 = {2} := by
    ext x; simp [mem_subtree, hsub2]
  have hsub3_eq : subtree R 3 = {3} := by
    ext x; simp [mem_subtree, hsub3]
  have hw1 : linearWeight R s 1 = 2 := by
    simp [linearWeight, parentCharge, hroot, hparent, s]
  have hw2 : linearWeight R s 2 = -3 := by
    simp [linearWeight, parentCharge, hroot, hparent, s]
    norm_num
  have hw3 : linearWeight R s 3 = 5 := by
    simp [linearWeight, parentCharge, hroot, hparent, s]
    norm_num
  refine ⟨hP1, hP2, ?_, ?_, ?_⟩
  · dsimp only [ns₂, ns₁]
    rw [hkeep₁]
    simp [extendChild]
  · rw [hcost 0, hw1, subtreeLinearCost, hsub2_eq, subtreeLinearCost, hsub3_eq]
    simp only [Finset.sum_singleton, hw2, hw3, q, reindexMatrix, σ₁, σ₂, n₁, n₂,
      Equiv.refl_apply, Equiv.swap_apply_left]
    norm_num
  · rw [hcost 1, hw1, subtreeLinearCost, hsub2_eq, subtreeLinearCost, hsub3_eq]
    simp only [Finset.sum_singleton, hw2, hw3, q, reindexMatrix, σ₁, σ₂, n₁, n₂,
      Equiv.refl_apply, Equiv.swap_apply_right]
    norm_num

end TwoChildSequential

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixValid_empty
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixValid_insert
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixValid_insert_of_transport
#print axioms UAVProof.TreeBudgetOrbitPrototype.two_child_insert_preserves_first
#print axioms UAVProof.TreeBudgetOrbitPrototype.ex_two_child_hub_regression
