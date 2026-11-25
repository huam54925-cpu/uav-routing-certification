import TreeBudgetOrbitPrototype
import TreeBudgetTransportExact

/-!
# Package C (Issue #26) Prototype — C3: Single-Child Witnessed Inside Join

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports C0/C1 (`TreeBudgetOrbitPrototype`) and C2 (`TreeBudgetTransportExact`)
from their single-source declarations with zero duplication.

Contents:
1. `#check` of both `compactRep_reindex` (C0) and `transport_realize_exact` (C2).
2. Pushforward histogram counting formula (`count_merged_eq_sum_table`,
   `merged_hist_eq_tablePushforwardHist`) for `g_in (a, b) = (a.1, a.2 + b.2)`,
   plus the `0 + 1` / `1 + 0` merging example (output multiplicity `2`).
3. Single-child witnessed inside join theorem (`inside_join_hist_iff`), keeping parent
   top-edge counts `q` and already-processed children `S` fixed (`w_v * q_i` counted once).
4. Four targeted regression examples: output-type merging, parent-child forbidden
   pairing (`K_in`), negative rational cost addition, and `m = 0`.
-/

#check UAVProof.TreeBudgetOrbitPrototype.compactRep_reindex
#check UAVProof.TreeBudgetOrbitPrototype.transport_realize_exact

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

section PushforwardHistogram

/-- Internal join combination rule: preserve parent activity and add signed linear costs. -/
def g_in (a b : JointType) : JointType :=
  (a.1, a.2 + b.2)

/-- Pushforward multiset of a finitely supported transport table `N : A → B → ℕ` under `g_in`. -/
noncomputable def tablePushforwardHist {A B : Finset JointType}
    (N : A → B → ℕ) : Multiset JointType :=
  ∑ a : A, ∑ b : B, Multiset.replicate (N a b) (g_in a.1 b.1)

/-- Exact multiplicity of any target type `t` in `tablePushforwardHist N`. -/
theorem count_tablePushforwardHist {A B : Finset JointType}
    (N : A → B → ℕ) (t : JointType) :
    Multiset.count t (tablePushforwardHist N) =
      ∑ a : A, ∑ b : B, if g_in a.1 b.1 = t then N a b else 0 := by
  classical
  unfold tablePushforwardHist
  rw [Multiset.count_sum']
  apply Finset.sum_congr rfl
  intro a _
  rw [Multiset.count_sum']
  apply Finset.sum_congr rfl
  intro b _
  rw [Multiset.count_replicate]

/-- Step 2: If a permutation `σ` realizes every cell count of `N`, then the output
histogram of `fun i => g_in (x i) (y (σ i))` has multiplicity at `t` equal to the
sum of `N a b` over all cells `(a, b)` with `g_in a b = t`. -/
theorem count_merged_eq_sum_table
    {m : ℕ} (A B : Finset JointType) (x y : Fin m → JointType)
    (σ : Equiv.Perm (Fin m)) (N : A → B → ℕ)
    (hxA : ∀ i, x i ∈ A) (hyB : ∀ j, y j ∈ B)
    (hN : ∀ (a : A) (b : B), inducedTable x y σ a.1 b.1 = N a b)
    (t : JointType) :
    Multiset.count t ((Finset.univ : Finset (Fin m)).val.map (fun i => g_in (x i) (y (σ i)))) =
      ∑ a : A, ∑ b : B, if g_in a.1 b.1 = t then N a b else 0 := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i => g_in (x i) (y (σ i)) = t)
  have hcnt :
      Multiset.count t ((Finset.univ : Finset (Fin m)).val.map (fun i => g_in (x i) (y (σ i)))) =
        S.card := by
    rw [Multiset.count_map]
    have hEq :
        Multiset.filter (fun i : Fin m => t = g_in (x i) (y (σ i)))
          (Finset.univ : Finset (Fin m)).val = S.val := by
      rw [Finset.filter_val]
      congr 1
      funext i
      exact propext eq_comm
    rw [hEq]
    rfl
  rw [hcnt]
  have hfib :
      S.card = ∑ p : A × B,
        (S.filter (fun i => ((⟨x i, hxA i⟩ : A), (⟨y (σ i), hyB (σ i)⟩ : B)) = p)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun i : Fin m => ((⟨x i, hxA i⟩ : A), (⟨y (σ i), hyB (σ i)⟩ : B)))
      (fun _ _ => Finset.mem_univ _)
  rw [hfib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hg : g_in a.1 b.1 = t
  · rw [if_pos hg, ← hN a b]
    unfold inducedTable
    apply congrArg Finset.card
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Subtype.ext_iff]
    constructor
    · intro h
      exact h.2
    · intro ⟨hxi, hyi⟩
      exact ⟨by rw [hxi, hyi, hg], hxi, hyi⟩
  · rw [if_neg hg]
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro i hi hpair
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Prod.mk.injEq, Subtype.ext_iff] at hpair
    rw [hpair.1, hpair.2] at hi
    exact hg hi

/-- Multiset equality form of the pushforward counting theorem. -/
theorem merged_hist_eq_tablePushforwardHist
    {m : ℕ} (A B : Finset JointType) (x y : Fin m → JointType)
    (σ : Equiv.Perm (Fin m)) (N : A → B → ℕ)
    (hxA : ∀ i, x i ∈ A) (hyB : ∀ j, y j ∈ B)
    (hN : ∀ (a : A) (b : B), inducedTable x y σ a.1 b.1 = N a b) :
    (Finset.univ : Finset (Fin m)).val.map (fun i => g_in (x i) (y (σ i))) =
      tablePushforwardHist N := by
  rw [Multiset.ext]
  intro t
  rw [count_merged_eq_sum_table A B x y σ N hxA hyB hN t, count_tablePushforwardHist N t]

end PushforwardHistogram

section InsideJoinWitnessed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Accumulated parent-side compact state at `v` after fixing top-edge counts `q`
(charging `linearWeight R s v * q i` once) and already-processed children `S`. -/
noncomputable def parentState (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (ns : V → Fin m → V → ℕ) : CompactState m where
  active := Finset.univ.filter (fun i => 0 < q i)
  cost := fun i =>
    linearWeight R s v * (q i : ℚ) + ∑ w ∈ S, subtreeLinearCost R s w (ns w i)

/-- Extend the already-processed child witness map `ns` with a witness `nNew` at child `u`. -/
def extendChild {m : ℕ} (u : V) (ns : V → Fin m → V → ℕ)
    (nNew : Fin m → V → ℕ) : V → Fin m → V → ℕ :=
  fun w => if w = u then nNew else ns w

omit [Fintype V] [DecidableEq V] in
theorem partialValid_reindex (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (u : V) (σ : Equiv.Perm (Fin m)) (n : Fin m → V → ℕ)
    (hn : PartialValid R H m u n) :
    PartialValid R H m u (reindexMatrix σ n) := by
  constructor
  · intro i x hx
    exact hn.outside (σ i) x hx
  · intro x hx
    simpa [reindexMatrix] using (Equiv.sum_comp σ (fun j => n j x)).trans (hn.column x hx)
  · intro i x hx hne hp
    exact hn.ancestor (σ i) x hx hne hp

omit [Fintype V] [DecidableEq V] in
theorem rootChildCap_reindex (R : RootedTree V) {m : ℕ}
    (u : V) (σ : Equiv.Perm (Fin m)) (n : Fin m → V → ℕ)
    (hcap : RootChildCap R u (fun i => n i u)) :
    RootChildCap R u (fun i => reindexMatrix σ n i u) :=
  fun hr i => hcap hr (σ i)

theorem jointType_parentState_insert
    (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ) (nChild : Fin m → V → ℕ) (zChild : CompactState m)
    (hChildCost : ∀ i, subtreeLinearCost R s u (nChild i) = zChild.cost i)
    (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    jointType (parentState R s v q (insert u S) (extendChild u ns (reindexMatrix σ nChild))) i =
      g_in (jointType (parentState R s v q S ns) i) (jointType zChild (σ i)) := by
  have hsum :
      (∑ w ∈ insert u S, subtreeLinearCost R s w (extendChild u ns (reindexMatrix σ nChild) w i)) =
        zChild.cost (σ i) + ∑ w ∈ S, subtreeLinearCost R s w (ns w i) := by
    rw [Finset.sum_insert huS]
    congr 1
    · simp only [extendChild, ↓reduceIte]
      exact hChildCost (σ i)
    · apply Finset.sum_congr rfl
      intro w hw
      have hwu : w ≠ u := fun h => huS (h ▸ hw)
      simp only [extendChild, if_neg hwu]
  simp only [jointType, g_in, parentState, hsum]
  refine Prod.ext rfl ?_
  ring

theorem compat_iff_K_in
    (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V)
    (ns : V → Fin m → V → ℕ) (nChild : Fin m → V → ℕ) (zChild : CompactState m)
    (hChildAct : ∀ i, i ∈ zChild.active ↔ 0 < nChild i u)
    (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    K_in (jointType (parentState R s v q S ns) i) (jointType zChild (σ i)) ↔
      (0 < reindexMatrix σ nChild i u → 0 < q i) := by
  simp only [K_in, jointType, parentState, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, hChildAct (σ i), reindexMatrix]

/-- C3 Main Theorem (`inside_join_hist_iff`):
Fix a non-root vertex `v`, parent top-edge counts `q`, already-processed children `S`
with fixed witnesses `ns`, and a new child `u ∉ S` with witness `nChild` representing
`zChild`. For any target output histogram `h`, there exists a legal transport table
whose pushforward is `h` iff there exists a row permutation `σ` of `nChild` that keeps
the child witness valid (`PartialValid`, `RootChildCap`, `CompactRep`), respects parent
activity `q`, and yields extended parent histogram `h`. -/
theorem inside_join_hist_iff
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V) (huS : u ∉ S)
    (ns : V → Fin m → V → ℕ)
    (nChild : Fin m → V → ℕ) (zChild : CompactState m)
    (hChildValid : PartialValid R H m u nChild)
    (hChildCap : RootChildCap R u (fun i => nChild i u))
    (hChildAct : ∀ i, i ∈ zChild.active ↔ 0 < nChild i u)
    (hChildCost : ∀ i, subtreeLinearCost R s u (nChild i) = zChild.cost i)
    (h : Multiset JointType) :
    (∃ N : (Finset.univ.image (jointType (parentState R s v q S ns))) →
           (Finset.univ.image (jointType zChild)) → ℕ,
      LegalTable
        (Finset.univ.image (jointType (parentState R s v q S ns)))
        (Finset.univ.image (jointType zChild))
        (jointType (parentState R s v q S ns))
        (jointType zChild)
        K_in N ∧
      tablePushforwardHist N = h)
    ↔
    (∃ σ : Equiv.Perm (Fin m),
      PartialValid R H m u (reindexMatrix σ nChild) ∧
      RootChildCap R u (fun i => reindexMatrix σ nChild i u) ∧
      CompactRep R H m s u (reindex σ zChild) ∧
      (∀ i, 0 < reindexMatrix σ nChild i u → 0 < q i) ∧
      jointHist (parentState R s v q (insert u S) (extendChild u ns (reindexMatrix σ nChild))) = h) := by
  let pState := parentState R s v q S ns
  let A : Finset JointType := Finset.univ.image (jointType pState)
  let B : Finset JointType := Finset.univ.image (jointType zChild)
  have hxA : ∀ i : Fin m, jointType pState i ∈ A := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hyB : ∀ j : Fin m, jointType zChild j ∈ B := fun j =>
    Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hRepChild : CompactRep R H m s u zChild :=
    ⟨nChild, hChildValid, hChildCap, hChildAct, hChildCost⟩
  constructor
  · rintro ⟨N, hLeg, hPush⟩
    rcases ((transport_realize_exact A B (jointType pState) (jointType zChild) K_in N).mp hLeg).2.2
      with ⟨σ, hK, hN⟩
    refine ⟨σ, partialValid_reindex R H u σ nChild hChildValid,
      rootChildCap_reindex R u σ nChild hChildCap,
      compactRep_reindex R H s u σ zChild hRepChild, ?_, ?_⟩
    · intro i
      exact (compat_iff_K_in R s v q S u ns nChild zChild hChildAct σ i).mp (hK i)
    · unfold jointHist
      have hmap :
          (Finset.univ : Finset (Fin m)).val.map
              (jointType (parentState R s v q (insert u S)
                (extendChild u ns (reindexMatrix σ nChild)))) =
            (Finset.univ : Finset (Fin m)).val.map
              (fun i => g_in (jointType pState i) (jointType zChild (σ i))) := by
        congr 1
        funext i
        exact jointType_parentState_insert R s v q S u huS ns nChild zChild hChildCost σ i
      rw [hmap, merged_hist_eq_tablePushforwardHist A B (jointType pState) (jointType zChild)
        σ N hxA hyB hN, hPush]
  · rintro ⟨σ, _, _, _, hCompat, hHist⟩
    have hK : ∀ i : Fin m, K_in (jointType pState i) (jointType zChild (σ i)) := fun i =>
      (compat_iff_K_in R s v q S u ns nChild zChild hChildAct σ i).mpr (hCompat i)
    let N : A → B → ℕ := fun a b => inducedTable (jointType pState) (jointType zChild) σ a.1 b.1
    refine ⟨N, legalTable_of_perm A B (jointType pState) (jointType zChild) K_in hxA hyB σ hK, ?_⟩
    have hEq := merged_hist_eq_tablePushforwardHist A B (jointType pState) (jointType zChild)
      σ N hxA hyB (fun _ _ => rfl)
    rw [← hEq, ← hHist]
    unfold jointHist
    congr 1
    funext i
    exact (jointType_parentState_insert R s v q S u huS ns nChild zChild hChildCost σ i).symm

end InsideJoinWitnessed

section RegressionExamples

/-! ### Regression 1: Output-type merging (`0 + 1` and `1 + 0` both produce `(true, 1)`, count = 2) -/

def exMerge_x : Fin 2 → JointType := ![(true, (0 : ℚ)), (true, (1 : ℚ))]
def exMerge_y : Fin 2 → JointType := ![(true, (1 : ℚ)), (false, (0 : ℚ))]
def exMerge_A : Finset JointType := {(true, (0 : ℚ)), (true, (1 : ℚ))}
def exMerge_B : Finset JointType := {(true, (1 : ℚ)), (false, (0 : ℚ))}
def exMerge_N : exMerge_A → exMerge_B → ℕ :=
  fun a b =>
    if (a.1 = (true, (0 : ℚ)) ∧ b.1 = (true, (1 : ℚ))) ∨
       (a.1 = (true, (1 : ℚ)) ∧ b.1 = (false, (0 : ℚ)))
    then 1 else 0

theorem exMerge_output_count_two :
    Multiset.count (true, (1 : ℚ))
      ((Finset.univ : Finset (Fin 2)).val.map
        (fun i => g_in (exMerge_x i) (exMerge_y (Equiv.refl (Fin 2) i)))) = 2 := by
  have hxA : ∀ i, exMerge_x i ∈ exMerge_A := by
    intro i; fin_cases i <;> simp [exMerge_x, exMerge_A]
  have hyB : ∀ j, exMerge_y j ∈ exMerge_B := by
    intro j; fin_cases j <;> simp [exMerge_y, exMerge_B]
  have hN : ∀ (a : exMerge_A) (b : exMerge_B),
      inducedTable exMerge_x exMerge_y (Equiv.refl (Fin 2)) a.1 b.1 = exMerge_N a b := by
    intro a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [exMerge_A, exMerge_B, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · unfold inducedTable
      simp only [exMerge_N, Equiv.refl_apply, true_and, true_or, ↓reduceIte]
      exact Finset.card_eq_one.mpr ⟨0, by ext i; fin_cases i <;> simp [exMerge_x, exMerge_y]⟩
    · unfold inducedTable
      simp only [exMerge_N, Equiv.refl_apply, Prod.mk.injEq, true_and, and_true,
        Bool.false_eq_true, zero_ne_one]
      apply Finset.card_eq_zero.mpr
      ext i; fin_cases i <;> simp [exMerge_x, exMerge_y]
    · unfold inducedTable
      simp only [exMerge_N, Equiv.refl_apply, Prod.mk.injEq, true_and, and_true,
        one_ne_zero, Bool.true_eq_false]
      apply Finset.card_eq_zero.mpr
      ext i; fin_cases i <;> simp [exMerge_x, exMerge_y]
    · unfold inducedTable
      simp only [exMerge_N, Equiv.refl_apply, true_and, or_true, ↓reduceIte]
      exact Finset.card_eq_one.mpr ⟨1, by ext i; fin_cases i <;> simp [exMerge_x, exMerge_y]⟩
  rw [count_merged_eq_sum_table exMerge_A exMerge_B exMerge_x exMerge_y
    (Equiv.refl (Fin 2)) exMerge_N hxA hyB hN (true, (1 : ℚ))]
  rw [← count_tablePushforwardHist]
  unfold tablePushforwardHist
  have hA : (Finset.univ : Finset exMerge_A) =
      {⟨(true, (0 : ℚ)), by simp [exMerge_A]⟩, ⟨(true, (1 : ℚ)), by simp [exMerge_A]⟩} := by
    ext ⟨a, ha⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa [exMerge_A] using ha
  have hB : (Finset.univ : Finset exMerge_B) =
      {⟨(true, (1 : ℚ)), by simp [exMerge_B]⟩, ⟨(false, (0 : ℚ)), by simp [exMerge_B]⟩} := by
    ext ⟨b, hb⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa [exMerge_B] using hb
  rw [hA, Finset.sum_pair (by intro h; simp at h)]
  rw [hB, Finset.sum_pair (by intro h; simp at h), Finset.sum_pair (by intro h; simp at h)]
  simp [exMerge_N, g_in]

/-! ### Regression 2: Parent-child forbidden pairing (`K_in` rejects `(false, _) + (true, _)`) -/

theorem exForbidden_no_legal_table :
    ¬ ∃ N : ({(false, (0 : ℚ))} : Finset JointType) →
            ({(true, (1 : ℚ))} : Finset JointType) → ℕ,
      LegalTable {(false, (0 : ℚ))} {(true, (1 : ℚ))}
        (fun _ : Fin 1 => (false, (0 : ℚ)))
        (fun _ : Fin 1 => (true, (1 : ℚ)))
        K_in N := by
  rintro ⟨N, _, _, hrow, _, hforb⟩
  have hzero : N ⟨(false, (0 : ℚ)), by simp⟩ ⟨(true, (1 : ℚ)), by simp⟩ = 0 :=
    hforb ⟨(false, (0 : ℚ)), by simp⟩ ⟨(true, (1 : ℚ)), by simp⟩ (by simp [K_in])
  have hr := hrow ⟨(false, (0 : ℚ)), by simp⟩
  simp at hr
  exact Nat.zero_ne_one (hzero.symm.trans hr)

/-! ### Regression 3: Negative rational cost addition (`5 + (-7) = -2`, `(-3/2) + (1/2) = -1`) -/

def exNeg_x : Fin 2 → JointType := ![(true, (5 : ℚ)), (true, (-3 : ℚ) / 2)]
def exNeg_y : Fin 2 → JointType := ![(true, (-7 : ℚ)), (false, (1 : ℚ) / 2)]

theorem exNeg_signed_cost_addition :
    g_in (exNeg_x 0) (exNeg_y 0) = (true, (-2 : ℚ)) ∧
    g_in (exNeg_x 1) (exNeg_y 1) = (true, (-1 : ℚ)) ∧
    K_in (exNeg_x 0) (exNeg_y 0) ∧
    K_in (exNeg_x 1) (exNeg_y 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [g_in, K_in, exNeg_x, exNeg_y] <;> norm_num

/-! ### Regression 4: Zero routes (`m = 0`) instantiation of `inside_join_hist_iff` -/

theorem exZeroRoutes_inside_join {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (H : V → ℕ) (s : V → ℚ)
    (v : V) (q : Fin 0 → ℕ) (S : Finset V) (u : V) (huS : u ∉ S)
    (ns : V → Fin 0 → V → ℕ)
    (nChild : Fin 0 → V → ℕ) (zChild : CompactState 0)
    (hChildValid : PartialValid R H 0 u nChild)
    (hChildCap : RootChildCap R u (fun i => nChild i u))
    (hChildAct : ∀ i, i ∈ zChild.active ↔ 0 < nChild i u)
    (hChildCost : ∀ i, subtreeLinearCost R s u (nChild i) = zChild.cost i) :
    ∃ N : (Finset.univ.image (jointType (parentState R s v q S ns))) →
          (Finset.univ.image (jointType zChild)) → ℕ,
      LegalTable
        (Finset.univ.image (jointType (parentState R s v q S ns)))
        (Finset.univ.image (jointType zChild))
        (jointType (parentState R s v q S ns))
        (jointType zChild)
        K_in N ∧
      tablePushforwardHist N = 0 := by
  apply (inside_join_hist_iff R H s v q S u huS ns nChild zChild
    hChildValid hChildCap hChildAct hChildCost 0).mpr
  refine ⟨Equiv.refl (Fin 0),
    partialValid_reindex R H u (Equiv.refl (Fin 0)) nChild hChildValid,
    rootChildCap_reindex R u (Equiv.refl (Fin 0)) nChild hChildCap,
    compactRep_reindex R H s u (Equiv.refl (Fin 0)) zChild
      ⟨nChild, hChildValid, hChildCap, hChildAct, hChildCost⟩,
    fun i => Fin.elim0 i, ?_⟩
  simp [jointHist]

end RegressionExamples

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.count_merged_eq_sum_table
#print axioms UAVProof.TreeBudgetOrbitPrototype.merged_hist_eq_tablePushforwardHist
#print axioms UAVProof.TreeBudgetOrbitPrototype.inside_join_hist_iff
