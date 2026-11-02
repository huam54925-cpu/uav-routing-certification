import LeanCompletion.UAV.TreeBudgetRootFactorization
import LeanCompletion.UAV.TreeBudgetCertificate

/-! Executable branch certificate operations. Rows and multiplicities, including
zero multiplicities, are preserved; no route copies are expanded. -/
namespace UAVProof.TreeBudgetBranchCertificate
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetRootFactorization
variable {n : ℕ}

abbrev Entry (n : ℕ) := (Fin n → ℕ) × ℕ

def entries (C : Certificate (Fin n)) : List (Entry n) :=
  List.ofFn (fun i => (C.row i, C.count i))

def ofEntries (xs : List (Entry n)) : Certificate (Fin n) :=
  ⟨xs.length, fun i => (xs.get i).1, fun i => (xs.get i).2⟩

def ValidEntries (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (Entry n)) : Prop :=
  (∀ e ∈ xs, RowValid R h s T e.1) ∧ (xs.map Prod.snd).sum = m ∧
    ∀ v, v ≠ R.root → (xs.map (fun e => e.2 * e.1 v)).sum = h v

@[simp] theorem entries_ofEntries (xs : List (Entry n)) : entries (ofEntries xs) = xs := by
  simpa only [entries, ofEntries, Prod.mk.eta] using List.ofFn_get xs

theorem valid_iff_entries (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) :
    Valid R h m s T C ↔ ValidEntries R h m s T (entries C) := by
  simp [Valid, ValidEntries, entries, List.map_ofFn, List.sum_ofFn]

theorem valid_ofEntries_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (xs : List (Entry n)) :
    Valid R h m s T (ofEntries xs) ↔ ValidEntries R h m s T xs := by
  rw [valid_iff_entries, entries_ofEntries]

def rootChildren (R : RootedTree (Fin n)) : List (RootChild R) :=
  (List.finRange n).filterMap fun v =>
    if hv : v ∈ children R R.root then some (⟨v, hv⟩ : RootChild R) else none

theorem mem_rootChildren (R : RootedTree (Fin n)) (c : RootChild R) : c ∈ rootChildren R := by
  apply List.mem_filterMap.mpr
  exact ⟨c.val, List.mem_finRange c.val, by simp [c.property]⟩

theorem nodup_rootChildren (R : RootedTree (Fin n)) : (rootChildren R).Nodup := by
  apply List.Nodup.filterMap ?_ (List.nodup_finRange n)
  intro a b c ha hb
  split_ifs at ha with ha'
  · split_ifs at hb with hb'
    · have hca : (⟨a, ha'⟩ : RootChild R) = c := by simpa using ha
      have hcb : (⟨b, hb'⟩ : RootChild R) = c := by simpa using hb
      exact congrArg Subtype.val (hca.trans hcb.symm)
    · simp at hb
  · simp at ha

theorem sum_rootChildren (R : RootedTree (Fin n)) (f : RootChild R → ℕ) :
    ((rootChildren R).map f).sum = ∑ c, f c := by
  have he : (rootChildren R).toFinset = Finset.univ := by
    ext c; simp [mem_rootChildren]
  rw [← List.sum_toFinset f (nodup_rootChildren R), he]

def splitBranch (R : RootedTree (Fin n)) (C : Certificate (Fin n))
    (c : RootChild R) : Certificate (Fin n) :=
  ofEntries ((entries C).filter (fun e => decide (e.1 c.val = 1)))

def mergeBranches (R : RootedTree (Fin n)) (cs : RootChild R → Certificate (Fin n)) :
    Certificate (Fin n) :=
  ofEntries ((rootChildren R).flatMap (fun c => entries (cs c)))

theorem rowValid_exists_pattern (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (p : Fin n → ℕ) (hp : RowValid R h s T p) :
    ∃ q : Pattern R h s T, values q.val = p := by
  have hn : TreeBudgetPatterns.normalize R p = p := by
    funext v
    by_cases hv : v = R.root <;> simp [TreeBudgetPatterns.normalize, hv, hp.1]
  refine ⟨⟨packRow R h p hp.2.1, ?_⟩, ?_⟩
  · simpa only [ValidPattern, values_packRow, hn] using hp.2.2
  · simpa only [values_packRow] using hn

theorem rowValid_zero_outside (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (p : Fin n → ℕ)
    (hp : RowValid R h s T p) (hc : p c.val = 1) {v : Fin n}
    (hv : ¬ InRootSubtree R c v) : p v = 0 := by
  obtain ⟨q, hq⟩ := rowValid_exists_pattern R h s T p hp
  have hqc : values q.val c.val = 1 := by rw [hq]; exact hc
  simpa only [hq] using pattern_zero_outside R h s T c ⟨q, hqc⟩ hv

theorem rowValid_branch_iff (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (p : Fin n → ℕ) :
    RowValid R (branchMultiplicity R h c) s T p ↔ RowValid R h s T p ∧ p c.val = 1 := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := rowValid_exists_pattern R _ s T p hp
    refine ⟨⟨hp.1, fun v hv => (hp.2.1 v hv).trans (branchMultiplicity_le R h c v), hp.2.2⟩, ?_⟩
    simpa only [hq] using masked_pattern_child R h s T c q
  · rintro ⟨hp, hc⟩
    refine ⟨hp.1, fun v hv => ?_, hp.2.2⟩
    by_cases hs : InRootSubtree R c v
    · simpa [branchMultiplicity, hs] using hp.2.1 v hv
    · simp [branchMultiplicity, hs, rowValid_zero_outside R h s T c p hp hc hs]

theorem sum_flatMap_map {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem sum_map_congr {A : Type*} (xs : List A) (f g : A → ℕ)
    (he : ∀ a ∈ xs, f a = g a) : (xs.map f).sum = (xs.map g).sum := by
  congr 1
  exact List.map_congr_left he

theorem sum_branchMultiplicity (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (v : Fin n) (hv : v ≠ R.root) : (∑ c : RootChild R, branchMultiplicity R h c v) = h v := by
  obtain ⟨c, hc, _⟩ := subtree_partition R v hv
  rw [Finset.sum_eq_single c]
  · simp [branchMultiplicity, hc]
  · intro d _ hdc
    have hn : ¬ InRootSubtree R d v := fun hd => hdc (subtree_disjoint R hd hc)
    simp [branchMultiplicity, hn]
  · simp

theorem mergeBranches_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cs : RootChild R → Certificate (Fin n))
    (hm : m = rootCount R h)
    (hcs : ∀ c, Valid R (branchMultiplicity R h c) (h c.val) s T (cs c)) :
    Valid R h m s T (mergeBranches R cs) := by
  have hl c := (valid_iff_entries R _ _ s T (cs c)).mp (hcs c)
  rw [mergeBranches, valid_ofEntries_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨c, _, he⟩ := List.mem_flatMap.mp he
    exact ((rowValid_branch_iff R h s T c e.1).mp ((hl c).1 e he)).1
  · rw [sum_flatMap_map]
    calc
      _ = ((rootChildren R).map (fun c => h c.val)).sum :=
        sum_map_congr _ _ _ (fun c _ => (hl c).2.1)
      _ = ∑ c : RootChild R, h c.val := sum_rootChildren R _
      _ = rootCount R h := Finset.sum_coe_sort _ _
      _ = m := hm.symm
  · intro v hv
    rw [sum_flatMap_map]
    calc
      _ = ((rootChildren R).map (fun c => branchMultiplicity R h c v)).sum :=
        sum_map_congr _ _ _ (fun c _ => (hl c).2.2 v hv)
      _ = ∑ c : RootChild R, branchMultiplicity R h c v := sum_rootChildren R _
      _ = h v := sum_branchMultiplicity R h v hv

theorem mergeBranches_checked (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cs : RootChild R → Certificate (Fin n))
    (hm : m = rootCount R h)
    (hcs : ∀ c, checkCertificate R (branchMultiplicity R h c) (h c.val) s T (cs c) = true) :
    checkCertificate R h m s T (mergeBranches R cs) = true :=
  (checkCertificate_eq_true_iff ..).mpr (mergeBranches_sound R h m s T cs hm
    (fun c => (checkCertificate_eq_true_iff ..).mp (hcs c)))

theorem rowValid_root_le_one (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (p : Fin n → ℕ)
    (hp : RowValid R h s T p) : p c.val ≤ 1 :=
  (Finset.single_le_sum (fun a _ => Nat.zero_le (p a)) c.property).trans hp.2.2.1.le

theorem rowValid_unselected_zero (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (p : Fin n → ℕ)
    (hp : RowValid R h s T p) (hc : p c.val ≠ 1) {v : Fin n}
    (hv : InRootSubtree R c v) : p v = 0 := by
  by_contra hn
  have hpos := positive_at_rootBranch R p hp.2.2.2.1 v hv.1 (Nat.pos_of_ne_zero hn)
  rw [hv.2] at hpos
  have hle := rowValid_root_le_one R h s T c p hp
  exact hc (by omega)

theorem filtered_column (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (xs : List (Entry n))
    (hx : ∀ e ∈ xs, RowValid R h s T e.1) (v : Fin n) (hv : InRootSubtree R c v) :
    ((xs.filter (fun e => decide (e.1 c.val = 1))).map (fun e => e.2 * e.1 v)).sum =
      (xs.map (fun e => e.2 * e.1 v)).sum := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have he := hx e (by simp)
    have ht : ∀ a ∈ xs, RowValid R h s T a.1 := fun a ha => hx a (by simp [ha])
    by_cases hc : e.1 c.val = 1
    · simp [hc, ih ht]
    · have hz := rowValid_unselected_zero R h s T c e.1 he hc hv
      simp [hc, hz, ih ht]

theorem splitBranch_sound (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) (c : RootChild R)
    (hC : Valid R h m s T C) :
    Valid R (branchMultiplicity R h c) (h c.val) s T (splitBranch R C c) := by
  have hx := (valid_iff_entries R h m s T C).mp hC
  have selected (e : Entry n)
      (he : e ∈ (entries C).filter (fun e => decide (e.1 c.val = 1))) :
      RowValid R h s T e.1 ∧ e.1 c.val = 1 := by
    obtain ⟨hm, hp⟩ := List.mem_filter.mp he
    exact ⟨hx.1 e hm, of_decide_eq_true hp⟩
  rw [splitBranch, valid_ofEntries_iff]
  refine ⟨fun e he => (rowValid_branch_iff ..).mpr (selected e he), ?_, ?_⟩
  · calc
      _ = (((entries C).filter (fun e => decide (e.1 c.val = 1))).map
          (fun e => e.2 * e.1 c.val)).sum := by
        apply sum_map_congr
        intro e he
        rw [(selected e he).2, Nat.mul_one]
      _ = ((entries C).map (fun e => e.2 * e.1 c.val)).sum :=
        filtered_column R h s T c _ hx.1 c.val (subtree_self R c)
      _ = h c.val := hx.2.2 c.val (child_spec R c).1
  · intro v hv
    by_cases hs : InRootSubtree R c v
    · rw [filtered_column R h s T c _ hx.1 v hs, hx.2.2 v hv]
      simp [branchMultiplicity, hs]
    · have hz : (((entries C).filter (fun e => decide (e.1 c.val = 1))).map
          (fun e => e.2 * e.1 v)).sum = 0 := by
        calc
          _ = (((entries C).filter (fun e => decide (e.1 c.val = 1))).map
              (fun _ => (0 : ℕ))).sum := by
            apply sum_map_congr
            intro e he
            rw [rowValid_zero_outside R h s T c e.1 (selected e he).1 (selected e he).2 hs,
              Nat.mul_zero]
          _ = 0 := by simp
      simpa [branchMultiplicity, hs] using hz

theorem splitBranch_checked (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) (c : RootChild R)
    (hC : checkCertificate R h m s T C = true) :
    checkCertificate R (branchMultiplicity R h c) (h c.val) s T (splitBranch R C c) = true :=
  (checkCertificate_eq_true_iff ..).mpr (splitBranch_sound R h m s T C c
    ((checkCertificate_eq_true_iff ..).mp hC))

theorem zero_branch_valid_size (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : RootChild R) (C : Certificate (Fin n))
    (hc : h c.val = 0) (hC : Valid R (branchMultiplicity R h c) 0 s T C) : C.size = 0 := by
  by_contra hn
  let i : Fin C.size := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hp := hC.1 i
  have hsel := ((rowValid_branch_iff R h s T c (C.row i)).mp hp).2
  have hbound := hp.2.1 c.val (child_spec R c).1
  simp [branchMultiplicity, hc, hsel] at hbound

/-- Regrouping changes order only, including duplicated and zero-multiplicity entries. -/
theorem merge_split_entries_perm (R : RootedTree (Fin n)) (h : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n)) (hC : Valid R h m s T C) :
    (entries (mergeBranches R (splitBranch R C))).Perm (entries C) := by
  classical
  have hx := (valid_iff_entries R h m s T C).mp hC
  apply List.perm_iff_count.mpr
  intro e
  simp only [mergeBranches, entries_ofEntries, List.count_flatMap, Function.comp_def,
    splitBranch, entries_ofEntries]
  rw [sum_rootChildren]
  by_cases he : e ∈ entries C
  · obtain ⟨q, hq⟩ := rowValid_exists_pattern R h s T e.1 (hx.1 e he)
    obtain ⟨c, hc, hu⟩ := pattern_unique_root_child R h s T q
    have hce : e.1 c.val = 1 := by rw [← hq]; exact hc
    rw [Finset.sum_eq_single c]
    · exact List.count_filter (by simpa using hce)
    · intro d _ hdc
      have hne : e.1 d.val ≠ 1 := by
        intro hd
        exact hdc (hu d (by simpa only [hq] using hd))
      apply List.count_eq_zero.mpr
      intro hd
      exact hne (of_decide_eq_true (List.mem_filter.mp hd).2)
    · simp
  · rw [List.count_eq_zero.mpr he]
    apply Finset.sum_eq_zero
    intro c _
    exact List.count_eq_zero.mpr (fun hc => he (List.mem_filter.mp hc).1)

end UAVProof.TreeBudgetBranchCertificate

#print axioms UAVProof.TreeBudgetBranchCertificate.entries_ofEntries
#print axioms UAVProof.TreeBudgetBranchCertificate.valid_iff_entries
#print axioms UAVProof.TreeBudgetBranchCertificate.nodup_rootChildren
#print axioms UAVProof.TreeBudgetBranchCertificate.rowValid_branch_iff
#print axioms UAVProof.TreeBudgetBranchCertificate.mergeBranches_sound
#print axioms UAVProof.TreeBudgetBranchCertificate.mergeBranches_checked
#print axioms UAVProof.TreeBudgetBranchCertificate.splitBranch_sound
#print axioms UAVProof.TreeBudgetBranchCertificate.splitBranch_checked
#print axioms UAVProof.TreeBudgetBranchCertificate.zero_branch_valid_size
#print axioms UAVProof.TreeBudgetBranchCertificate.merge_split_entries_perm
