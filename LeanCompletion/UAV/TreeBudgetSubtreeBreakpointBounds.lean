import LeanCompletion.UAV.TreeBudgetSubtreeBudgetProfile
import LeanCompletion.UAV.TreeBudgetSubtreeResourceRealizes

/-! Arithmetic and positional bounds for strict prefix minima in the final root table. -/
namespace UAVProof.TreeBudgetSubtreeBudgetProfile
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeIntegerWitnessSeed

private theorem records_sublist {α : Type} (xs : List (Int × α)) (cut : Option Int) :
    (records cut xs).Sublist xs := by
  induction xs generalizing cut with
  | nil => cases cut <;> simp [records]
  | cons x xs ih =>
    cases cut with
    | none => exact (ih _).cons_cons _
    | some t =>
      by_cases h : x.1 < t
      · simpa only [records, if_pos h] using (ih (some x.1)).cons_cons x
      · simpa only [records, if_neg h] using (ih (some t)).cons x

private theorem query_mem {α : Type} {e : Int × α} (B : Int) (xs : List (Int × α))
    (h : query B xs = some e) : e ∈ xs := by
  induction xs with
  | nil => simp [query] at h
  | cons a as ih =>
    by_cases ha : a.1 ≤ B
    · simp [query, ha] at h
      simp [h]
    · exact List.mem_cons_of_mem _ (ih (by simpa [query, ha] using h))

/-- With positions carried as payloads, every all-budget equivalent subsequence
contains each record position, including the first representative of a tie. -/
theorem records_necessary {α : Type} (xs ys : List (Int × α))
    (heq : ∀ B, query B ys = query B xs) {e} (he : e ∈ records none xs) : e ∈ ys :=
  query_mem e.1 ys ((heq _).trans ((query_records_none _ _).symm.trans
    (query_at_record (records_decreasing _ _) he)))

variable {N k : Nat}

/-- The integer cost coordinates of every root witness come from one nonnegative
matrix with exactly the prescribed non-root column sums. -/
private theorem root_matrix (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (r : Root N m)
    (hr : r ∈ roots ((childrenList R R.root).map (compute R H w m))) :
    ∃ n : Fin m → Fin N → Nat,
      (∀ x, x ≠ R.root → ∑ i, n i x = H x) ∧
      ∀ i, val r.key.cost i = ∑ x ∈ Finset.univ.erase R.root, w x * (n i x : Int) := by
  classical
  obtain ⟨sel, costs⟩ := TreeBudgetSubtreeResourceSeed.roots_cost_spec _ r hr
  obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R R.root)
    (compute R H w m) r.picks).mp sel
  have valid u (hu : u ∈ R.children R.root) := TreeBudgetSubtreeResourceSeed.compute_realizes
    R H w m u (f u) (hm u ((mem_childrenList ..).mpr hu))
  have partials u (hu : u ∈ R.children R.root) := (valid u hu).1
  let n := glueMatrix R R.root (fun _ : Fin m => 0) (fun u => TreeBudgetSubtreeWitness.matrixVal (f u).matrix)
  have here {u x} (hu : u ∈ R.children R.root) (hx : InSubtree R u x) (i) :
      n i x = TreeBudgetSubtreeWitness.matrixVal (f u).matrix i x := glueMatrix_child _ partials hu hx i
  refine ⟨n, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (subtree_cases (root_subtree R x)).resolve_left hx
    simpa only [here hu hxu] using (partials u hu).column x hxu
  · intro i
    rw [costs i, ← hf, List.map_map, childrenList_sum]
    let g (x : Fin N) := w x * (n i x : Int)
    have forest : (∑ u ∈ R.children R.root, ∑ x ∈ subtree R u, g x) =
        ∑ x ∈ Finset.univ.erase R.root, g x := by
      have h := sum_subtree R R.root g
      rw [subtree_root] at h
      have e := Finset.sum_erase_add Finset.univ g (Finset.mem_univ R.root)
      omega
    refine Eq.trans (Finset.sum_congr rfl ?_) forest
    intro u hu
    change val (f u).key.cost i = _
    rw [← (valid u hu).2.2.2 i]
    exact Finset.sum_congr rfl fun x hx => by simp [g, here hu ((mem_subtree ..).mp hx)]

private theorem scored_mem {rs : List (Root N (k+1))} {e : Int × Root N (k+1)}
    (he : e ∈ scored rs) : e.2 ∈ rs ∧ e.1 = peak e.2.key := by
  induction rs with
  | nil => simp [scored] at he
  | cons r rs ih =>
    by_cases h : completeUse r.key = true
    · simp only [scored, h, if_true, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨List.mem_cons_self, rfl⟩
      · exact ⟨List.mem_cons_of_mem _ (ih he).1, (ih he).2⟩
    · simp only [scored, h] at he
      exact ⟨List.mem_cons_of_mem _ (ih he).1, (ih he).2⟩

private theorem peak_attained (q : TreeBudgetSubtreeInteger.IntRoot (k+1)) :
    ∃ i, peak q = val q.cost i := by
  by_contra! h
  have upper := (peak_le q (peak q)).mp le_rfl
  have hh : peak q ≤ peak q - 1 := (peak_le q _).mpr fun i => by
    have := h i
    have := upper i
    omega
  omega

noncomputable def total (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int) : Int :=
  ∑ v ∈ Finset.univ.erase R.root, w v * H v

noncomputable def positiveTotal (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int) : Int :=
  ∑ v ∈ Finset.univ.erase R.root, max (w v) 0 * H v

/-- GCD uses only non-root columns of positive mass. -/
noncomputable def divisor (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int) : Int :=
  ((Finset.univ.erase R.root).filter (fun x => 0 < H x)).gcd w

private theorem record_range (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    {e : Int × Root N (k+1)} (he : e ∈ buildProfile R H w k) :
    total R H w ≤ (k+1 : Nat) * e.1 ∧ e.1 ≤ positiveTotal R H w ∧ divisor R H w ∣ e.1 := by
  obtain ⟨hr, hb⟩ := scored_mem ((records_sublist _ none).subset he)
  obtain ⟨n, cols, costs⟩ := root_matrix R H w (k+1) e.2 hr
  have allSum : (∑ i, val e.2.key.cost i) = total R H w := by
    simp_rw [costs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum, ← cols x (Finset.mem_erase.mp hx).1]
    simp
  have up := (peak_le e.2.key e.1).mp hb.ge
  obtain ⟨i, hi⟩ := peak_attained e.2.key
  refine ⟨?_, ?_, ?_⟩
  · rw [← allSum]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => up i)
  · rw [hb, hi, costs]
    apply Finset.sum_le_sum
    intro x hx
    have h := Finset.single_le_sum (f := fun j => n j x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [cols x (Finset.mem_erase.mp hx).1] at h
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast h) (le_max_right _ _))
  · rw [hb, hi, costs]
    apply Finset.dvd_sum
    intro x hx
    by_cases hz : H x = 0
    · have h := Finset.single_le_sum (f := fun j => n j x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [cols x (Finset.mem_erase.mp hx).1, hz] at h
      simp [Nat.eq_zero_of_le_zero h]
    · exact dvd_mul_of_dvd_left (Finset.gcd_dvd (Finset.mem_filter.mpr ⟨hx, by omega⟩)) _

private theorem length_le_card (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (k : Nat) (s : Finset Int) (hs : ∀ e ∈ buildProfile R H w k, e.1 ∈ s) :
    (buildProfile R H w k).length ≤ s.card := by
  let xs := buildProfile R H w k
  have h : xs.Pairwise (fun a b => b.1 < a.1) := records_decreasing _ _
  have nd : (xs.map Prod.fst).Nodup := List.pairwise_map.mpr (h.imp fun hp => ne_of_gt hp)
  have sub : (xs.map Prod.fst).toFinset ⊆ s := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact hs _ he
  simpa only [List.toFinset_card_of_nodup nd, List.length_map] using Finset.card_le_card sub

/-- Bound the number of breakpoints by the number of full-use candidates and
by the integer multiples of the active-column gcd in the attainable interval. -/
theorem breakpoint_bound (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (k : Nat) (hg : 0 < divisor R H w) :
    let g := divisor R H w
    let lower := -((-total R H w) / (((k+1 : Nat) : Int) * g))
    let upper := positiveTotal R H w / g
    let rs := roots ((childrenList R R.root).map (compute R H w (k+1)))
    (buildProfile R H w k).length ≤ min (scored rs).length (upper+1-lower).toNat := by
  dsimp only
  apply le_min
  · exact (records_sublist _ none).length_le
  · let g := divisor R H w
    let m : Int := k+1
    let lower := -((-total R H w) / (m*g))
    let upper := positiveTotal R H w / g
    let interval := Finset.Icc lower upper
    have hp : 0 < m*g := mul_pos (by dsimp [m]; positivity) hg
    have h := length_le_card R H w k (interval.image (fun z => g*z)) (by
      intro e he
      obtain ⟨hl, hu, z, hz⟩ := record_range R H w he
      refine Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hz.symm⟩
      · change -((-total R H w)/(m*g)) ≤ z
        apply neg_le.mp
        apply (Int.le_ediv_iff_mul_le hp).mpr
        change total R H w ≤ m * e.1 at hl
        rw [hz] at hl
        nlinarith
      · apply (Int.le_ediv_iff_mul_le hg).mpr
        simpa only [hz, mul_comm] using hu)
    exact (h.trans Finset.card_image_le).trans_eq (Int.card_Icc ..)

theorem breakpoint_bound_zero (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (k : Nat) (hg : divisor R H w = 0) : (buildProfile R H w k).length ≤ 1 := by
  apply (length_le_card R H w k {0} ?_).trans_eq (Finset.card_singleton _)
  intro e he
  have hh := (record_range R H w he).2.2
  simpa [hg] using hh

theorem breakpoint_bound_single (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int) :
    (buildProfile R H w 0).length ≤ 1 := by
  apply (length_le_card R H w 0 {total R H w} ?_).trans_eq (Finset.card_singleton _)
  intro e he
  obtain ⟨hr, hb⟩ := scored_mem ((records_sublist _ none).subset he)
  obtain ⟨n, cols, costs⟩ := root_matrix R H w 1 e.2 hr
  obtain ⟨i, hi⟩ := peak_attained e.2.key
  rw [Finset.mem_singleton, hb, hi, costs]
  apply Finset.sum_congr rfl
  intro x hx
  have col := cols x (Finset.mem_erase.mp hx).1
  have hi0 : i = (0 : Fin 1) := Fin.ext (by omega)
  simpa [Finset.univ_unique, hi0] using
    congrArg (fun a : Nat => w x * (a : Int)) col

end UAVProof.TreeBudgetSubtreeBudgetProfile
