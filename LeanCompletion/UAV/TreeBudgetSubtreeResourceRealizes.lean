import LeanCompletion.UAV.TreeBudgetSubtreeResourceCensus
import LeanCompletion.UAV.TreeBudgetSubtreeResourceWidths

/-! Integer payload semantics before deduplication and before root rejection. -/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeWitness (Matrix matrixVal)
variable {N m : ℕ}

theorem inside_spec (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) (r : Inside N m) (hr : r ∈ inside a base ts) :
    List.Forall₂ (fun t e => e ∈ t) ts r.picks ∧
      (∀ e ∈ r.picks, subsetB e.key.active a = true) ∧
      ∀ i, val r.cost i = val base i + (r.picks.map fun e => val e.key.cost i).sum := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨base, []⟩ := by simpa [inside] using hr
    subst r
    exact ⟨.nil, by simp, by simp⟩
  | cons t ts ih =>
    have hh := TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Inside.cost hr
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hh
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hp, hs, hc⟩ := ih b hb
    obtain ⟨het, hea⟩ := List.mem_filter.mp he
    refine ⟨.cons het hp, ?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hea
      · exact hs f hf
    · intro i
      simp only [TreeBudgetSubtreeInteger.add, val_ofFn, List.map_cons, List.sum_cons, hc i]
      ring

theorem glue_eq (R : RootedTree (Fin N)) (v : Fin N) (q : Vector ℕ m)
    (es : List (Entry N m)) (f : Fin N → Entry N m) (hf : (childrenList R v).map f = es) :
    matrixVal (glue v q es) = glueMatrix R v (val q) (fun u => matrixVal (f u).matrix) := by
  funext i x
  simp only [matrixVal, glue, val_ofFn, glueMatrix]
  rw [← hf, List.map_map, childrenList_sum]
  rfl

def Realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (e : Entry N m) : Prop :=
  PartialValid R H m v (matrixVal e.matrix) ∧
    RootChildCap R v (fun i => matrixVal e.matrix i v) ∧
    (∀ i, val e.key.active i = true ↔ 0 < matrixVal e.matrix i v) ∧
    ∀ i, (∑ x ∈ subtree R v, w x * (matrixVal e.matrix i x : ℤ)) = val e.key.cost i

theorem nodeRaw_realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (tables : Fin N → List (Entry N m))
    (ht : ∀ u ∈ R.children v, ∀ e ∈ tables u, Realizes R H w u e)
    (e : Entry N m) (he : e ∈ nodeRawEntries R H w m v ((childrenList R v).map tables)) :
    Realizes R H w v e := by
  classical
  simp only [nodeRawEntries, List.mem_flatMap, List.mem_map] at he
  obtain ⟨q, hq, r, hr, rfl⟩ := he
  obtain ⟨hsel, hs, hc⟩ := inside_spec _ _ _ r hr
  obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R v) tables r.picks).mp hsel
  have hv : ∀ u ∈ R.children v, Realizes R H w u (f u) := fun u hu =>
    ht u hu (f u) (hm u ((mem_childrenList _ _ _).mpr hu))
  have hn := fun u hu => (hv u hu).1
  obtain ⟨hqsum, hcap⟩ := (localCandidates_spec R H v q).mp hq
  simp only [Realizes]
  rw [glue_eq R v q r.picks f hf]
  refine ⟨partial_glue_valid hqsum hn ?_, ?_, ?_, ?_⟩
  · intro u hu i hp
    have hmem : f u ∈ r.picks := by
      rw [← hf]
      exact List.mem_map_of_mem ((mem_childrenList _ _ _).mpr hu)
    have hsub := (subsetB_spec _ _).mp (hs (f u) hmem)
    have hpos := hsub i ((hv u hu).2.2.1 i |>.mpr hp)
    simpa [support] using hpos
  · simpa only [glueMatrix_top] using hcap
  · intro i; simp [support]
  · intro i
    rw [sum_subtree, glueMatrix_top]
    have hh : (∑ u ∈ R.children v, ∑ x ∈ subtree R u,
        w x * (glueMatrix R v (val q) (fun u => matrixVal (f u).matrix) i x : ℤ)) =
        ∑ u ∈ R.children v, val (f u).key.cost i := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        _ = ∑ x ∈ subtree R u, w x * (matrixVal (f u).matrix i x : ℤ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [glueMatrix_child (val q) hn hu ((mem_subtree _ _ _).mp hx)]
        _ = _ := (hv u hu).2.2.2 i
    rw [hh]
    have hc' := hc i
    rw [← hf, List.map_map, childrenList_sum] at hc'
    simpa using hc'.symm

theorem compute_realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (e : Entry N m) (he : e ∈ compute R H w m v) :
    Realizes R H w v e := by
  rw [compute, List.attach_map_val] at he
  apply nodeRaw_realizes R H w m v (compute R H w m) ?_ e
    (TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Entry.key he)
  intro u hu e he
  exact compute_realizes R H w m u e he
termination_by R.rank v
decreasing_by exact R.child_rank hu

noncomputable def subtreeMagnitude (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (v : Fin N) : ℕ := ∑ x ∈ subtree R v, (w x).natAbs * H x

noncomputable def costMagnitude (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) : ℕ := ∑ x ∈ Finset.univ.erase R.root, (w x).natAbs * H x

theorem realizes_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (e : Entry N m) (he : Realizes R H w v e) (i : Fin m) :
    (val e.key.cost i).natAbs ≤ subtreeMagnitude R H w v := by
  classical
  rw [← he.2.2.2 i]
  apply (Int.natAbs_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (he.1.entry_le i x ((mem_subtree _ _ _).mp hx))

theorem subtreeMagnitude_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (hv : v ≠ R.root) : subtreeMagnitude R H w v ≤ costMagnitude R H w := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro x hx
  exact Finset.mem_erase.mpr ⟨subtree_ne_root hv ((mem_subtree _ _ _).mp hx), Finset.mem_univ _⟩

theorem nodeRaw_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (hv : v ≠ R.root) (e : Entry N m)
    (he : e ∈ nodeRawEntries R H w m v ((childrenList R v).map (compute R H w m))) (i : Fin m) :
    (val e.key.cost i).natAbs ≤ costMagnitude R H w := by
  exact (realizes_cost_bound R H w v e (nodeRaw_realizes R H w m v _
    (fun u _ e he => compute_realizes R H w m u e he) e he) i).trans
      (subtreeMagnitude_le R H w v hv)

def insideRawEntries (a : Vector Bool m) (base : Vector ℤ m)
    (t : List (Entry N m)) (ts : List (List (Entry N m))) : List (Inside N m) :=
  (t.filter fun e => subsetB e.key.active a).flatMap fun e =>
    (inside a base ts).map fun r => ⟨TreeBudgetSubtreeInteger.add e.key.cost r.cost, e :: r.picks⟩

theorem insideRaw_spec (a : Vector Bool m) (base : Vector ℤ m)
    (t : List (Entry N m)) (ts : List (List (Entry N m))) (r : Inside N m)
    (hr : r ∈ insideRawEntries a base t ts) :
    List.Forall₂ (fun t e => e ∈ t) (t :: ts) r.picks ∧
      ∀ i, val r.cost i = val base i + (r.picks.map fun e => val e.key.cost i).sum := by
  obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hsel, _, hc⟩ := inside_spec _ _ _ b hb
  refine ⟨.cons (List.mem_filter.mp he).1 hsel, ?_⟩
  intro i
  simp only [TreeBudgetSubtreeInteger.add, val_ofFn, List.map_cons, List.sum_cons, hc i]
  ring

theorem roots_cost_spec (ts : List (List (Entry N m))) (r : Root N m)
    (hr : r ∈ roots ts) :
    List.Forall₂ (fun t e => e ∈ t) ts r.picks ∧
      ∀ i, val r.key.cost i = (r.picks.map fun e => val e.key.cost i).sum := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨TreeBudgetSubtreeInteger.rootZero m, []⟩ := by simpa [roots] using hr
    subst r
    exact ⟨.nil, by simp [TreeBudgetSubtreeInteger.rootZero]⟩
  | cons t ts ih =>
    have hh := (List.mem_filter.mp (TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Root.key hr)).1
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hh
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hsel, hc⟩ := ih b hb
    refine ⟨.cons he hsel, ?_⟩
    intro i
    simp [TreeBudgetSubtreeInteger.rootAdd, TreeBudgetSubtreeInteger.add, hc i, add_comm]

def rootsRawEntries (t : List (Entry N m)) (ts : List (List (Entry N m))) : List (Root N m) :=
  t.flatMap fun e => (roots ts).map fun r =>
    ⟨TreeBudgetSubtreeInteger.rootAdd r.key e.key, e :: r.picks⟩

theorem rootsRaw_spec (t : List (Entry N m)) (ts : List (List (Entry N m)))
    (r : Root N m) (hr : r ∈ rootsRawEntries t ts) :
    List.Forall₂ (fun t e => e ∈ t) (t :: ts) r.picks ∧
      ∀ i, val r.key.cost i = (r.picks.map fun e => val e.key.cost i).sum := by
  obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hsel, hc⟩ := roots_cost_spec _ b hb
  refine ⟨.cons he hsel, ?_⟩
  intro i
  simp [TreeBudgetSubtreeInteger.rootAdd, TreeBudgetSubtreeInteger.add, hc i, add_comm]

theorem selected_cost_bound {α : Type} (xs : List α) (tables : α → List (Entry N m))
    (es : List (Entry N m)) (B : α → ℕ) (i : Fin m)
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map tables) es)
    (ht : ∀ x ∈ xs, ∀ e ∈ tables x, (val e.key.cost i).natAbs ≤ B x) :
    ((es.map fun (e : Entry N m) => val e.key.cost i).sum).natAbs ≤ (xs.map B).sum := by
  induction xs generalizing es with
  | nil => cases hsel; simp
  | cons x xs ih =>
    cases hsel with
    | cons he hs =>
      simp only [List.map_cons, List.sum_cons]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (ht x (by simp) _ he)
        (ih _ hs (fun y hy => ht y (by simp [hy]))))

theorem forest_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (xs : List (Fin N)) (es : List (Entry N m)) (i : Fin m)
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es) :
    ((es.map fun (e : Entry N m) => val e.key.cost i).sum).natAbs ≤ (xs.map (subtreeMagnitude R H w)).sum := by
  exact selected_cost_bound xs _ es _ i hsel
    (fun x _ e he => realizes_cost_bound R H w x e (compute_realizes R H w m x e he) i)

theorem sublist_magnitude_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v)) :
    (xs.map (subtreeMagnitude R H w)).sum ≤
      ((childrenList R v).map (subtreeMagnitude R H w)).sum := by
  exact (hx.map _).sum_le_sum (by intro x _; exact Nat.zero_le _)

theorem inside_cost_bound_of_selection (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (v : Fin N) (hv : v ≠ R.root) (xs : List (Fin N))
    (hx : xs.Sublist (childrenList R v)) (q : Vector ℕ m) (hq : q ∈ localCandidates R H m v)
    (r : Inside N m)
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) r.picks)
    (hc : ∀ i, val r.cost i = w v * ((val q i : ℕ) : ℤ) +
      (r.picks.map fun e => val e.key.cost i).sum) (i : Fin m) :
    (val r.cost i).natAbs ≤ costMagnitude R H w := by
  classical
  have hqsum := ((localCandidates_spec R H v q).mp hq).1
  have hqi : val q i ≤ H v := by
    rw [← hqsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hf := (forest_cost_bound R H w xs r.picks i hsel).trans
    (sublist_magnitude_le R H w v xs hx)
  have hb : (w v * ((val q i : ℕ) : ℤ)).natAbs ≤ (w v).natAbs * H v := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left (w v).natAbs hqi
  rw [hc]
  apply ((Int.natAbs_add_le _ _).trans (Nat.add_le_add hb hf)).trans
  have hs := sum_subtree R v (fun x => (w x).natAbs * H x)
  rw [← childrenList_sum] at hs
  change subtreeMagnitude R H w v = (w v).natAbs * H v +
    ((childrenList R v).map (subtreeMagnitude R H w)).sum at hs
  rw [← hs]
  exact subtreeMagnitude_le R H w v hv

theorem roots_cost_bound_of_selection (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R R.root))
    (r : Root N m)
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) r.picks)
    (hc : ∀ i, val r.key.cost i = (r.picks.map fun e => val e.key.cost i).sum) (i : Fin m) :
    (val r.key.cost i).natAbs ≤ costMagnitude R H w := by
  rw [hc]
  apply ((forest_cost_bound R H w xs r.picks i hsel).trans
    (sublist_magnitude_le R H w R.root xs hx)).trans_eq
  exact root_children_sum R (fun x => (w x).natAbs * H x)

theorem inside_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (v : Fin N) (hv : v ≠ R.root) (xs : List (Fin N))
    (hx : xs.Sublist (childrenList R v)) (q : Vector ℕ m) (hq : q ∈ localCandidates R H m v)
    (r : Inside N m) (hr : r ∈ inside (support q)
      (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) (xs.map (compute R H w m))) (i : Fin m) :
    (val r.cost i).natAbs ≤ costMagnitude R H w := by
  have hs := inside_spec _ _ _ r hr
  exact inside_cost_bound_of_selection R H w v hv xs hx q hq r hs.1
    (by simpa using hs.2.2) i

theorem insideRaw_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (v : Fin N) (hv : v ≠ R.root) (u : Fin N) (xs : List (Fin N))
    (hx : (u :: xs).Sublist (childrenList R v)) (q : Vector ℕ m)
    (hq : q ∈ localCandidates R H m v) (r : Inside N m)
    (hr : r ∈ insideRawEntries (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ))
      (compute R H w m u) (xs.map (compute R H w m))) (i : Fin m) :
    (val r.cost i).natAbs ≤ costMagnitude R H w := by
  have hs := insideRaw_spec _ _ _ _ r hr
  exact inside_cost_bound_of_selection R H w v hv (u :: xs) hx q hq r hs.1
    (by simpa using hs.2) i

theorem rootsRaw_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (u : Fin N) (xs : List (Fin N))
    (hx : (u :: xs).Sublist (childrenList R R.root)) (r : Root N m)
    (hr : r ∈ rootsRawEntries (compute R H w m u) (xs.map (compute R H w m))) (i : Fin m) :
    (val r.key.cost i).natAbs ≤ costMagnitude R H w := by
  have hs := rootsRaw_spec _ _ r hr
  exact roots_cost_bound_of_selection R H w (u :: xs) hx r hs.1 hs.2 i

theorem roots_cost_bound (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R R.root))
    (r : Root N m) (hr : r ∈ roots (xs.map (compute R H w m))) (i : Fin m) :
    (val r.key.cost i).natAbs ≤ costMagnitude R H w := by
  have hs := roots_cost_spec _ r hr
  exact roots_cost_bound_of_selection R H w xs hx r hs.1 hs.2 i

theorem realizes_coordinate_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (e : Entry N m) (he : Realizes R H w v e) (i : Fin m) (x : Fin N) :
    matrixVal e.matrix i x ≤ H x := by
  by_cases hx : InSubtree R v x
  · exact he.1.entry_le i x hx
  · rw [he.1.outside i x hx]
    exact Nat.zero_le _

theorem nodeRaw_coordinate_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (e : Entry N m)
    (he : e ∈ nodeRawEntries R H w m v ((childrenList R v).map (compute R H w m)))
    (i : Fin m) (x : Fin N) : matrixVal e.matrix i x ≤ H x :=
  realizes_coordinate_le R H w v e (nodeRaw_realizes R H w m v _
    (fun u _ e he => compute_realizes R H w m u e he) e he) i x

theorem forest_coordinate_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v))
    (es : List (Entry N m))
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es)
    (i : Fin m) (x : Fin N) : (es.map fun e => matrixVal e.matrix i x).sum ≤ H x := by
  classical
  have hn := (childrenList_nodup R v).sublist hx
  obtain ⟨f, hf, hm⟩ := (selected_family xs hn (compute R H w m) es).mp hsel
  have hreal (u : Fin N) (hu : u ∈ xs) := compute_realizes R H w m u (f u) (hm u hu)
  have hchild (u : Fin N) (hu : u ∈ xs) : u ∈ R.children v :=
    (mem_childrenList _ _ _).mp (hx.subset hu)
  rw [← hf, List.map_map, ← List.sum_toFinset _ hn]
  simp only [Function.comp_def]
  by_cases hex : ∃ u ∈ xs, InSubtree R u x
  · obtain ⟨u, hu, hux⟩ := hex
    rw [Finset.sum_eq_single u]
    · exact (hreal u hu).1.entry_le i x hux
    · intro y hy hyu
      apply (hreal y (List.mem_toFinset.mp hy)).1.outside i x
      intro hyx
      exact hyu (child_subtrees_pairwise_disjoint (hchild y (List.mem_toFinset.mp hy))
        (hchild u hu) hyx hux)
    · intro h; exact (h (List.mem_toFinset.mpr hu)).elim
  · have hz : ∀ y ∈ xs.toFinset, matrixVal (f y).matrix i x = 0 := by
      intro y hy
      apply (hreal y (List.mem_toFinset.mp hy)).1.outside i x
      exact fun h => hex ⟨y, List.mem_toFinset.mp hy, h⟩
    rw [Finset.sum_eq_zero hz]
    exact Nat.zero_le _

theorem realizes_root_zero (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (hv : v ≠ R.root) (e : Entry N m) (he : Realizes R H w v e) (i : Fin m) :
    matrixVal e.matrix i R.root = 0 :=
  he.1.outside i R.root (fun hx => subtree_ne_root hv hx rfl)

theorem forest_root_zero (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v))
    (es : List (Entry N m))
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es) (i : Fin m) :
    (es.map fun e => matrixVal e.matrix i R.root).sum = 0 := by
  have hn := (childrenList_nodup R v).sublist hx
  obtain ⟨f, hf, hm⟩ := (selected_family xs hn (compute R H w m) es).mp hsel
  rw [← hf, List.map_map]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
  exact realizes_root_zero R H w u
    ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp (hx.subset hu))).1 (f u)
    (compute_realizes R H w m u (f u) (hm u hu)) i

theorem temp_prefix_coordinate_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v))
    (es : List (Entry N m))
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es)
    (ys : List (Entry N m)) (hy : ys.Sublist es) (i : Fin m) (x : Fin N) :
    (ys.map fun e => matrixVal e.matrix i x).sum ≤ H x :=
  ((hy.map _).sum_le_sum (by intro z _; exact Nat.zero_le _)).trans
    (forest_coordinate_le R H w v xs hx es hsel i x)

theorem costMagnitude_lt_pow (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (T : ℚ) (b U : ℕ)
    (hs : ∀ v, v ≠ R.root → (s v).num.natAbs < 2 ^ b ∧ (s v).den < 2 ^ b)
    (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    costMagnitude R H (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) <
      2^((((N - 1) + 1) * b + 1) + Nat.size (N - 1) + Nat.size U) := by
  classical
  let K := ((N - 1) + 1) * b + 1
  have hb : costMagnitude R H (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) ≤
      (N - 1) * (2 ^ K * U) := by
    calc
      _ ≤ ∑ v ∈ Finset.univ.erase R.root, 2 ^ K * U := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.mul_le_mul
          (TreeBudgetSubtreeResource.prepare_weight_lt_pow R s T b hs v).le
          (hU v (Finset.mem_erase.mp hv).1)
      _ = _ := by simp
  apply hb.trans_lt
  calc
    (N - 1) * (2 ^ K * U) ≤ 2^(Nat.size (N - 1)) * (2 ^ K * U) :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ < 2^(Nat.size (N - 1)) * (2 ^ K * 2^(Nat.size U)) :=
      Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self U) (by positivity)) (by positivity)
    _ = _ := by simp [pow_add, K]; ring

theorem nodeRaw_coordinate_fits (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (m U : ℕ) (hU : ∀ x, x ≠ R.root → H x ≤ U)
    (v : Fin N) (hv : v ≠ R.root) (e : Entry N m)
    (he : e ∈ nodeRawEntries R H w m v ((childrenList R v).map (compute R H w m)))
    (i : Fin m) (x : Fin N) :
    matrixVal e.matrix i x < 2 ^ TreeBudgetSubtreeResource.coordBits U := by
  have hr := nodeRaw_realizes R H w m v _
    (fun u _ e he => compute_realizes R H w m u e he) e he
  apply TreeBudgetSubtreeResource.coordinate_lt_pow
  by_cases hx : x = R.root
  · subst x
    rw [realizes_root_zero R H w v hv e hr i]
    exact Nat.zero_le _
  · exact (realizes_coordinate_le R H w v e hr i x).trans (hU x hx)

theorem temp_prefix_coordinate_fits (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (U : ℕ) (hU : ∀ x, x ≠ R.root → H x ≤ U)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v))
    (es : List (Entry N m))
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es)
    (ys : List (Entry N m)) (hy : ys.Sublist es) (i : Fin m) (x : Fin N) :
    (ys.map fun e => matrixVal e.matrix i x).sum < 2 ^ TreeBudgetSubtreeResource.coordBits U := by
  apply TreeBudgetSubtreeResource.coordinate_lt_pow
  by_cases hroot : x = R.root
  · subst x
    have hh := (hy.map (fun e => matrixVal e.matrix i R.root)).sum_le_sum
      (by intro z _; exact Nat.zero_le _)
    rw [forest_root_zero R H w v xs hx es hsel i] at hh
    exact hh.trans (Nat.zero_le _)
  · exact (temp_prefix_coordinate_le R H w v xs hx es hsel ys hy i x).trans (hU x hroot)

theorem certificate_coordinate_fits (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (w : Fin N → ℤ) (U : ℕ) (hU : ∀ x, x ≠ R.root → H x ≤ U)
    (r : Root N m) (hr : r ∈ roots ((childrenList R R.root).map (compute R H w m)))
    (i : Fin m) (x : Fin N) :
    (certificate R r).row i x < 2 ^ TreeBudgetSubtreeResource.coordBits U := by
  apply TreeBudgetSubtreeResource.coordinate_lt_pow
  by_cases hx : x = R.root
  · simp [certificate, matrixVal, glue, hx]
  · simp only [certificate, matrixVal, glue, val_ofFn, if_neg hx]
    exact (forest_coordinate_le R H w R.root (childrenList R R.root) (.refl _) r.picks
      (roots_selection _ r hr) i x).trans (hU x hx)

end UAVProof.TreeBudgetSubtreeResourceSeed
