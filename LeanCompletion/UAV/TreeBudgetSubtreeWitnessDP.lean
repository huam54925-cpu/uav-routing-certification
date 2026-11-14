import LeanCompletion.UAV.TreeBudgetSubtreeDP
import LeanCompletion.UAV.TreeBudgetCertificate

/-! Explicit matrix payloads. Deduplication compares only the state key and
retains the rightmost representative, including at intermediate folds. -/
namespace UAVProof.TreeBudgetSubtreeWitness
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
variable {N m : ℕ}

def dedupKey {α β : Type} [DecidableEq β] (key : α → β) : List α → List α
  | [] => []
  | x :: xs => let r := dedupKey key xs; if key x ∈ r.map key then r else x :: r

theorem dedupKey_map {α β : Type} [DecidableEq β] (key : α → β) (xs : List α) :
    (dedupKey key xs).map key = (xs.map key).dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [dedupKey]
    split <;> simp_all [List.dedup_cons']

theorem mem_of_mem_dedupKey {α β : Type} [DecidableEq β] (key : α → β)
    {xs : List α} {x : α} (hx : x ∈ dedupKey key xs) : x ∈ xs := by
  induction xs with
  | nil => simp [dedupKey] at hx
  | cons y ys ih =>
    simp only [dedupKey] at hx
    split at hx
    · exact List.mem_cons_of_mem y (ih hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem y (ih hx)

abbrev Matrix (N m : ℕ) := Vector (Vector ℕ N) m
def matrixVal (n : Matrix N m) (i : Fin m) (x : Fin N) : ℕ := val (val n i) x

structure Entry (N m : ℕ) where
  key : ExecCompactState m
  matrix : Matrix N m
  deriving Inhabited

structure Inside (N m : ℕ) where
  cost : Vector ℚ m
  picks : List (Entry N m)

def inside (a : Vector Bool m) (base : Vector ℚ m) :
    List (List (Entry N m)) → List (Inside N m)
  | [] => [⟨base, []⟩]
  | t :: ts => dedupKey Inside.cost ((t.filter fun e => subsetB e.key.active a).flatMap fun e =>
      (inside a base ts).map fun r => ⟨addCost e.key.cost r.cost, e :: r.picks⟩)

theorem inside_keys (a : Vector Bool m) (base : Vector ℚ m) (ts : List (List (Entry N m))) :
    (inside a base ts).map Inside.cost = insideCosts a base (ts.map (List.map Entry.key)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [inside, dedupKey_map, insideCosts, List.map_cons, List.map_flatMap,
      List.map_map, List.filter_map, List.flatMap_map, Function.comp_def]
    congr 1
    apply List.flatMap_congr
    intro e _
    rw [← ih, List.map_map]
    rfl

theorem inside_spec (a : Vector Bool m) (base : Vector ℚ m) (ts : List (List (Entry N m)))
    (r : Inside N m) (hr : r ∈ inside a base ts) :
    List.Forall₂ (fun t e => e ∈ t) ts r.picks ∧
      (∀ e ∈ r.picks, subsetB e.key.active a = true) ∧
      ∀ i, val r.cost i = val base i + (r.picks.map fun e => val e.key.cost i).sum := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨base, []⟩ := by simpa [inside] using hr
    subst r
    exact ⟨.nil, by simp, by simp⟩
  | cons t ts ih =>
    have hh := mem_of_mem_dedupKey Inside.cost hr
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
      simp only [addCost, val_ofFn, List.map_cons, List.sum_cons, hc i]
      ring

def glue (v : Fin N) (q : Vector ℕ m) (es : List (Entry N m)) : Matrix N m :=
  Vector.ofFn fun i => Vector.ofFn fun x =>
    if x = v then val q i else (es.map fun e => matrixVal e.matrix i x).sum

theorem glue_eq (R : RootedTree (Fin N)) (v : Fin N) (q : Vector ℕ m)
    (es : List (Entry N m)) (f : Fin N → Entry N m) (hf : (childrenList R v).map f = es) :
    matrixVal (glue v q es) = glueMatrix R v (val q) (fun u => matrixVal (f u).matrix) := by
  funext i x
  simp only [matrixVal, glue, val_ofFn, glueMatrix]
  rw [← hf, List.map_map, childrenList_sum]
  rfl

def node (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) : List (Entry N m) :=
  dedupKey Entry.key ((localCandidates R H m v).flatMap fun q =>
    (inside (support q) (Vector.ofFn fun i => linearWeight R s v * ((val q i : ℕ) : ℚ)) ts).map
      fun r => ⟨⟨support q, r.cost⟩, glue v q r.picks⟩)

theorem node_keys (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) :
    (node R H s m v ts).map Entry.key = nodeTable R H s m v (ts.map (List.map Entry.key)) := by
  simp only [node, nodeTable, dedupKey_map, List.map_flatMap, List.map_map, Function.comp_def]
  congr 1
  apply List.flatMap_congr
  intro q _
  rw [← inside_keys, List.map_map]
  rfl

def compute (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : List (Entry N m) :=
  node R H s m v ((childrenList R v).attach.map fun u => compute R H s m u.val)
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem compute_keys (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : (compute R H s m v).map Entry.key = computeCompact R H s m v := by
  rw [compute, node_keys, computeCompact]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro u _
  exact compute_keys R H s m u.val
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

def Realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (v : Fin N) (e : Entry N m) : Prop :=
  PartialValid R H m v (matrixVal e.matrix) ∧
    RootChildCap R v (fun i => matrixVal e.matrix i v) ∧
    (∀ i, val e.key.active i = true ↔ 0 < matrixVal e.matrix i v) ∧
    ∀ i, subtreeLinearCost R s v (matrixVal e.matrix i) = val e.key.cost i

theorem node_realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (tables : Fin N → List (Entry N m))
    (ht : ∀ u ∈ R.children v, ∀ e ∈ tables u, Realizes R H s u e)
    (e : Entry N m) (he : e ∈ node R H s m v ((childrenList R v).map tables)) :
    Realizes R H s v e := by
  have hh := mem_of_mem_dedupKey Entry.key he
  simp only [List.mem_flatMap, List.mem_map] at hh
  obtain ⟨q, hq, r, hr, rfl⟩ := hh
  obtain ⟨hsel, hs, hc⟩ := inside_spec _ _ _ r hr
  obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R v) tables r.picks).mp hsel
  have hv : ∀ u ∈ R.children v, Realizes R H s u (f u) := fun u hu =>
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
    rw [subtreeLinearCost, sum_subtree, glueMatrix_top]
    have hh : (∑ u ∈ R.children v, ∑ x ∈ subtree R u,
        linearWeight R s x * (glueMatrix R v (val q) (fun u => matrixVal (f u).matrix) i x : ℚ)) =
        ∑ u ∈ R.children v, val (f u).key.cost i := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        _ = subtreeLinearCost R s u (matrixVal (f u).matrix i) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [glueMatrix_child (val q) hn hu ((mem_subtree _ _ _).mp hx)]
        _ = _ := (hv u hu).2.2.2 i
    rw [hh]
    have hc' := hc i
    rw [← hf, List.map_map, childrenList_sum] at hc'
    simpa using hc'.symm

theorem compute_realizes (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (e : Entry N m) (he : e ∈ compute R H s m v) : Realizes R H s v e := by
  rw [compute, List.attach_map_val] at he
  apply node_realizes R H s m v (compute R H s m) ?_ e he
  intro u hu e he
  exact compute_realizes R H s m u e he
termination_by R.rank v
decreasing_by exact R.child_rank hu

structure Root (N m : ℕ) where
  key : ExecRootState m
  picks : List (Entry N m)

def roots : List (List (Entry N m)) → List (Root N m)
  | [] => [⟨rootZero m, []⟩]
  | t :: ts => dedupKey Root.key
      ((t.flatMap fun e => (roots ts).map fun r => ⟨rootAdd r.key e.key, e :: r.picks⟩).filter
        fun r => rootCapB r.key)

theorem roots_keys (ts : List (List (Entry N m))) :
    (roots ts).map Root.key = rootFold (ts.map (List.map Entry.key)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [roots, dedupKey_map, List.map_cons, rootFold]
    have hh : ((t.flatMap fun e => (roots ts).map fun r =>
        (⟨rootAdd r.key e.key, e :: r.picks⟩ : Root N m)).map Root.key) =
        (t.map Entry.key).flatMap (fun e => (rootFold (ts.map (List.map Entry.key))).map
          fun b => rootAdd b e) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map]
      apply List.flatMap_congr
      intro e _
      rw [← ih, List.map_map]
      rfl
    rw [← hh, List.filter_map]
    rfl

theorem roots_spec (ts : List (List (Entry N m))) (r : Root N m) (hr : r ∈ roots ts) :
    List.Forall₂ (fun t e => e ∈ t) ts r.picks ∧
      (∀ i, val r.key.used i = (r.picks.map fun e => bit (val e.key.active i)).sum) ∧
      ∀ i, val r.key.cost i = (r.picks.map fun e => val e.key.cost i).sum := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨rootZero m, []⟩ := by simpa [roots] using hr
    subst r
    exact ⟨.nil, by simp [rootZero], by simp [rootZero, zeroCost]⟩
  | cons t ts ih =>
    have hh := (List.mem_filter.mp (mem_of_mem_dedupKey Root.key hr)).1
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hh
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hsel, hu, hc⟩ := ih b hb
    refine ⟨.cons he hsel, ?_, ?_⟩
    · intro i; simp [rootAdd, hu i, Nat.add_comm]
    · intro i; simp [rootAdd, addCost, hc i, add_comm]

def certificate (R : RootedTree (Fin N)) (r : Root N m) : TreeBudgetCertificate.Certificate (Fin N) :=
  ⟨m, matrixVal (glue R.root (Vector.ofFn fun _ => 0) r.picks), fun _ => 1⟩

def solve (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    Option (TreeBudgetCertificate.Certificate (Fin N)) :=
  ((roots ((childrenList R R.root).map (compute R H s m))).find? fun r => acceptRootB T r.key).map
    (certificate R)

theorem certificate_sound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) (r : Root N m)
    (hr : r ∈ roots ((childrenList R R.root).map (compute R H s m)))
    (ha : acceptRootB T r.key = true) :
    TreeBudgetCertificate.checkCertificate R H m s T (certificate R r) = true := by
  classical
  obtain ⟨hsel, hused, hcost⟩ := roots_spec _ r hr
  obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R R.root)
    (compute R H s m) r.picks).mp hsel
  have hv : ∀ u ∈ R.children R.root, Realizes R H s u (f u) := fun u hu =>
    compute_realizes R H s m u (f u) (hm u ((mem_childrenList _ _ _).mpr hu))
  have hvalid := fun u hu => (hv u hu).1
  let n := glueMatrix R R.root (fun _ : Fin m => 0) (fun u => matrixVal (f u).matrix)
  have he {u x : Fin N} (hu : u ∈ R.children R.root) (hx : InSubtree R u x) (i) :
      n i x = matrixVal (f u).matrix i x := glueMatrix_child _ hvalid hu hx i
  have hc : ∀ x, x ≠ R.root → (∑ i, n i x) = H x := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (subtree_cases (root_subtree R x)).resolve_left hx
    simpa only [he hu hxu] using (hvalid u hu).column x hxu
  have htop (u : Fin N) (hu : u ∈ R.children R.root) (i : Fin m) :
      matrixVal (f u).matrix i u = bit (val (f u).key.active i) := by
    have hcap := (hv u hu).2.1 ((R.mem_children _ _).mp hu).2 i
    have hac := (hv u hu).2.2.1 i
    cases hb : val (f u).key.active i <;> simp [hb, bit] at * <;> omega
  have hdeg : ∀ i, TreeBudgetRow.rootDegree R (n i) = 1 := by
    intro i
    have hu := hused i
    rw [← hf, List.map_map, childrenList_sum] at hu
    rw [((acceptRootB_spec _ _).mp ha i).1] at hu
    unfold TreeBudgetRow.rootDegree
    rw [hu]
    apply Finset.sum_congr rfl
    intro u hu
    exact (he hu .self i).trans (htop u hu i)
  have hanc : ∀ i, TreeBudgetRow.AncestorClosed R (n i) := by
    intro i x hx hp hparent
    obtain ⟨u, hu, hxu⟩ := (subtree_cases (root_subtree R x)).resolve_left hx
    have hne : x ≠ u := by
      intro heq; subst x
      exact hparent ((R.mem_children _ _).mp hu).2
    rw [he hu (parent_mem_subtree_of_ne_top hxu hne)]
    exact (hvalid u hu).ancestor i x hxu hne (by simpa only [he hu hxu] using hp)
  have hbudget : ∀ i, TreeBudgetRow.rowCost R (n i) s ≤ T := by
    intro i
    rw [rowCost_eq_sum_root_subtrees]
    have hh : (∑ u ∈ R.children R.root, subtreeCost R s u (n i)) = val r.key.cost i := by
      rw [hcost i, ← hf, List.map_map, childrenList_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hec := (hv u hu).2.2.2 i
      rw [subtreeLinearCost_eq R s u ((R.mem_children _ _).mp hu).1] at hec
      simp only [parentCharge, ((R.mem_children _ _).mp hu).2, if_true, zero_mul, add_zero] at hec
      exact (subtreeCost_congr R s u (fun x hx => he hu hx i)).trans hec
    rw [hh]
    exact ((acceptRootB_spec _ _).mp ha i).2
  rw [TreeBudgetCertificate.checkCertificate_eq_true_iff]
  unfold TreeBudgetCertificate.Valid certificate
  rw [glue_eq R R.root (Vector.ofFn fun _ => 0) r.picks f hf]
  have hz : val (Vector.ofFn (fun _ : Fin m => (0 : ℕ))) = fun _ => 0 := by
    funext i; simp
  rw [hz]
  change (∀ i, TreeBudgetCertificate.RowValid R H s T (n i)) ∧
    (∑ _ : Fin m, 1) = m ∧ ∀ x, x ≠ R.root → (∑ i, 1 * n i x) = H x
  refine ⟨?_, by simp, by simpa using hc⟩
  intro i
  refine ⟨by simp [n], ?_, ?_, hanc i, ?_⟩
  · intro x hx
    rw [← hc x hx]
    exact Finset.single_le_sum (f := fun j => n j x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · rw [TreeBudgetPatterns.rootCount_eq]; exact hdeg i
  · rw [TreeBudgetPatterns.cost_eq]; exact hbudget i

theorem solve_isSome (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : (solve R H s m T).isSome = checkCompact R H s m T := by
  have ht : ((childrenList R R.root).map (compute R H s m)).map (List.map Entry.key) =
      (childrenList R R.root).map (computeCompact R H s m) := by
    simp only [List.map_map, Function.comp_def, compute_keys]
  unfold solve checkCompact
  dsimp only
  rw [← ht, ← roots_keys, List.any_map]
  simp [List.isSome_find?, Function.comp_def]

theorem solve_sound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) (c : TreeBudgetCertificate.Certificate (Fin N))
    (hc : solve R H s m T = some c) : TreeBudgetCertificate.checkCertificate R H m s T c = true := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hc
  have ha := List.find?_some hr
  exact certificate_sound R H s m T r (List.mem_of_find?_eq_some hr) ha

theorem solve_none_iff (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : solve R H s m T = none ↔ ¬ TreeBudgetMatrix.MatrixFeasible R H m s T := by
  rw [← checkCompact_eq_false_iff R H s m T, ← solve_isSome]
  cases solve R H s m T <;> simp

theorem solve_size (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) (c : TreeBudgetCertificate.Certificate (Fin N))
    (hc : solve R H s m T = some c) : c.size = m := by
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp hc
  rfl

theorem solve_exact_iff (R : RootedTree (Fin N)) (H d : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (hd : SupportExactFeasibility.HasDegrees R.root d m (edgeFlow R H)) :
    (solve R H s m T).isSome = true ↔
      SupportExactFeasibility.ExactFeasible R.root (edgeFlow R H) d m s T := by
  rw [solve_isSome]
  exact checkCompact_exact_iff R H d s m T hd

end UAVProof.TreeBudgetSubtreeWitness
