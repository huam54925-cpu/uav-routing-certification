import LeanCompletion.UAV.TreeBudgetSubtreeStats
import LeanCompletion.UAV.TreeBudgetSubtreeCompositionBounds

/-! Bounds before and after deduplication. Empty child tables are allowed;
the empty fold has length one. No semantic matrix enumeration is used. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeStats
variable {m N : ℕ}

def tableProduct (ts : List (List (ExecCompactState m))) : ℕ :=
  (ts.map List.length).prod

theorem insideCosts_length_le (a : Vector Bool m) (base : Vector ℚ m)
    (ts : List (List (ExecCompactState m))) :
    (insideCosts a base ts).length ≤ tableProduct ts := by
  induction ts with
  | nil => simp [insideCosts, tableProduct]
  | cons t ts ih =>
    change (insideRaw a t (insideCosts a base ts)).dedup.length ≤ _
    apply (List.dedup_sublist _).length_le.trans
    rw [insideRaw_length]
    exact Nat.mul_le_mul (List.length_filter_le _ _) ih

theorem insideRaw_length_le (a : Vector Bool m) (base : Vector ℚ m)
    (t : List (ExecCompactState m)) (ts : List (List (ExecCompactState m))) :
    (insideRaw a t (insideCosts a base ts)).length ≤ tableProduct (t :: ts) := by
  rw [insideRaw_length]
  exact Nat.mul_le_mul (List.length_filter_le _ _) (insideCosts_length_le a base ts)

theorem rootFold_length_le (ts : List (List (ExecCompactState m))) :
    (rootFold ts).length ≤ tableProduct ts := by
  induction ts with
  | nil => simp [rootFold, tableProduct]
  | cons t ts ih =>
    change ((rootRaw t (rootFold ts)).filter rootCapB).dedup.length ≤ _
    apply (List.dedup_sublist _).length_le.trans
    apply (List.length_filter_le _ _).trans
    rw [rootRaw_length]
    exact Nat.mul_le_mul_left _ ih

theorem rootRaw_length_le (t : List (ExecCompactState m))
    (ts : List (List (ExecCompactState m))) :
    (rootRaw t (rootFold ts)).length ≤ tableProduct (t :: ts) := by
  rw [rootRaw_length]
  exact Nat.mul_le_mul_left _ (rootFold_length_le ts)

def nodeRaw (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) : List (ExecCompactState m) :=
  (localCandidates R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn fun i => linearWeight R s v * ((val q i : ℕ) : ℚ)) ts).map
        fun b => ⟨support q, b⟩

theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    omega

theorem nodeRaw_length_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeRaw R H s m v ts).length ≤
      (localCandidates R H m v).length * tableProduct ts := by
  apply length_flatMap_le
  intro q _
  simpa using insideCosts_length_le (support q)
    (Vector.ofFn fun i => linearWeight R s v * ((val q i : ℕ) : ℚ)) ts

theorem nodeTable_length_le (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeTable R H s m v ts).length ≤
      (localCandidates R H m v).length * tableProduct ts :=
  (List.dedup_sublist _).length_le.trans (nodeRaw_length_le R H s m v ts)

def columnFactor (m h : ℕ) : ℕ := max 1 (columnCount m h)

noncomputable def columnProduct (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (v : Fin N) : ℕ := ∏ x ∈ subtree R v, columnFactor m (H x)

noncomputable def globalProduct (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) : ℕ := ∏ x ∈ Finset.univ.erase R.root, columnFactor m (H x)

theorem prod_subtree {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (v : V) (f : V → ℕ) :
    (∏ x ∈ subtree R v, f x) = f v * ∏ u ∈ R.children v, ∏ x ∈ subtree R u, f x := by
  classical
  rw [subtree_eq_insert_children_union, Finset.prod_insert]
  · congr 1
    apply Finset.prod_biUnion
    intro u hu w hw hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hne (child_subtrees_pairwise_disjoint hu hw
      ((mem_subtree _ _ _).mp hx) ((mem_subtree _ _ _).mp hy))
  · simp only [Finset.mem_biUnion, mem_subtree, not_exists, not_and]
    exact fun u hu => top_not_child_subtree hu

theorem columnProduct_split (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (v : Fin N) : columnProduct R H m v =
      columnFactor m (H v) * ∏ u ∈ R.children v, columnProduct R H m u :=
  prod_subtree R v _

theorem localCandidates_length_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (v : Fin N) : (localCandidates R H m v).length ≤ columnFactor m (H v) := by
  apply (List.length_filter_le _ _).trans
  rw [compositionsV_length]
  exact le_max_right _ _

theorem tableProduct_children_le (R : RootedTree (Fin N)) (v : Fin N)
    (ts : Fin N → List (ExecCompactState m)) (B : Fin N → ℕ)
    (h : ∀ u ∈ R.children v, (ts u).length ≤ B u) :
    tableProduct ((childrenList R v).map ts) ≤ ∏ u ∈ R.children v, B u := by
  unfold tableProduct
  rw [List.map_map, ← List.prod_toFinset _ (childrenList_nodup R v), childrenList_toFinset]
  exact Finset.prod_le_prod' h

theorem computeCompact_length_le_columnProduct (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (m : ℕ) (v : Fin N) :
    (computeCompact R H s m v).length ≤ columnProduct R H m v := by
  rw [computeCompact_eq, columnProduct_split]
  apply (nodeTable_length_le R H s m v _).trans
  apply Nat.mul_le_mul (localCandidates_length_le R H m v)
  apply tableProduct_children_le
  intro u hu
  exact computeCompact_length_le_columnProduct R H s m u
termination_by R.rank v
decreasing_by exact R.child_rank hu

theorem columnProduct_le_globalProduct (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (v : Fin N) (hv : v ≠ R.root) :
    columnProduct R H m v ≤ globalProduct R H m := by
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro x hx
    exact Finset.mem_erase.mpr ⟨subtree_ne_root hv ((mem_subtree _ _ _).mp hx), Finset.mem_univ x⟩
  · intro x _ _; exact le_max_left _ _

theorem nodeRaw_length_le_columnProduct (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (m : ℕ) (v : Fin N) :
    (nodeRaw R H s m v ((childrenList R v).map (computeCompact R H s m))).length ≤
      columnProduct R H m v := by
  rw [columnProduct_split]
  apply (nodeRaw_length_le R H s m v _).trans
  exact Nat.mul_le_mul (localCandidates_length_le R H m v)
    (tableProduct_children_le R v _ _ (fun u _ => computeCompact_length_le_columnProduct R H s m u))

theorem root_children_product (R : RootedTree (Fin N)) (H : Fin N → ℕ) (m : ℕ) :
    (∏ u ∈ R.children R.root, columnProduct R H m u) = globalProduct R H m := by
  classical
  have hn : R.root ∉ (R.children R.root).biUnion (subtree R) := by
    simp only [Finset.mem_biUnion, not_exists, not_and, mem_subtree]
    exact fun u hu => top_not_child_subtree hu
  have he : Finset.univ.erase R.root = (R.children R.root).biUnion (subtree R) := by
    rw [← subtree_root R, subtree_eq_insert_children_union, Finset.erase_insert hn]
  unfold globalProduct
  rw [he, Finset.prod_biUnion]
  · rfl
  · intro u hu w hw hne
    exact Finset.disjoint_left.mpr (fun x hx hy => hne (child_subtrees_pairwise_disjoint hu hw
      ((mem_subtree _ _ _).mp hx) ((mem_subtree _ _ _).mp hy)))

theorem rootFold_length_le_globalProduct (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (m : ℕ) :
    (rootFold ((childrenList R R.root).map (computeCompact R H s m))).length ≤ globalProduct R H m := by
  rw [← root_children_product]
  exact (rootFold_length_le _).trans (tableProduct_children_le R R.root _ _
    (fun u _ => computeCompact_length_le_columnProduct R H s m u))

theorem columnProduct_pos (R : RootedTree (Fin N)) (H : Fin N → ℕ) (m : ℕ) (v : Fin N) :
    1 ≤ columnProduct R H m v := Finset.one_le_prod' (fun _ _ => le_max_left _ _)

theorem globalProduct_pos (R : RootedTree (Fin N)) (H : Fin N → ℕ) (m : ℕ) :
    1 ≤ globalProduct R H m := Finset.one_le_prod' (fun _ _ => le_max_left _ _)

end UAVProof.TreeBudgetSubtreeExecutable
