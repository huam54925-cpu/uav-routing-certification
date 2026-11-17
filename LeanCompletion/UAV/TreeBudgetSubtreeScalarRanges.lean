import LeanCompletion.UAV.TreeBudgetSubtreeScalarBounds
import LeanCompletion.UAV.TreeBudgetSubtreeResourceRealizes

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeBudgetSubtreeAutoScaleSeed TreeFlowExistence
open TreeBudgetSubtreePre (Input serviceBits massBits)
open TreeBudgetSubtreeResource
variable {N m : Nat}

theorem mapC_length_le_ops {α β : Type} (f : α → Counted β) (xs : List α) :
    (mapC f xs).value.length ≤ (mapC f xs).ops := by
  rw [mapC_value, List.length_map, mapC_ops, mapWork_eq]; omega

theorem filterC_input_le_ops {α : Type} (p : α → Counted Bool) (xs : List α) :
    xs.length ≤ (filterC p xs).ops := by rw [filterC_ops]; omega

theorem flatMapC_length_le_ops {α β : Type} (f : α → Counted (List β)) (xs : List α) :
    (flatMapC f xs).value.length ≤ (flatMapC f xs).ops := by
  induction xs with
  | nil => simp [flatMapC]
  | cons x xs ih =>
    simp only [flatMapC, (appendC_spec _ _).1, (appendC_spec _ _).2, List.length_append]
    omega

theorem dedupTraceC_input_le_ops {α κ : Type} (key : α → κ)
    (eq : κ → κ → Counted Bool) (xs : List α) : xs.length ≤ (dedupTraceC key eq xs).ops := by
  induction xs <;> simp_all only [dedupTraceC, List.length_nil, List.length_cons] <;> omega

theorem dedupTraceC_output_le_input {α κ : Type} (key : α → κ)
    (eq : κ → κ → Counted Bool) (xs : List α) :
    (dedupTraceC key eq xs).value.value.length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupTraceC]
  | cons x xs ih =>
    simp only [dedupTraceC, List.length_cons]
    split <;> (try simp only [List.length_cons]) <;> omega

theorem dedupC_lengths {α κ : Type} (key : α → κ)
    (eq : κ → κ → Counted Bool) (xs : List α) :
    (dedupC key eq xs).value.value.length ≤ xs.length ∧ xs.length ≤ (dedupC key eq xs).ops := by
  exact ⟨dedupTraceC_output_le_input key eq xs, by
    have h := dedupTraceC_input_le_ops key eq xs
    dsimp [dedupC]; omega⟩

/-- Every prefix/suffix cursor of a materialized list is covered by its paid
construction. The proof uses the actual instruction count, never a capacity axiom. -/
theorem constructed_cursor_bits {α : Type} (xs : List α) (c k : Nat)
    (hbuild : xs.length ≤ c) (hk : k ≤ xs.length) : k.size ≤ c :=
  (TreeBudgetSubtreePre.size_self_le k).trans (hk.trans hbuild)

theorem tabulateC_index_bits {α : Type} {n : Nat} (f : Fin n → Counted α) (i : Nat)
    (hi : i ≤ n) : i.size ≤ (tabulateC f).ops := by
  have h := (TreeBudgetSubtreePre.size_self_le i).trans hi
  rw [tabulateC_ops]; omega

/-- A callback's instructions occur in the containing map; this also transports
the construction/cursor certificate through outer list controls. -/
theorem mapC_callback_le {α β : Type} (f : α → Counted β) (xs : List α)
    (x : α) (hx : x ∈ xs) : (f x).ops ≤ (mapC f xs).ops := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [mapC]; omega
    · have hh := ih hx; simp only [mapC]; omega

theorem collectC_callback_le {α : Type} (rs : List (Counted (ResourceResult α)))
    (r : Counted (ResourceResult α)) (hr : r ∈ rs) : r.ops ≤ (collectC rs).ops := by
  have hh : r.ops ≤ (rs.map Counted.ops).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨r, hr, rfl⟩)
  dsimp [collectC]; omega

/-- Conservative padding includes sign, arithmetic carry, all indices and the
paid list-construction/control bound. It is polynomial in the proven DP census. -/
def dpWidth (N m b h c : Nat) : Nat := (N+2)*(b+h+2)+N+m+c+4

theorem prepared_weight_bits (R : RootedTree (Fin N)) (s : Fin N → Rat) (T : Rat)
    (b : Nat) (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (v : Fin N) :
    (val (prepare R s T).weight v).natAbs.size ≤ N*b+1 := by
  have hn : 1 ≤ N := Nat.zero_lt_of_lt R.root.isLt
  have hh := TreeBudgetSubtreeResource.prepare_weight_lt_pow R s T b
    (fun x _ => ⟨Nat.size_le.mp (hs x).1, Nat.size_le.mp (hs x).2⟩) v
  have he : N-1+1=N := by omega
  simpa [he] using Nat.size_le.mpr hh

theorem prepared_budget_bits (R : RootedTree (Fin N)) (s : Fin N → Rat) (T : Rat)
    (b : Nat) (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b)
    (hT : TreeBudgetSubtreePre.RatFits T b) : (prepare R s T).budget.natAbs.size ≤ N*b := by
  have hn : 1 ≤ N := Nat.zero_lt_of_lt R.root.isLt
  have hh := TreeBudgetSubtreeResource.prepare_budget_lt_pow R s T b
    (fun x _ => Nat.size_le.mp (hs x).2) (Nat.size_le.mp hT.1)
  have he : N-1+1=N := by omega
  simpa [he] using Nat.size_le.mpr hh

theorem magnitude_bits (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h) :
    (costMagnitude R H (val (prepare R s T).weight)).size ≤ N*b+N+h+2 := by
  have hh := costMagnitude_lt_pow R H s T b (2^h)
    (fun x _ => ⟨Nat.size_le.mp (hs x).1, Nat.size_le.mp (hs x).2⟩)
    (fun x _ => (Nat.size_le.mp (hH x)).le)
  have hn : 1 ≤ N := Nat.zero_lt_of_lt R.root.isLt
  have hsize := TreeBudgetSubtreePre.size_self_le (N-1)
  apply (Nat.size_le.mpr hh).trans
  have he : N-1+1=N := by omega
  simp only [he, Nat.size_pow]
  omega

theorem magnitude_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (z : Int) (hz : z.natAbs ≤ costMagnitude R H (val (prepare R s T).weight)) :
    z.natAbs.size+1 ≤ dpWidth N m b h c := by
  have hh := (Nat.size_le_size hz).trans (magnitude_bits R H s T b h hs hH)
  unfold dpWidth; nlinarith

/-- Covers rejected root pairs as well as retained states, before the cap test. -/
theorem root_raw_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (u : Fin N) (xs : List (Fin N)) (hx : (u::xs).Sublist (childrenList R R.root))
    (r : Root N m) (hr : r ∈ rootsRawEntries (compute R H (val (prepare R s T).weight) m u)
      (xs.map (compute R H (val (prepare R s T).weight) m))) (i : Fin m) :
    (val r.key.cost i).natAbs.size+1 ≤ dpWidth N m b h c :=
  magnitude_padded R H s T b h c hs hH _
    (rootsRaw_cost_bound R H (val (prepare R s T).weight) u xs hx r hr i)

theorem inside_raw_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (hv : v ≠ R.root) (u : Fin N) (xs : List (Fin N))
    (hx : (u::xs).Sublist (childrenList R v)) (q : Vector Nat m)
    (hq : q ∈ localCandidates R H m v) (r : Inside N m)
    (hr : r ∈ insideRawEntries (support q)
      (Vector.ofFn fun i => val (prepare R s T).weight v * ((val q i : Nat) : Int))
      (compute R H (val (prepare R s T).weight) m u)
      (xs.map (compute R H (val (prepare R s T).weight) m))) (i : Fin m) :
    (val r.cost i).natAbs.size+1 ≤ dpWidth N m b h c :=
  magnitude_padded R H s T b h c hs hH _
    (insideRaw_cost_bound R H (val (prepare R s T).weight) v hv u xs hx q hq r hr i)

theorem node_raw_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (hv : v ≠ R.root) (e : Entry N m)
    (he : e ∈ nodeRawEntries R H (val (prepare R s T).weight) m v
      ((childrenList R v).map (compute R H (val (prepare R s T).weight) m))) (i : Fin m) :
    (val e.key.cost i).natAbs.size+1 ≤ dpWidth N m b h c :=
  magnitude_padded R H s T b h c hs hH _
    (nodeRaw_cost_bound R H (val (prepare R s T).weight) m v hv e he i)

theorem candidate_product_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) (b h c : Nat)
    (hs : ∀ v, TreeBudgetSubtreePre.RatFits (s v) b) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (q : Vector Nat m) (hq : q ∈ localCandidates R H m v) (i : Fin m) :
    (val (prepare R s T).weight v * ((val q i : Nat) : Int)).natAbs.size ≤ dpWidth N m b h c := by
  have hqsum := ((localCandidates_spec R H v q).mp hq).1
  have hqi : val q i ≤ H v := by
    rw [← hqsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hqbits := (Nat.size_le_size hqi).trans (hH v)
  have hw := prepared_weight_bits R s T b hs v
  have hp := TreeBudgetSubtreePre.size_mul (val (prepare R s T).weight v).natAbs (val q i)
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  unfold dpWidth
  nlinarith

theorem roots_used_le_one (ts : List (List (Entry N m))) (r : Root N m)
    (hr : r ∈ roots ts) (i : Fin m) : val r.key.used i ≤ 1 := by
  cases ts with
  | nil => simp only [roots, List.mem_singleton] at hr; subst r
           simp [TreeBudgetSubtreeInteger.rootZero]
  | cons t ts =>
    have hcap := (List.mem_filter.mp (TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Root.key hr)).2
    exact of_decide_eq_true ((List.all_eq_true.mp hcap) i (List.mem_finRange i))

theorem root_add_used_le_two (ts : List (List (Entry N m))) (r : Root N m)
    (hr : r ∈ roots ts) (e : Entry N m) (i : Fin m) :
    val (rootAddC r.key e.key).value.used i ≤ 2 := by
  have hu := roots_used_le_one ts r hr i
  rw [rootAddC_value]
  simp only [TreeBudgetSubtreeInteger.rootAdd, val_ofFn]
  have hb : bit (val e.key.active i) ≤ 1 := by cases val e.key.active i <;> decide
  omega

theorem matrix_partial_padded (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (b h c : Nat) (hH : ∀ v, (H v).size ≤ h)
    (v : Fin N) (xs : List (Fin N)) (hx : xs.Sublist (childrenList R v))
    (es : List (Entry N m))
    (hsel : List.Forall₂ (fun t e => e ∈ t) (xs.map (compute R H w m)) es)
    (ys : List (Entry N m)) (hy : ys.Sublist es) (i : Fin m) (x : Fin N) :
    (ys.map fun e => TreeBudgetSubtreeWitness.matrixVal e.matrix i x).sum.size ≤ dpWidth N m b h c := by
  have hh := (Nat.size_le_size
    (temp_prefix_coordinate_le R H w v xs hx es hsel ys hy i x)).trans (hH x)
  unfold dpWidth; nlinarith

end UAVProof.TreeBudgetSubtreeScalar
