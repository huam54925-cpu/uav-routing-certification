import LeanCompletion.UAV.TreeBudgetSubtreeResourceStats

/-! Exact source-level matrix and list census. Raw node entries are a proof view;
the executor does not rerun this view to obtain counters. -/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeStats TreeBudgetSubtreeIntegerWitnessSeed
variable {N m : ℕ}

theorem inside_selection (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) (r : Inside N m) (hr : r ∈ inside a base ts) :
    List.Forall₂ (fun t e => e ∈ t) ts r.picks := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨base, []⟩ := by simpa [inside] using hr
    subst r
    exact .nil
  | cons t ts ih =>
    have hh := TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Inside.cost hr
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hh
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    exact .cons (List.mem_filter.mp he).1 (ih b hb)

theorem roots_selection (ts : List (List (Entry N m))) (r : Root N m)
    (hr : r ∈ roots ts) : List.Forall₂ (fun t e => e ∈ t) ts r.picks := by
  induction ts generalizing r with
  | nil =>
    have he : r = ⟨TreeBudgetSubtreeInteger.rootZero m, []⟩ := by simpa [roots] using hr
    subst r
    exact .nil
  | cons t ts ih =>
    have hh := TreeBudgetSubtreeWitness.mem_of_mem_dedupKey Root.key hr
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp (List.mem_filter.mp hh).1
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    exact .cons he (ih b hb)

def nodeRawEntries (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) : List (Entry N m) :=
  (localCandidates R H m v).flatMap fun q =>
    (inside (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts).map
      fun r => ⟨⟨support q, r.cost⟩, glue v q r.picks⟩

def rawCount (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) : ℕ :=
  (nodeRawEntries R H w m v ((childrenList R v).map (compute R H w m))).length

def Charges (N m : ℕ) (s : DPStats) (p : PayloadStats) (a d c : ℕ) : Prop :=
  p.matrices = a ∧ p.matrixCells = m * N * a ∧
  p.columnReads = m * a ∧ p.childReads = m * (N - 1) * d ∧
  p.natAdds = m * (N - 1) * d ∧ p.tempCells = m * (N - 1) * d ∧
  p.pickCons = s.insidePairs + s.rootPairs ∧ p.rootZeroCells = m * c

theorem charges_add {s t : DPStats} {p q : PayloadStats} {a d c b e f : ℕ}
    (hs : Charges N m s p a d c) (ht : Charges N m t q b e f) :
    Charges N m (s.add t) (p.add q) (a + b) (d + e) (c + f) := by
  simp only [Charges, DPStats.add, PayloadStats.add, Nat.mul_add] at *
  omega

theorem charges_sum {α : Type} (xs : List α) (s : α → DPStats) (p : α → PayloadStats)
    (a d c : α → ℕ) (h : ∀ x ∈ xs, Charges N m (s x) (p x) (a x) (d x) (c x)) :
    Charges N m (sumStats (xs.map s)) (sumPayload (xs.map p))
      (xs.map a).sum (xs.map d).sum (xs.map c).sum := by
  induction xs with
  | nil => simp [Charges, sumStats, sumPayload]
  | cons x xs ih =>
    exact charges_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem dedupResource_charges {α κ : Type} [DecidableEq κ] (key : α → κ) (xs : List α) :
    Charges N m (dedupResource key xs).keyStats (dedupResource key xs).payload 0 0 0 := by
  simp [Charges, dedupResource]

theorem insideR_charges (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) :
    Charges N m (insideR a base ts).keyStats (insideR a base ts).payload 0 0 0 := by
  induction ts with
  | nil => simp [Charges, insideR]
  | cons t ts ih =>
    rw [insideR]
    apply charges_add (b := 0) (e := 0) (f := 0) ih
    apply charges_add (a := 0) (d := 0) (c := 0) (b := 0) (e := 0) (f := 0)
    · simp [Charges, insideStep]
    · exact dedupResource_charges _ _

theorem rootsR_charges (ts : List (List (Entry N m))) :
    Charges N m (rootsR ts).keyStats (rootsR ts).payload 0 0 0 := by
  induction ts with
  | nil => simp [Charges, rootsR]
  | cons t ts ih =>
    rw [rootsR]
    apply charges_add (b := 0) (e := 0) (f := 0) ih
    apply charges_add (a := 0) (d := 0) (c := 0) (b := 0) (e := 0) (f := 0)
    · simp [Charges, rootStep]
    · exact dedupResource_charges _ _

theorem glueCharge_charges (k : ℕ) : Charges N m {} (glueCharge N m k) 1 k 0 := by
  simp [Charges, glueCharge]

theorem sum_glueCharge {α : Type} (xs : List α) (f : α → ℕ) (k : ℕ)
    (h : ∀ x ∈ xs, f x = k) :
    Charges N m {} (sumPayload (xs.map fun x => glueCharge N m (f x)))
      xs.length (k * xs.length) 0 := by
  induction xs with
  | nil => simp [Charges, sumPayload]
  | cons x xs ih =>
    have hh := charges_add (N := N) (m := m) (glueCharge_charges k)
      (ih (fun y hy => h y (by simp [hy])))
    simpa [sumPayload, h x (by simp), DPStats.add, Nat.mul_add, Nat.add_comm] using hh

theorem localCandidates_noPairs (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (v : Fin N) :
    Charges N m (localCandidatesStats R H m v).stats {} 0 0 0 := by
  rw [localCandidatesStats_count, compositionProfile_only]
  simp [Charges, DPStats.add]

theorem nodeR_charges (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) :
    Charges N m (nodeR R H w m v ts).keyStats (nodeR R H w m v ts).payload
      (nodeRawEntries R H w m v ts).length
      (ts.length * (nodeRawEntries R H w m v ts).length) 0 := by
  let qs := (localCandidatesStats R H m v).value
  let run := fun q : Vector ℕ m =>
    insideR (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts
  have hr (q : Vector ℕ m) :
      Charges N m ((run q).keyStats.add { ratMuls := m })
        ((run q).payload.add (sumPayload ((run q).value.map fun b =>
          glueCharge N m b.picks.length)))
        (run q).value.length (ts.length * (run q).value.length) 0 := by
    have hg := sum_glueCharge (N := N) (m := m) (run q).value
      (fun b : Inside N m => b.picks.length) ts.length
      (by intro b hb; exact (inside_selection _ _ _ b (by simpa [run] using hb)).length_eq.symm)
    have hh := charges_add (insideR_charges (N := N) (support q)
      (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts) hg
    simpa only [Nat.zero_add, Nat.add_zero, Charges, DPStats.add] using hh
  have hsum := charges_sum qs
    (fun q => (run q).keyStats.add { ratMuls := m })
    (fun q => (run q).payload.add (sumPayload ((run q).value.map fun b =>
      glueCharge N m b.picks.length)))
    (fun q => (run q).value.length) (fun q => ts.length * (run q).value.length)
    (fun _ => 0) (fun q _ => hr q)
  have hh := charges_add (localCandidates_noPairs R H m v)
    (charges_add hsum (dedupResource_charges Entry.key (nodeRawEntries R H w m v ts)))
  simpa [nodeR, nodeRawEntries, qs, run, List.flatMap_map, List.map_map,
    Function.comp_def, List.length_flatMap, List.sum_map_mul_left,
    insideR_erase] using hh

theorem computeR_charges (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) :
    Charges N m (computeR R H w m v).keyStats (computeR R H w m v).payload
      (∑ x ∈ subtree R v, rawCount R H w m x)
      (∑ x ∈ subtree R v, (childrenList R x).length * rawCount R H w m x) 0 := by
  classical
  have hc := charges_sum (childrenList R v)
    (fun u => (computeR R H w m u).keyStats) (fun u => (computeR R H w m u).payload)
    (fun u => ∑ x ∈ subtree R u, rawCount R H w m x)
    (fun u => ∑ x ∈ subtree R u, (childrenList R x).length * rawCount R H w m x)
    (fun _ => 0) (by
      intro u hu
      exact computeR_charges R H w m u)
  have hn := nodeR_charges R H w m v ((childrenList R v).map (compute R H w m))
  have hh := charges_add (show Charges N m { nodeCalls := 1 } {} 0 0 0 by simp [Charges])
    (charges_add hc hn)
  rw [computeR, sum_subtree R v (rawCount R H w m),
    sum_subtree R v (fun x => (childrenList R x).length * rawCount R H w m x)]
  simpa [collectR, List.map_map, Function.comp_def, computeR_erase,
    List.attach_map_val, ← childrenList_sum, rawCount, Nat.add_comm] using hh
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp hu)

theorem root_children_sum (R : RootedTree (Fin N)) (f : Fin N → ℕ) :
    ((childrenList R R.root).map fun u => ∑ x ∈ subtree R u, f x).sum =
      ∑ x ∈ Finset.univ.erase R.root, f x := by
  classical
  have hs := sum_subtree R R.root f
  rw [subtree_root, ← childrenList_sum] at hs
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ R.root)
  omega

def optionCount {α : Type} (o : Option α) : ℕ := if o.isSome then 1 else 0

@[simp] theorem optionCount_map {α β : Type} (f : α → β) (o : Option α) :
    optionCount (o.map f) = optionCount o := by cases o <;> rfl

theorem optionCount_le_one {α : Type} (o : Option α) : optionCount o ≤ 1 := by
  cases o <;> simp [optionCount]

theorem finishR_charges (R : RootedTree (Fin N)) (r : Option (Root N m)) (k : ℕ)
    (h : ∀ x, r = some x → x.picks.length = k) :
    Charges N m {} (finishR R r).2 (optionCount r) (optionCount r * k) (optionCount r) := by
  cases r with
  | none => simp [finishR, optionCount, Charges]
  | some x => simp [finishR, optionCount, Charges, glueCharge, PayloadStats.add, h x rfl]

@[simp] theorem finishR_optionCount (R : RootedTree (Fin N)) (r : Option (Root N m)) :
    optionCount (finishR R r).1 = optionCount r := by cases r <;> rfl

theorem solveR_charges (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) :
    Charges N m (solveR R H w m B).keyStats (solveR R H w m B).payload
      ((∑ x ∈ Finset.univ.erase R.root, rawCount R H w m x) +
        optionCount (solveR R H w m B).value)
      ((∑ x ∈ Finset.univ.erase R.root, (childrenList R x).length * rawCount R H w m x) +
        optionCount (solveR R H w m B).value * (childrenList R R.root).length)
      (optionCount (solveR R H w m B).value) := by
  classical
  let ts := (childrenList R R.root).map (compute R H w m)
  let f := findCounted (fun x : Root N m => TreeBudgetSubtreeInteger.accept B x.key) (roots ts)
  have hc := charges_sum (childrenList R R.root)
    (fun u => (computeR R H w m u).keyStats) (fun u => (computeR R H w m u).payload)
    (fun u => ∑ x ∈ subtree R u, rawCount R H w m x)
    (fun u => ∑ x ∈ subtree R u, (childrenList R x).length * rawCount R H w m x)
    (fun _ => 0) (fun u _ => computeR_charges R H w m u)
  have hf := finishR_charges R f.1 (childrenList R R.root).length (by
    intro x hx
    have hx' : (roots ts).find? (fun x => TreeBudgetSubtreeInteger.accept B x.key) = some x :=
      (findCounted_spec _ _).1.symm.trans hx
    have hm : x ∈ roots ts := List.mem_of_find?_eq_some hx'
    simpa [ts] using (roots_selection ts x hm).length_eq.symm)
  have hf' : Charges N m { acceptCalls := f.2 } (finishR R f.1).2
      (optionCount f.1) (optionCount f.1 * (childrenList R R.root).length) (optionCount f.1) := hf
  have hh := charges_add hc (charges_add (rootsR_charges ts) hf')
  simpa [solveR, collectR, List.map_map, Function.comp_def, computeR_erase, rootsR_erase,
    ts, f, root_children_sum] using hh

end UAVProof.TreeBudgetSubtreeResourceSeed
