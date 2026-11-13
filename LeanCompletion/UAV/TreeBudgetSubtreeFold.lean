import LeanCompletion.UAV.TreeBudgetSubtreeCandidates

/-! Exact incremental table combination. Internal folds keep a fixed support.
The root uses a zero/one usage vector to encode the set of assigned labels. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
variable {m : ℕ}

def insideCosts (a : Vector Bool m) (base : Vector ℚ m) :
    List (List (ExecCompactState m)) → List (Vector ℚ m)
  | [] => [base]
  | t :: ts =>
    let rest := insideCosts a base ts
    ((t.filter (fun e => subsetB e.active a)).flatMap fun e =>
      rest.map (fun b => addCost e.cost b)).dedup

theorem insideCosts_spec (a : Vector Bool m) (base b : Vector ℚ m)
    (ts : List (List (ExecCompactState m))) :
    b ∈ insideCosts a base ts ↔ ∃ es : List (ExecCompactState m),
      List.Forall₂ (fun t e => e ∈ t) ts es ∧
      (∀ e ∈ es, subsetB e.active a = true) ∧
      ∀ i, val b i = val base i + (es.map (fun e => val e.cost i)).sum := by
  induction ts generalizing b with
  | nil =>
    constructor
    · intro h
      have hb : b = base := by simpa [insideCosts] using h
      exact ⟨[], .nil, by simp, by simp [hb]⟩
    · rintro ⟨es, he, _, hc⟩
      cases he
      have hb : b = base := vector_ext (by simpa using hc)
      simp [insideCosts, hb]
  | cons t ts ih =>
    simp only [insideCosts, List.mem_dedup, List.mem_flatMap, List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨e, ⟨he, ha⟩, b, hb, rfl⟩
      obtain ⟨es, hsel, hs, hc⟩ := (ih b).mp hb
      refine ⟨e :: es, .cons he hsel, ?_, ?_⟩
      · simpa using And.intro ha hs
      · intro i
        simp only [addCost, val_ofFn, List.map_cons, List.sum_cons, hc i]
        ring
    · rintro ⟨es, hsel, hs, hc⟩
      cases hsel with
      | @cons _ e _ es he hsel =>
        let tail := Vector.ofFn fun i => val base i + (es.map (fun e => val e.cost i)).sum
        refine ⟨e, ⟨he, hs e (by simp)⟩, tail, ?_, ?_⟩
        · apply (ih tail).mpr
          exact ⟨es, hsel, fun e he => hs e (by simp [he]), fun i => by simp [tail]⟩
        · apply vector_ext
          intro i
          simp only [addCost, val_ofFn, tail]
          rw [hc i]
          simp only [List.map_cons, List.sum_cons]
          ring

/-- Materialized usage is always zero or one in accepted root-fold states. -/
structure ExecRootState (m : ℕ) where
  used : Vector ℕ m
  cost : Vector ℚ m
  deriving DecidableEq, Inhabited

def rootZero (m : ℕ) : ExecRootState m := ⟨Vector.ofFn (fun _ => 0), zeroCost m⟩

def rootAdd (x : ExecRootState m) (e : ExecCompactState m) : ExecRootState m :=
  ⟨Vector.ofFn (fun i => val x.used i + bit (val e.active i)), addCost x.cost e.cost⟩

def rootCapB (x : ExecRootState m) : Bool :=
  (List.finRange m).all fun i => decide (val x.used i ≤ 1)

@[simp] theorem rootCapB_spec (x : ExecRootState m) :
    rootCapB x = true ↔ ∀ i, val x.used i ≤ 1 := by simp [rootCapB]

theorem rootState_ext {x y : ExecRootState m}
    (hu : ∀ i, val x.used i = val y.used i)
    (hc : ∀ i, val x.cost i = val y.cost i) : x = y := by
  cases x; cases y
  congr 1
  · exact vector_ext hu
  · exact vector_ext hc

def rootFold : List (List (ExecCompactState m)) → List (ExecRootState m)
  | [] => [rootZero m]
  | t :: ts =>
    let rest := rootFold ts
    ((t.flatMap fun e => rest.map (fun b => rootAdd b e)).filter rootCapB).dedup

theorem rootFold_spec (ts : List (List (ExecCompactState m))) (b : ExecRootState m) :
    b ∈ rootFold ts ↔ ∃ es : List (ExecCompactState m),
      List.Forall₂ (fun t e => e ∈ t) ts es ∧
      (∀ i, val b.used i ≤ 1) ∧
      (∀ i, val b.used i = (es.map (fun e => bit (val e.active i))).sum) ∧
      ∀ i, val b.cost i = (es.map (fun e => val e.cost i)).sum := by
  induction ts generalizing b with
  | nil =>
    constructor
    · intro h
      have hb : b = rootZero m := by simpa [rootFold] using h
      exact ⟨[], .nil, by simp [hb, rootZero], by simp [hb, rootZero],
        by simp [hb, rootZero, zeroCost]⟩
    · rintro ⟨es, hsel, _, hu, hc⟩
      cases hsel
      have hb : b = rootZero m := by
        apply rootState_ext <;> intro i
        · simpa [rootZero] using hu i
        · simpa [rootZero, zeroCost] using hc i
      simp [rootFold, hb]
  | cons t ts ih =>
    simp only [rootFold, List.mem_dedup, List.mem_filter, List.mem_flatMap, List.mem_map,
      rootCapB_spec]
    constructor
    · rintro ⟨⟨e, he, b, hb, rfl⟩, hcap⟩
      obtain ⟨es, hsel, _, hu, hc⟩ := (ih b).mp hb
      refine ⟨e :: es, .cons he hsel, hcap, ?_, ?_⟩
      · intro i; simp [rootAdd, hu i, Nat.add_comm]
      · intro i; simp [rootAdd, addCost, hc i, add_comm]
    · rintro ⟨es, hsel, hcap, hu, hc⟩
      cases hsel with
      | @cons _ e _ es he hsel =>
        let tail : ExecRootState m :=
          ⟨Vector.ofFn (fun i => (es.map (fun e => bit (val e.active i))).sum),
           Vector.ofFn (fun i => (es.map (fun e => val e.cost i)).sum)⟩
        have heq : rootAdd tail e = b := by
          apply rootState_ext <;> intro i
          · rw [hu i]; simp [rootAdd, tail, Nat.add_comm]
          · rw [hc i]; simp [rootAdd, tail, addCost, add_comm]
        refine ⟨⟨e, he, tail, ?_, heq⟩, hcap⟩
        apply (ih tail).mpr
        refine ⟨es, hsel, ?_, by simp [tail], by simp [tail]⟩
        intro i
        have h := hcap i
        rw [hu i] at h
        simp only [List.map_cons, List.sum_cons] at h
        simp only [tail, val_ofFn]
        omega

/-- A no-duplicate index list can represent any equally long selection by a family. -/
theorem exists_family_of_length {α β : Type*} [Inhabited β]
    (us : List α) (hu : us.Nodup) (es : List β) (hlen : es.length = us.length) :
    ∃ f : α → β, us.map f = es := by
  classical
  induction us generalizing es with
  | nil =>
    have he : es = [] := by simpa using hlen
    exact ⟨fun _ => default, by simp [he]⟩
  | cons u us ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      obtain ⟨f, hf⟩ := ih hu.of_cons es (by simpa using hlen)
      refine ⟨Function.update f u e, ?_⟩
      simp only [List.map_cons, Function.update_self]
      congr 1
      rw [← hf]
      apply List.map_congr_left
      intro x hx
      have hxu : x ≠ u := by
        intro he
        subst x
        exact (List.nodup_cons.mp hu).1 hx
      exact Function.update_of_ne hxu _ _

theorem selected_family {α β : Type*} [Inhabited β]
    (us : List α) (hu : us.Nodup) (tables : α → List β) (es : List β) :
    List.Forall₂ (fun t e => e ∈ t) (us.map tables) es ↔
      ∃ f : α → β, us.map f = es ∧ ∀ u ∈ us, f u ∈ tables u := by
  classical
  constructor
  · intro hs
    obtain ⟨f, hf⟩ := exists_family_of_length us hu es (by simpa using hs.length_eq.symm)
    refine ⟨f, hf, ?_⟩
    rw [← hf] at hs
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same] using hs
  · rintro ⟨f, rfl, hf⟩
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same] using hf

end UAVProof.TreeBudgetSubtreeExecutable
