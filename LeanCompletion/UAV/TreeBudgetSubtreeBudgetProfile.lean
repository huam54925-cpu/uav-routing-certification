import LeanCompletion.UAV.TreeBudgetSubtreeScalarEntry

/-!
Budget queries on a fixed ordered subtree root table. For a positive number of
routes each eligible entry has a signed peak cost. Keeping strict prefix minima
preserves the first passing payload, including ties.
-/
namespace UAVProof.TreeBudgetSubtreeBudgetProfile

open TreeFlowExistence TreeBudgetSubtreeExecutable

section Prefix
variable {α : Type}

/-- The list order determines which payload a budget query receives. -/
def query (B : Int) : List (Int × α) → Option (Int × α)
  | [] => none
  | e :: es => if e.1 ≤ B then some e else query B es

/-- The bound is the least threshold in the prefix already processed. -/
def records : Option Int → List (Int × α) → List (Int × α)
  | _, [] => []
  | none, e :: es => e :: records (some e.1) es
  | some t, e :: es =>
    if e.1 < t then e :: records (some e.1) es else records (some t) es

theorem query_records (B : Int) (xs : List (Int × α)) (cut : Option Int)
    (hc : ∀ t, cut = some t → B < t) :
    query B (records cut xs) = query B xs := by
  induction xs generalizing cut with
  | nil => cases cut <;> rfl
  | cons e es ih =>
    have takeStep : query B (e :: records (some e.1) es) = query B (e :: es) := by
      by_cases hb : e.1 ≤ B
      · simp [query, hb]
      · simp only [query, if_neg hb]
        apply ih
        intro t ht
        cases ht
        omega
    cases cut with
    | none => exact takeStep
    | some t =>
      by_cases he : e.1 < t
      · simpa only [records, if_pos he] using takeStep
      · have hbt := hc t rfl
        have hb : ¬ e.1 ≤ B := by omega
        simp only [records, if_neg he, query, if_neg hb]
        exact ih (some t) hc

theorem query_records_none (B : Int) (xs : List (Int × α)) :
    query B (records none xs) = query B xs :=
  query_records B xs none (by simp)

private theorem records_lt (xs : List (Int × α)) (t : Int) :
    ∀ e ∈ records (some t) xs, e.1 < t := by
  induction xs generalizing t with
  | nil => simp [records]
  | cons x xs ih =>
    by_cases hx : x.1 < t
    · simp only [records, if_pos hx, List.mem_cons, forall_eq_or_imp]
      exact ⟨hx, fun e he => lt_trans (ih x.1 e he) hx⟩
    · simpa only [records, if_neg hx] using ih t

theorem records_decreasing (xs : List (Int × α)) (cut : Option Int) :
    (records cut xs).Pairwise (fun a b => b.1 < a.1) := by
  induction xs generalizing cut with
  | nil => cases cut <;> simp [records]
  | cons x xs ih =>
    have keep := List.pairwise_cons.mpr ⟨records_lt xs x.1, ih (some x.1)⟩
    cases cut with
    | none => exact keep
    | some t =>
      by_cases hx : x.1 < t
      · simpa only [records, if_pos hx] using keep
      · simpa only [records, if_neg hx] using ih (some t)

private theorem query_none_iff (B : Int) (xs : List (Int × α)) :
    query B xs = none ↔ ∀ e ∈ xs, B < e.1 := by
  induction xs with
  | nil => simp [query]
  | cons x xs ih =>
    by_cases hx : x.1 ≤ B
    · simp [query, hx, not_lt_of_ge hx]
    · simp [query, hx, ih, lt_of_not_ge hx]

/-- Every retained entry is selected at its own threshold, including its payload. -/
theorem query_at_record {xs : List (Int × α)}
    (hs : xs.Pairwise (fun a b => b.1 < a.1)) {e : Int × α} (he : e ∈ xs) :
    query e.1 xs = some e := by
  induction xs with
  | nil => simp at he
  | cons x xs ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simp [query]
    · have hx := (List.pairwise_cons.mp hs).1 _ he
      simpa only [query, if_neg (not_le_of_gt hx)] using
        ih (List.pairwise_cons.mp hs).2 he

private theorem last_threshold {xs : List (Int × α)}
    (hs : xs.Pairwise (fun a b => b.1 < a.1)) {e : Int × α}
    (he : xs.getLast? = some e) (B : Int) :
    query B xs = none ↔ B < e.1 := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp he
  rw [query_none_iff]
  constructor
  · exact fun h => h e (by simp)
  · intro h x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact lt_trans h ((List.pairwise_append.mp hs).2.2 _ hx e (by simp))
    · obtain rfl := List.mem_singleton.mp hx
      exact h

end Prefix

section RootBudget

variable {N k : Nat}

def completeUse {m : Nat} (q : TreeBudgetSubtreeInteger.IntRoot m) : Bool :=
  (List.finRange m).all fun i => decide (val q.used i = 1)

def peak (q : TreeBudgetSubtreeInteger.IntRoot (k+1)) : Int :=
  ((List.finRange (k+1)).map (val q.cost)).foldl max (val q.cost 0)

private theorem foldMax_le (xs : List Int) (a B : Int) :
    xs.foldl max a ≤ B ↔ a ≤ B ∧ ∀ z ∈ xs, z ≤ B := by
  induction xs generalizing a with
  | nil => simp
  | cons z zs ih => simp [List.foldl, ih, and_assoc, and_left_comm, and_comm]

theorem peak_le (q : TreeBudgetSubtreeInteger.IntRoot (k+1)) (B : Int) :
    peak q ≤ B ↔ ∀ i, val q.cost i ≤ B := by
  rw [peak, foldMax_le]
  constructor
  · intro h i
    exact h.2 _ (List.mem_map.mpr ⟨i, by simp, rfl⟩)
  · intro h
    refine ⟨h 0, ?_⟩
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact h i

theorem accept_iff (q : TreeBudgetSubtreeInteger.IntRoot (k+1)) (B : Int) :
    TreeBudgetSubtreeInteger.accept B q = true ↔
      completeUse q = true ∧ peak q ≤ B := by
  have h₁ : TreeBudgetSubtreeInteger.accept B q = true ↔
      ∀ i, val q.used i = 1 ∧ val q.cost i ≤ B := by
    simp [TreeBudgetSubtreeInteger.accept]
  have h₂ : completeUse q = true ↔ ∀ i, val q.used i = 1 := by
    simp [completeUse]
  rw [h₁, h₂, peak_le]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
    fun h i => ⟨h.1 i, h.2 i⟩⟩

open TreeBudgetSubtreeIntegerWitnessSeed in
def scored : List (Root N (k+1)) → List (Int × Root N (k+1))
  | [] => []
  | e :: es =>
    if completeUse e.key then (peak e.key, e) :: scored es else scored es

open TreeBudgetSubtreeIntegerWitnessSeed in
theorem query_scored (B : Int) (xs : List (Root N (k+1))) :
    (query B (scored xs)).map Prod.snd =
      xs.find? (fun e => TreeBudgetSubtreeInteger.accept B e.key) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have off (h : ¬ (completeUse e.key = true ∧ peak e.key ≤ B)) :
        TreeBudgetSubtreeInteger.accept B e.key = false := by
      cases h' : TreeBudgetSubtreeInteger.accept B e.key with
      | false => rfl
      | true => exact (h ((accept_iff e.key B).mp h')).elim
    cases hu : completeUse e.key with
    | false =>
      have ha := off (by simp [hu])
      simp [scored, hu, List.find?, ha, ih]
    | true =>
      by_cases hp : peak e.key ≤ B
      · have ha := (accept_iff e.key B).mpr ⟨hu, hp⟩
        simp [scored, hu, query, hp, List.find?, ha]
      · have ha := off (by simp [hp])
        simp [scored, hu, query, hp, List.find?, ha, ih]

open TreeBudgetSubtreeIntegerWitnessSeed in
def buildProfile (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (k : Nat) : List (Int × Root N (k+1)) :=
  let rs := roots ((childrenList R R.root).map (compute R H w (k+1)))
  records none (scored rs)

open TreeBudgetSubtreeIntegerWitnessSeed in
theorem profile_query_eq_solve (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (k : Nat) (B : Int) :
    ((query B (buildProfile R H w k)).map Prod.snd).map (certificate R) =
      solve R H w (k+1) B := by
  unfold buildProfile
  rw [query_records_none, query_scored]
  rfl

open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeIntegerWitnessSeed in
theorem profile_query_eq_auto (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (k : Nat) (T : Rat) :
    let p := prepare R s 0
    let xs := buildProfile R H (val p.weight) k
    ((query (TreeBudgetSubtreeInteger.floorBudget p.scale T) xs).map Prod.snd).map
        (certificate R) = solveAuto R H s (k+1) T := by
  dsimp only
  unfold solveAuto
  exact profile_query_eq_solve R H (val (prepare R s 0).weight) k
    (TreeBudgetSubtreeInteger.floorBudget (prepare R s 0).scale T)

theorem accept_zero (q : TreeBudgetSubtreeInteger.IntRoot 0) (B : Int) :
    TreeBudgetSubtreeInteger.accept B q = true := by
  simp [TreeBudgetSubtreeInteger.accept]

open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeIntegerWitnessSeed in
theorem profile_query_eq_materialized (R : RootedTree (Fin N))
    (I : TreeBudgetSubtreePre.Input N) (hr : TreeBudgetSubtreePre.Represents I R)
    (hk : I.routes = k+1) :
    let p := prepare R (val I.service) 0
    let xs := buildProfile R (val I.mass) (val p.weight) k
    ((query (TreeBudgetSubtreeInteger.floorBudget p.scale I.budget) xs).map Prod.snd).map
        (certificate R) = (TreeBudgetSubtreeScalar.executeC R I).value.value := by
  rw [TreeBudgetSubtreeScalar.executeC_certificate_eq R I hr, hk]
  exact (profile_query_eq_auto R (val I.mass) (val I.service) k I.budget).trans
    (solveAuto_eq R (val I.mass) (val I.service) (k+1) I.budget)

end RootBudget

section Optimization

open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeInteger (floorBudget lift_budget)
open TreeBudgetSubtreeResource (rootMass)
variable {N : Nat}

/-- The all-budgets case carries the empty-fleet certificate. -/
inductive Optimum (α : Type) where
  | infeasible
  | allBudgets (cert : α)
  | least (budget : Rat) (cert : α)

/-- Reject incompatible root mass before constructing any route vectors. -/
def optimize (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat) (m : Nat) :
    Optimum (TreeBudgetCertificate.Certificate (Fin N)) :=
  if m = rootMass R H then
    match m with
    | 0 =>
      match solveAuto R H s 0 0 with
      | none => .infeasible
      | some c => .allBudgets c
    | k + 1 =>
      let p := prepare R s 0
      match (buildProfile R H (val p.weight) k).getLast? with
      | none => .infeasible
      | some (b, r) => .least ((b : Rat) / p.scale) (certificate R r)
  else .infeasible

theorem solveAuto_zero_budget_independent (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (T : Rat) : solveAuto R H s 0 T = solveAuto R H s 0 0 := by
  simp only [solveAuto, solve, accept_zero]
  rfl

/-- At a reported minimum the original solver returns the reported certificate.
Matrix feasibility holds exactly on the closed ray starting at this budget. -/
theorem optimize_spec (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) :
    match optimize R H s m with
    | .infeasible => ∀ T, ¬ TreeBudgetMatrix.MatrixFeasible R H m s T
    | .allBudgets c => ∀ T, solveAuto R H s m T = some c
    | .least q c => solveAuto R H s m q = some c ∧
        ∀ T, TreeBudgetMatrix.MatrixFeasible R H m s T ↔ q ≤ T := by
  unfold optimize
  by_cases hg : m = rootMass R H
  · rw [if_pos hg]
    cases m with
    | zero =>
      cases hc : solveAuto R H s 0 0 with
      | none =>
        intro T
        apply (solveAuto_none_iff ..).mp
        exact (solveAuto_zero_budget_independent R H s T).trans hc
      | some c =>
        exact fun T => (solveAuto_zero_budget_independent R H s T).trans hc
    | succ k =>
      dsimp only
      set p := prepare R s 0
      set xs := buildProfile R H (val p.weight) k
      have href (T : Rat) := profile_query_eq_auto R H s k T
      change ∀ (T : Rat), ((query (floorBudget p.scale T) xs).map Prod.snd).map
        (certificate R) = solveAuto R H s (k+1) T at href
      cases he : xs.getLast? with
      | none =>
        have hx : xs = [] := List.getLast?_eq_none_iff.mp he
        intro T
        apply (solveAuto_none_iff ..).mp
        rw [← href, hx]
        rfl
      | some e =>
        have hsorted : xs.Pairwise (fun a b => b.1 < a.1) := records_decreasing _ none
        have hm : e ∈ xs := by
          obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp he
          simp [hys]
        have hscale := prepare_pos R s 0
        have hfloor : floorBudget p.scale ((e.1 : Rat) / p.scale) = e.1 := by
          unfold floorBudget
          have hd : (p.scale : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hscale)
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ hd, Int.floor_intCast]
        have hlast := last_threshold hsorted he
        constructor
        · rw [← href, hfloor, query_at_record hsorted hm]
          rfl
        · intro T
          have hnone : solveAuto R H s (k+1) T = none ↔ floorBudget p.scale T < e.1 := by
            rw [← href]
            simpa using hlast (floorBudget p.scale T)
          have hb := lift_budget hscale e.1 T
          rw [← not_iff_not, ← solveAuto_none_iff, hnone, hb, not_le]
  · rw [if_neg hg]
    exact fun T hf => hg (TreeBudgetSubtreeResource.matrixFeasible_rootMass R H s m T hf)

/-- With the prescribed degrees, the same minimum is attained by an exact route
family, and the returned matrix certificate passes the original checker. -/
theorem least_exact_iff (R : RootedTree (Fin N)) (H d : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (q : Rat) (c : TreeBudgetCertificate.Certificate (Fin N))
    (hc : optimize R H s m = .least q c)
    (hd : SupportExactFeasibility.HasDegrees R.root d m (edgeFlow R H)) :
    TreeBudgetCertificate.checkCertificate R H m s q c = true ∧
      ∀ T, SupportExactFeasibility.ExactFeasible R.root (edgeFlow R H) d m s T ↔ q ≤ T := by
  have h := optimize_spec R H s m
  rw [hc] at h
  exact ⟨solveAuto_sound R H s m q c h.1, fun T =>
    (TreeBudgetMatrix.exact_iff_matrix R H d m s T hd).trans (h.2 T)⟩

end Optimization

end UAVProof.TreeBudgetSubtreeBudgetProfile
