import LeanCompletion.UAV.TreeBudgetVectorMemoIntegration

/-! A compositional cost interface for the ordered vector search. A backend
supplies executable primitives and their value proofs. This module does not
declare their costs to be machine time: an instantiated binary backend and a
storage simulation are required before a bit-complexity conclusion. -/
namespace UAVProof.TreeBudgetCostedSearch
open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetVectorMemoSearch
open TreeBudgetVectorSearchStats TreeBudgetSearchStats
variable {n : ℕ}

/-- Primitive work is observed independently of the six search counters. -/
structure Backend (n : ℕ) where
  keyEq : KeyV n → KeyV n → Bool × ℕ
  guard : Vector ℕ n → Vector ℕ n → Bool × ℕ
  subtract : Vector ℕ n → Vector ℕ n → Vector ℕ n × ℕ
  zero : Vector ℕ n → Bool × ℕ
  keyEqAlloc : KeyV n → KeyV n → ℕ := fun _ _ => 0
  guardAlloc : Vector ℕ n → Vector ℕ n → ℕ := fun _ _ => 0
  subtractAlloc : Vector ℕ n → Vector ℕ n → ℕ := fun _ _ => 0
  zeroAlloc : Vector ℕ n → ℕ := fun _ => 0
  keyEq_value : ∀ p q, (keyEq p q).1 = keyEqB p q
  guard_value : ∀ p q, (guard p q).1 = leB p q
  subtract_value : ∀ p q, (subtract p q).1 = sub p q
  zero_value : ∀ p, (zero p).1 = isZero p

structure Run (α : Type) where
  value : α
  events : Counts := {}
  work : ℕ := 0
  allocations : ℕ := 0

def observe {α : Type} (out : Run α) : Measured α := (out.value, out.events)

def addWork {α : Type} (w : ℕ) (out : Run α) (a : ℕ := 0) : Run α :=
  { out with work := w + out.work, allocations := a + out.allocations }

def addEvents {α : Type} (c : Counts) (out : Run α) : Run α :=
  { out with events := c.add out.events }

@[simp] theorem observe_addWork {α : Type} (w : ℕ) (out : Run α) (a : ℕ := 0) :
    observe (addWork w out a) = observe out := rfl

@[simp] theorem observe_addEvents {α : Type} (c : Counts) (out : Run α) :
    observe (addEvents c out) = bump c (observe out) := rfl

/-- The second projection counts visited entries; work includes each primitive
comparison plus traversal. It stops at the first matching key. -/
def lookupCost (B : Backend n) : CacheV n → KeyV n → Run (Option (AnswerV n))
  | [], _ => ⟨none, {}, 1, 2⟩
  | e :: cs, q =>
    let cmp := B.keyEq e.1 q
    if cmp.1 then
      ⟨some e.2, { lookupComparisons := 1 }, cmp.2 + 1, B.keyEqAlloc e.1 q + 3⟩ else
      addWork (cmp.2 + 1)
        (addEvents { lookupComparisons := 1 } (lookupCost B cs q))
        (B.keyEqAlloc e.1 q + 1)

theorem lookupCost_value (B : Backend n) (cs : CacheV n) (q : KeyV n) :
    (lookupCost B cs q).value = lookupV cs q := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [lookupCost, lookupV, B.keyEq_value]
    split <;> simp_all [addWork, addEvents]

def filterCost (B : Backend n) : CacheV n → KeyV n → Run (CacheV n)
  | [], _ => ⟨[], {}, 1, 2⟩
  | e :: cs, q =>
    let cmp := B.keyEq e.1 q
    let out := filterCost B cs q
    ⟨if cmp.1 then out.value else e :: out.value,
      ({ insertionScans := 1 } : Counts).add out.events,
      cmp.2 + 2 + out.work,
      B.keyEqAlloc e.1 q + 1 + (if cmp.1 then 0 else 3) + out.allocations⟩

theorem filterCost_value (B : Backend n) (cs : CacheV n) (q : KeyV n) :
    (filterCost B cs q).value = cs.filter (fun e => !(keyEqB e.1 q)) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [filterCost, B.keyEq_value, ih]
    cases he : keyEqB e.1 q <;> simp [he]

def insertCost (B : Backend n) (cs : CacheV n) (q : KeyV n) (a : AnswerV n) :
    Run (CacheV n) :=
  let out := filterCost B cs q
  ⟨(q, a) :: out.value, out.events, out.work + 1, out.allocations + 6⟩

@[simp] theorem insertCost_value (B : Backend n) (cs : CacheV n)
    (q : KeyV n) (a : AnswerV n) :
    (insertCost B cs q a).value = insertV cs q a := by
  simp [insertCost, insertV, filterCost_value]

def scanCost (B : Backend n)
    (solve : Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n))
    (r : Vector ℕ n) : List (Vector ℕ n) → CacheV n → Run (AnswerV n × CacheV n)
  | [], cs => ⟨(none, cs), {}, 1, 4⟩
  | p :: ps, cs =>
    let guarded := B.guard p r
    addWork (guarded.2 + 1) (addEvents { candidates := 1 } <|
      if guarded.1 then
        let residual := B.subtract r p
        let out := solve residual.1 cs
        addWork (residual.2 + 1) (
          match out.value.1 with
          | some rows =>
              ⟨(some (p :: rows), out.value.2), out.events, out.work + 1,
                out.allocations + 7⟩
          | none =>
            let tail := scanCost B solve r ps out.value.2
            ⟨tail.value, out.events.add tail.events, out.work + tail.work,
              out.allocations + tail.allocations⟩) (B.subtractAlloc r p + 1)
      else scanCost B solve r ps cs) (B.guardAlloc p r + 1)

def memoCost (B : Backend n) (ps : List (Vector ℕ n)) :
    ℕ → Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n)
  | k, r, cs =>
    let found := lookupCost B cs (k, r)
    match found.value with
    | some a => ⟨(a, cs),
        ({ calls := 1, hits := 1 } : Counts).add found.events, found.work + 1,
        found.allocations + 5⟩
    | none =>
      let out : Run (AnswerV n × CacheV n) := match k with
        | 0 =>
          let z := B.zero r
          ⟨(if z.1 then some [] else none, cs), {}, z.2 + 1,
            B.zeroAlloc r + (if z.1 then 5 else 3)⟩
        | j + 1 => scanCost B (memoCost B ps j) r ps cs
      let saved := insertCost B out.value.2 (k, r) out.value.1
      ⟨(out.value.1, saved.value),
        (({ calls := 1, expansions := 1 } : Counts).add found.events).add
          (out.events.add saved.events),
        found.work + out.work + saved.work + 1,
        found.allocations + out.allocations + saved.allocations + 5⟩

@[simp] theorem counts_zero_add (c : Counts) : ({} : Counts).add c = c := by
  cases c
  simp [Counts.add]

@[simp] theorem counts_add_zero (c : Counts) : c.add {} = c := by
  cases c
  simp [Counts.add]

theorem counts_add_assoc (a b c : Counts) : (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp [Counts.add, Nat.add_assoc]

theorem lookupCost_observe (B : Backend n) (cs : CacheV n) (q : KeyV n) :
    observe (lookupCost B cs q) =
      ((lookupStatV cs q).1, { lookupComparisons := (lookupStatV cs q).2 }) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [lookupCost, lookupStatV, B.keyEq_value]
    split
    · rfl
    · simp only [observe_addWork, observe_addEvents, ih]
      simp [bump, Counts.add, Nat.add_comm]

theorem filterCost_events (B : Backend n) (cs : CacheV n) (q : KeyV n) :
    (filterCost B cs q).events = { insertionScans := cs.length } := by
  induction cs with
  | nil => rfl
  | cons e cs ih => simp [filterCost, ih, Counts.add, Nat.add_comm]

theorem insertCost_observe (B : Backend n) (cs : CacheV n)
    (q : KeyV n) (a : AnswerV n) :
    observe (insertCost B cs q a) = insertStatV cs q a := by
  simp [observe, insertCost, filterCost_value, filterCost_events, insertStatV, insertV]

theorem scanCost_observe (B : Backend n)
    (solve : Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n))
    (refSolve : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (h : ∀ r cs, observe (solve r cs) = refSolve r cs)
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n) :
    observe (scanCost B solve r ps cs) = scanStatV refSolve r ps cs := by
  induction ps generalizing cs with
  | nil => rfl
  | cons p ps ih =>
    simp only [scanCost, scanStatV, B.guard_value, B.subtract_value,
      observe_addWork, observe_addEvents]
    split_ifs with hp
    · rw [← h]
      cases he : solve (sub r p) cs with
      | mk out events work allocations =>
        rcases out with ⟨a, cache⟩
        cases a with
        | none =>
          simpa [observe, bump] using congrArg (bump ({ candidates := 1 } : Counts))
            (congrArg (bump events) (ih cache))
        | some rows => rfl
    · rw [ih]

/-- Both the exact ordinary result and the six event counters are preserved.
The primitive work field is independent of the observer counters. -/
theorem memoCost_observe (B : Backend n) (ps : List (Vector ℕ n))
    (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    observe (memoCost B ps k r cs) = memoStatV ps k r cs := by
  induction k generalizing r cs with
  | zero =>
    have hv := congrArg Prod.fst (lookupCost_observe B cs (0, r))
    have hc := congrArg Prod.snd (lookupCost_observe B cs (0, r))
    change (lookupCost B cs (0, r)).value = _ at hv
    change (lookupCost B cs (0, r)).events = _ at hc
    simp only [memoCost, memoStatV, hv, hc, B.zero_value]
    cases he : (lookupStatV cs (0, r)).1 with
    | some a => simp [observe, Counts.add]
    | none =>
      simp [observe, insertCost, filterCost_value, filterCost_events, insertStatV,
        insertV, Counts.add]
  | succ k ih =>
    have hv := congrArg Prod.fst (lookupCost_observe B cs (k + 1, r))
    have hc := congrArg Prod.snd (lookupCost_observe B cs (k + 1, r))
    change (lookupCost B cs (k + 1, r)).value = _ at hv
    change (lookupCost B cs (k + 1, r)).events = _ at hc
    have hs := scanCost_observe B (memoCost B ps k) (memoStatV ps k) ih r ps cs
    simp only [memoCost, memoStatV, hv, hc]
    cases he : (lookupStatV cs (k + 1, r)).1 with
    | some a => simp [observe, Counts.add]
    | none =>
      rw [← hs]
      simp [observe, insertCost, filterCost_value, filterCost_events, insertStatV,
        insertV, Counts.add]

theorem memoCost_value (B : Backend n) (ps : List (Vector ℕ n))
    (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    (memoCost B ps k r cs).value = memoRowsWithV ps k r cs := by
  have h := congrArg Prod.fst (memoCost_observe B ps k r cs)
  simpa only [observe, memoStatV_erase] using h

end UAVProof.TreeBudgetCostedSearch

#print axioms UAVProof.TreeBudgetCostedSearch.Backend
#print axioms UAVProof.TreeBudgetCostedSearch.Run
#print axioms UAVProof.TreeBudgetCostedSearch.observe
#print axioms UAVProof.TreeBudgetCostedSearch.addWork
#print axioms UAVProof.TreeBudgetCostedSearch.addEvents
#print axioms UAVProof.TreeBudgetCostedSearch.observe_addWork
#print axioms UAVProof.TreeBudgetCostedSearch.observe_addEvents
#print axioms UAVProof.TreeBudgetCostedSearch.lookupCost
#print axioms UAVProof.TreeBudgetCostedSearch.lookupCost_value
#print axioms UAVProof.TreeBudgetCostedSearch.filterCost
#print axioms UAVProof.TreeBudgetCostedSearch.filterCost_value
#print axioms UAVProof.TreeBudgetCostedSearch.insertCost
#print axioms UAVProof.TreeBudgetCostedSearch.insertCost_value
#print axioms UAVProof.TreeBudgetCostedSearch.scanCost
#print axioms UAVProof.TreeBudgetCostedSearch.memoCost
#print axioms UAVProof.TreeBudgetCostedSearch.counts_zero_add
#print axioms UAVProof.TreeBudgetCostedSearch.counts_add_zero
#print axioms UAVProof.TreeBudgetCostedSearch.counts_add_assoc
#print axioms UAVProof.TreeBudgetCostedSearch.lookupCost_observe
#print axioms UAVProof.TreeBudgetCostedSearch.filterCost_events
#print axioms UAVProof.TreeBudgetCostedSearch.insertCost_observe
#print axioms UAVProof.TreeBudgetCostedSearch.scanCost_observe
#print axioms UAVProof.TreeBudgetCostedSearch.memoCost_observe
#print axioms UAVProof.TreeBudgetCostedSearch.memoCost_value
