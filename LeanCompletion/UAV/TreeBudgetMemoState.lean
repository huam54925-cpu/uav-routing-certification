import LeanCompletion.UAV.TreeBudgetResidualSearch

/-! Executable association-list cache for one fixed tree-budget input.
The key retains both the number of rows and every residual coordinate.
An outer none is a miss; some none is a proved failure; some (some rows)
is a cached witness, including a successful empty list. -/
namespace UAVProof.TreeBudgetMemoState
open TreeFlowExistence TreeBudgetResidualSearch

abbrev Rows (n : ℕ) := List (Fin n → ℕ)
abbrev Key (n : ℕ) := ℕ × (Fin n → ℕ)
abbrev Answer (n : ℕ) := Option (Rows n)
abbrev Cache (n : ℕ) := List (Key n × Answer n)

variable {n : ℕ}

def emptyCache : Cache n := []

def lookup : Cache n → Key n → Option (Answer n)
  | [], _ => none
  | e :: cache, q => if e.1 = q then some e.2 else lookup cache q

/-- Replace every old occurrence of q and put its new answer first.
This does not impose any validity assumption on a raw cache operation. -/
def insert (cache : Cache n) (q : Key n) (answer : Answer n) : Cache n :=
  (q, answer) :: cache.filter (fun e => decide (e.1 ≠ q))

def AnswerValid (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (q : Key n) : Answer n → Prop
  | some rows => ResidualWitness R H s T q.1 q.2 rows
  | none => ¬ ResidualFeasible R H s T q.1 q.2

/-- Validity is relative to the same fixed R,H,s,T for all queries.
A caller must not reuse this invariant for a different input. -/
def CacheValid (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) : Prop :=
  ∀ q answer, lookup cache q = some answer → AnswerValid R H s T q answer

def KeysNodup (cache : Cache n) : Prop := (cache.map Prod.fst).Nodup

@[simp] theorem lookup_empty (q : Key n) : lookup emptyCache q = none := rfl

@[simp] theorem lookup_insert_same (cache : Cache n) (q : Key n) (answer : Answer n) :
    lookup (insert cache q answer) q = some answer := by simp [insert, lookup]

theorem lookup_filter_other (cache : Cache n) (q q' : Key n) (hne : q' ≠ q) :
    lookup (cache.filter (fun e => decide (e.1 ≠ q))) q' = lookup cache q' := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    by_cases he : e.1 = q
    · have he' : e.1 ≠ q' := by intro h; exact hne (h.symm.trans he)
      rw [List.filter_cons_of_neg (by simp [he]), lookup, if_neg he']
      exact ih
    · rw [List.filter_cons_of_pos (by simp [he])]
      simp only [lookup, ih]

theorem lookup_insert_other (cache : Cache n) (q q' : Key n) (answer : Answer n)
    (hne : q' ≠ q) : lookup (insert cache q answer) q' = lookup cache q' := by
  simp only [insert, lookup, if_neg hne.symm]
  exact lookup_filter_other cache q q' hne

theorem cacheValid_empty (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : CacheValid R H s T emptyCache := by
  intro q answer h
  simp at h

theorem cacheValid_insert (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) (q : Key n) (answer : Answer n)
    (hc : CacheValid R H s T cache) (ha : AnswerValid R H s T q answer) :
    CacheValid R H s T (insert cache q answer) := by
  intro q' answer' hh
  by_cases he : q' = q
  · subst q'
    rw [lookup_insert_same] at hh
    cases Option.some.inj hh
    exact ha
  · rw [lookup_insert_other cache q q' answer he] at hh
    exact hc q' answer' hh

@[simp] theorem keysNodup_empty : KeysNodup (emptyCache : Cache n) := by
  simp [KeysNodup, emptyCache]

theorem keysNodup_insert (cache : Cache n) (q : Key n) (answer : Answer n)
    (hc : KeysNodup cache) : KeysNodup (insert cache q answer) := by
  unfold KeysNodup insert
  rw [List.map_cons, List.nodup_cons]
  constructor
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, not_exists, not_and]
    intro e he hq
    exact he.2 hq
  · exact (List.filter_sublist.map Prod.fst).nodup hc

/-- Replacement never adds more than one entry, including on malformed caches. -/
theorem insert_length_le (cache : Cache n) (q : Key n) (answer : Answer n) :
    (insert cache q answer).length ≤ cache.length + 1 := by
  simpa only [insert, List.length_cons, Nat.add_le_add_iff_right] using
    (List.length_filter_le (p := fun e : Key n × Answer n => decide (e.1 ≠ q)) cache)

/-- Any sequence of valid insertions from the empty cache stays valid and has
no duplicate keys. The induction hypothesis also admits an already valid cache. -/
theorem insert_preserves (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) (q : Key n) (answer : Answer n)
    (hc : CacheValid R H s T cache ∧ KeysNodup cache)
    (ha : AnswerValid R H s T q answer) :
    CacheValid R H s T (insert cache q answer) ∧ KeysNodup (insert cache q answer) :=
  ⟨cacheValid_insert R H s T cache q answer hc.1 ha, keysNodup_insert cache q answer hc.2⟩

end UAVProof.TreeBudgetMemoState

#print axioms UAVProof.TreeBudgetMemoState.lookup_empty
#print axioms UAVProof.TreeBudgetMemoState.lookup_insert_same
#print axioms UAVProof.TreeBudgetMemoState.lookup_insert_other
#print axioms UAVProof.TreeBudgetMemoState.cacheValid_empty
#print axioms UAVProof.TreeBudgetMemoState.cacheValid_insert
#print axioms UAVProof.TreeBudgetMemoState.keysNodup_empty
#print axioms UAVProof.TreeBudgetMemoState.keysNodup_insert
#print axioms UAVProof.TreeBudgetMemoState.insert_length_le
#print axioms UAVProof.TreeBudgetMemoState.insert_preserves
