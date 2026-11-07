import LeanCompletion.UAV.TreeBudgetVector
import LeanCompletion.UAV.TreeBudgetMemoState

/-! Materialized vector states for the ordered association-list cache. Decoding
is a specification map only: all executable comparisons inspect vectors. Raw
caches may contain duplicate or conflicting keys; first-match lookup and full
stable replacement retain precisely the reference protocol. -/
namespace UAVProof.TreeBudgetVectorMemoState
open TreeBudgetVector
variable {n : ℕ}

abbrev RowsV (n : ℕ) := List (Vector ℕ n)
abbrev KeyV (n : ℕ) := ℕ × Vector ℕ n
abbrev AnswerV (n : ℕ) := Option (RowsV n)
abbrev CacheV (n : ℕ) := List (KeyV n × AnswerV n)

def decodeRows (rows : RowsV n) : TreeBudgetMemoState.Rows n := rows.map decode
def decodeKey (q : KeyV n) : TreeBudgetMemoState.Key n := (q.1, decode q.2)
def decodeAnswer (answer : AnswerV n) : TreeBudgetMemoState.Answer n :=
  answer.map decodeRows
def decodeCache (cache : CacheV n) : TreeBudgetMemoState.Cache n :=
  cache.map fun e => (decodeKey e.1, decodeAnswer e.2)
def decodeResult (out : AnswerV n × CacheV n) :
    TreeBudgetMemoState.Answer n × TreeBudgetMemoState.Cache n :=
  (decodeAnswer out.1, decodeCache out.2)

@[simp] theorem decodeRows_nil : decodeRows ([] : RowsV n) = [] := rfl
@[simp] theorem decodeRows_cons (p : Vector ℕ n) (rows : RowsV n) :
    decodeRows (p :: rows) = decode p :: decodeRows rows := rfl
@[simp] theorem decodeRows_length (rows : RowsV n) :
    (decodeRows rows).length = rows.length := by simp [decodeRows]
@[simp] theorem decodeAnswer_none : decodeAnswer (none : AnswerV n) = none := rfl
@[simp] theorem decodeAnswer_some (rows : RowsV n) :
    decodeAnswer (some rows) = some (decodeRows rows) := rfl
@[simp] theorem decodeCache_nil : decodeCache ([] : CacheV n) = [] := rfl
@[simp] theorem decodeCache_cons (q : KeyV n) (a : AnswerV n) (cache : CacheV n) :
    decodeCache ((q, a) :: cache) = (decodeKey q, decodeAnswer a) :: decodeCache cache := rfl
@[simp] theorem decodeCache_length (cache : CacheV n) :
    (decodeCache cache).length = cache.length := by simp [decodeCache]
@[simp] theorem decodeResult_pair (a : AnswerV n) (cache : CacheV n) :
    decodeResult (a, cache) = (decodeAnswer a, decodeCache cache) := rfl

def keyEqB (q q' : KeyV n) : Bool := decide (q.1 = q'.1) && eqB q.2 q'.2

@[simp] theorem keyEqB_eq_true (q q' : KeyV n) :
    keyEqB q q' = true ↔ decodeKey q = decodeKey q' := by
  simp [keyEqB, eqB_eq_true, decodeKey, Prod.mk.injEq]

def lookupV : CacheV n → KeyV n → Option (AnswerV n)
  | [], _ => none
  | e :: cache, q => if keyEqB e.1 q then some e.2 else lookupV cache q

def insertV (cache : CacheV n) (q : KeyV n) (answer : AnswerV n) : CacheV n :=
  (q, answer) :: cache.filter (fun e => !(keyEqB e.1 q))

@[simp] theorem decode_lookupV (cache : CacheV n) (q : KeyV n) :
    (lookupV cache q).map decodeAnswer =
      TreeBudgetMemoState.lookup (decodeCache cache) (decodeKey q) := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    rcases e with ⟨q', a⟩
    simp only [lookupV, decodeCache_cons, TreeBudgetMemoState.lookup, keyEqB_eq_true]
    split <;> simp_all

theorem decodeCache_filter (cache : CacheV n) (q : KeyV n) :
    decodeCache (cache.filter fun e => !(keyEqB e.1 q)) =
      (decodeCache cache).filter (fun e => decide (e.1 ≠ decodeKey q)) := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    rcases e with ⟨q', a⟩
    by_cases h : decodeKey q' = decodeKey q
    · have hb : keyEqB q' q = true := (keyEqB_eq_true ..).mpr h
      simp [hb, h, ih]
    · have hb : keyEqB q' q = false :=
        Bool.eq_false_iff.mpr (fun ht => h ((keyEqB_eq_true ..).mp ht))
      simp [hb, h, ih]

@[simp] theorem decode_insertV (cache : CacheV n) (q : KeyV n) (a : AnswerV n) :
    decodeCache (insertV cache q a) =
      TreeBudgetMemoState.insert (decodeCache cache) (decodeKey q) (decodeAnswer a) := by
  simp [insertV, TreeBudgetMemoState.insert, decodeCache_filter]

end UAVProof.TreeBudgetVectorMemoState

#print axioms UAVProof.TreeBudgetVectorMemoState.decodeRows_nil
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeRows_cons
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeRows_length
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeAnswer_none
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeAnswer_some
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeCache_nil
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeCache_cons
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeCache_length
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeResult_pair
#print axioms UAVProof.TreeBudgetVectorMemoState.keyEqB_eq_true
#print axioms UAVProof.TreeBudgetVectorMemoState.decode_lookupV
#print axioms UAVProof.TreeBudgetVectorMemoState.decodeCache_filter
#print axioms UAVProof.TreeBudgetVectorMemoState.decode_insertV
