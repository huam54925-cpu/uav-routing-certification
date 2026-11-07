import LeanCompletion.UAV.TreeBudgetTypedStore
import LeanCompletion.UAV.TreeBudgetBinaryCodec

/-! Concrete immutable search payloads and ordered cache nodes. A payload has
an actual unary bit-length header followed by its binary data, so its footprint
is exactly twice the payload length plus one. The header is linear in encoded
length, not numeric magnitude. Cache nodes contain real key, answer and tail
references; prepending shares all three referenced objects. This module proves
storage decoding and first-hit lookup, not a simulation of the memo evaluator
or a total addressed-machine time bound. -/
namespace UAVProof.TreeBudgetSearchStore
open TreeBudgetTypedStore TreeBudgetAllocationBounds TreeBudgetBinaryCodec

abbrev WireKey := ℕ × List ℕ
abbrev WireAnswer := Option Matrix
abbrev WireCache := List (WireKey × WireAnswer)

def blobSlots (bits : Bits) : List Slot :=
  List.replicate bits.length (.bit true) ++ .bit false :: bits.map Slot.bit

theorem blobSlots_length (bits : Bits) : (blobSlots bits).length = 2 * bits.length + 1 := by
  simp [blobSlots]; omega

def BlobRep (heap : Heap) (address : ℕ) (bits : Bits) : Prop :=
  Represents heap ⟨address, 2 * bits.length + 1⟩ (blobSlots bits)

def allocateBlob (heap : Heap) (bits : Bits) : ℕ × Heap :=
  (heap.size, allocateBlock heap (blobSlots bits))

theorem allocateBlob_correct (heap : Heap) (bits : Bits) :
    BlobRep (allocateBlob heap bits).2 (allocateBlob heap bits).1 bits := by
  simpa [BlobRep, allocateBlob, allocateTyped, blobSlots_length] using
    allocateTyped_represents heap (blobSlots bits)

theorem blobRep_persist {before after : Heap} (he : Extends before after)
    (a : ℕ) (bits : Bits) (h : BlobRep before a bits) : BlobRep after a bits :=
  represents_of_extends he _ _ h

def readLength : ℕ → Heap → ℕ → Option (ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, heap, address => do
      let slot ← read heap address
      match slot with
      | .ref _ => none
      | .bit false => some (0, address + 1)
      | .bit true => (readLength fuel heap (address + 1)).map fun out => (out.1 + 1, out.2)

theorem readLength_correct (heap : Heap) (a k fuel : ℕ) (hk : k < fuel)
    (ht : ∀ i < k, read heap (a + i) = some (.bit true))
    (hf : read heap (a + k) = some (.bit false)) :
    readLength fuel heap a = some (k, a + k + 1) := by
  induction k generalizing a fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [Nat.add_zero] at hf
      simp [readLength, hf]
  | succ k ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh : read heap a = some (.bit true) := by simpa using ht 0 (by omega)
      have hrec := ih (a + 1) fuel (by omega)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht (i + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
      simp [readLength, hh, hrec, Nat.add_assoc]
      omega

def readBlob (heap : Heap) (address : ℕ) : Option Bits := do
  let (length, data) ← readLength (heap.size + 1) heap address
  readWord heap ⟨data, length⟩

theorem readBlob_correct (heap : Heap) (a : ℕ) (bits : Bits) (h : BlobRep heap a bits) :
    readBlob heap a = some bits := by
  have hsize : a + (2 * bits.length + 1) ≤ heap.size := h.1
  have ht : ∀ i < bits.length, read heap (a + i) = some (.bit true) := by
    intro i hi
    have hread := h.2.2 i (by rw [blobSlots_length]; omega)
    simpa [blobSlots, List.getElem_append_left hi, hi] using hread
  have hf : read heap (a + bits.length) = some (.bit false) := by
    have hread := h.2.2 bits.length (by rw [blobSlots_length]; omega)
    simpa [blobSlots] using hread
  have hl := readLength_correct heap a bits.length (heap.size + 1) (by omega) ht hf
  have hw : WordRep heap ⟨a + bits.length + 1, bits.length⟩ bits := by
    refine ⟨by simp; omega, by simp, ?_⟩
    intro i hi
    have hii : i < bits.length := by simpa using hi
    have hread := h.2.2 (bits.length + 1 + i) (by rw [blobSlots_length]; omega)
    simp only [blobSlots] at hread
    rw [List.getElem_append_right (by simp; omega)] at hread
    simp only [List.length_replicate] at hread
    have hindex : bits.length + (1 + i) - bits.length = i + 1 := by omega
    simpa only [Nat.add_assoc, hindex, List.getElem_cons_succ, List.getElem_map] using hread
  simp [readBlob, hl, readWord_correct heap _ bits hw]

def encodeKey (q : WireKey) : Bits := encodeNat q.1 ++ encodeNats q.2

def parseKey (bits : Bits) : Option WireKey := do
  let (count, rest) ← parseNat bits
  let (row, tail) ← parseNats rest
  if tail = [] then some (count, row) else none

@[simp] theorem parseKey_encode (q : WireKey) : parseKey (encodeKey q) = some q := by
  rcases q with ⟨k, row⟩
  have hr := parseNats_append row []
  simp only [List.append_nil] at hr
  simp [parseKey, encodeKey, parseNat_append, hr]

theorem encodeKey_injective : Function.Injective encodeKey := by
  intro p q h
  have hh := congrArg parseKey h
  simpa using hh

def encodeAnswer : WireAnswer → Bits
  | none => [false]
  | some rows => true :: encodeMatrix rows

def parseAnswer : Bits → Option WireAnswer
  | [] => none
  | false :: rest => if rest = [] then some none else none
  | true :: rest => (parseMatrix rest).map some

@[simp] theorem parseAnswer_encode (answer : WireAnswer) :
    parseAnswer (encodeAnswer answer) = some answer := by
  cases answer <;> simp [parseAnswer, encodeAnswer]

def KeyRep (heap : Heap) (a : ℕ) (q : WireKey) : Prop := BlobRep heap a (encodeKey q)
def AnswerRep (heap : Heap) (a : ℕ) (answer : WireAnswer) : Prop :=
  BlobRep heap a (encodeAnswer answer)

def readKey (heap : Heap) (a : ℕ) : Option WireKey := (readBlob heap a).bind parseKey
def readAnswer (heap : Heap) (a : ℕ) : Option WireAnswer := (readBlob heap a).bind parseAnswer

@[simp] theorem readKey_correct (heap : Heap) (a : ℕ) (q : WireKey) (h : KeyRep heap a q) :
    readKey heap a = some q := by simp [readKey, readBlob_correct heap a (encodeKey q) h]

@[simp] theorem readAnswer_correct (heap : Heap) (a : ℕ) (answer : WireAnswer)
    (h : AnswerRep heap a answer) : readAnswer heap a = some answer := by
  simp [readAnswer, readBlob_correct heap a (encodeAnswer answer) h]

inductive CacheRep (heap : Heap) : ℕ → WireCache → Prop
  | nil (a : ℕ) (header : Represents heap ⟨a, 1⟩ [.bit false]) : CacheRep heap a []
  | cons (a key answer tail : ℕ) (q : WireKey) (ans : WireAnswer) (cs : WireCache)
      (header : Represents heap ⟨a, 4⟩ [.bit true, .ref key, .ref answer, .ref tail])
      (key_rep : KeyRep heap key q) (answer_rep : AnswerRep heap answer ans)
      (tail_rep : CacheRep heap tail cs) (tail_lt : tail < a) :
      CacheRep heap a ((q, ans) :: cs)

theorem cacheRep_persist {before after : Heap} (he : Extends before after)
    (a : ℕ) (cs : WireCache) (h : CacheRep before a cs) : CacheRep after a cs := by
  induction h with
  | nil a hh => exact CacheRep.nil a (represents_of_extends he _ _ hh)
  | cons a key answer tail q ans cs hh hk ha ht hl ih =>
    exact CacheRep.cons a key answer tail q ans cs (represents_of_extends he _ _ hh)
      (blobRep_persist he _ _ hk) (blobRep_persist he _ _ ha) ih hl

def bitsEq : Bits → Bits → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && bitsEq as bs
  | _, _ => false

@[simp] theorem bitsEq_eq_true (xs ys : Bits) : bitsEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys <;> cases ys <;> simp_all [bitsEq]

def lookupWire : WireCache → WireKey → Option WireAnswer
  | [], _ => none
  | (q, answer) :: cs, query => if q = query then some answer else lookupWire cs query

def lookupStore : ℕ → Heap → ℕ → Bits → Option (Option WireAnswer)
  | 0, _, _, _ => none
  | fuel + 1, heap, address, query => do
      let tag ← read heap address
      match tag with
      | .ref _ => none
      | .bit false => some none
      | .bit true =>
        let .ref key ← read heap (address + 1) | none
        let .ref answer ← read heap (address + 2) | none
        let .ref tail ← read heap (address + 3) | none
        let bits ← readBlob heap key
        if bitsEq bits query then
          (readAnswer heap answer).map some
        else lookupStore fuel heap tail query

theorem lookupStore_correct (heap : Heap) (a : ℕ) (cs : WireCache)
    (h : CacheRep heap a cs) (query : WireKey) (fuel : ℕ) (hf : a < fuel) :
    lookupStore fuel heap a (encodeKey query) = some (lookupWire cs query) := by
  induction h generalizing fuel with
  | nil a hh =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h₀ : read heap a = some (.bit false) := by simpa using hh.2.2 0 (by simp)
      simp [lookupStore, lookupWire, h₀]
  | cons a key answer tail q ans cs hh hk ha ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h₀ : read heap a = some (.bit true) := by simpa using hh.2.2 0 (by simp)
      have h₁ : read heap (a + 1) = some (.ref key) := by simpa using hh.2.2 1 (by simp)
      have h₂ : read heap (a + 2) = some (.ref answer) := by simpa using hh.2.2 2 (by simp)
      have h₃ : read heap (a + 3) = some (.ref tail) := by simpa using hh.2.2 3 (by simp)
      have hq : bitsEq (encodeKey q) (encodeKey query) = true ↔ q = query :=
        (bitsEq_eq_true _ _).trans encodeKey_injective.eq_iff
      simp only [lookupStore, bind, Option.bind, h₀, h₁, h₂, h₃,
        readBlob_correct heap key (encodeKey q) hk, readAnswer_correct heap answer ans ha]
      by_cases he : q = query
      · simp [lookupWire, he]
      · have hb : bitsEq (encodeKey q) (encodeKey query) = false := Bool.eq_false_iff.mpr (fun h => he (hq.mp h))
        simp [hb, lookupWire, he, ih fuel (by omega)]

def emptyCache (heap : Heap) : ℕ × Heap := (heap.size, allocateBlock heap [.bit false])

theorem emptyCache_correct (heap : Heap) : CacheRep (emptyCache heap).2 (emptyCache heap).1 [] := by
  apply CacheRep.nil
  simpa [emptyCache, allocateTyped] using allocateTyped_represents heap [.bit false]

def prependCache (heap : Heap) (key answer tail : ℕ) : ℕ × Heap :=
  (heap.size, allocateBlock heap [.bit true, .ref key, .ref answer, .ref tail])

theorem prependCache_correct (heap : Heap) (key answer tail : ℕ)
    (q : WireKey) (ans : WireAnswer) (cs : WireCache)
    (hk : KeyRep heap key q) (ha : AnswerRep heap answer ans) (ht : CacheRep heap tail cs)
    (hl : tail < heap.size) :
    CacheRep (prependCache heap key answer tail).2 (prependCache heap key answer tail).1 ((q, ans) :: cs) := by
  have he := allocateBlock_extends heap [.bit true, .ref key, .ref answer, .ref tail]
  apply CacheRep.cons heap.size key answer tail q ans cs
  · simpa [prependCache, allocateTyped] using
      allocateTyped_represents heap [.bit true, .ref key, .ref answer, .ref tail]
  · exact blobRep_persist he key _ hk
  · exact blobRep_persist he answer _ ha
  · exact cacheRep_persist he tail cs ht
  · exact hl

theorem prependCache_shares (heap : Heap) (key answer tail : ℕ) :
    read (prependCache heap key answer tail).2 (heap.size + 1) = some (.ref key) ∧
    read (prependCache heap key answer tail).2 (heap.size + 2) = some (.ref answer) ∧
    read (prependCache heap key answer tail).2 (heap.size + 3) = some (.ref tail) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [prependCache] using read_allocateBlock_new heap
      [.bit true, .ref key, .ref answer, .ref tail] 1 (by simp)
  · simpa [prependCache] using read_allocateBlock_new heap
      [.bit true, .ref key, .ref answer, .ref tail] 2 (by simp)
  · simpa [prependCache] using read_allocateBlock_new heap
      [.bit true, .ref key, .ref answer, .ref tail] 3 (by simp)

def decodeCacheStore : ℕ → Heap → ℕ → Option WireCache
  | 0, _, _ => none
  | fuel + 1, heap, address => do
      let tag ← read heap address
      match tag with
      | .ref _ => none
      | .bit false => some []
      | .bit true =>
        let .ref key ← read heap (address + 1) | none
        let .ref answer ← read heap (address + 2) | none
        let .ref tail ← read heap (address + 3) | none
        let q ← readKey heap key
        let ans ← readAnswer heap answer
        let cs ← decodeCacheStore fuel heap tail
        some ((q, ans) :: cs)

theorem decodeCacheStore_correct (heap : Heap) (a : ℕ) (cs : WireCache)
    (h : CacheRep heap a cs) (fuel : ℕ) (hf : a < fuel) :
    decodeCacheStore fuel heap a = some cs := by
  induction h generalizing fuel with
  | nil a hh =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h₀ : read heap a = some (.bit false) := by simpa using hh.2.2 0 (by simp)
      simp [decodeCacheStore, h₀]
  | cons a key answer tail q ans cs hh hk ha ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h₀ : read heap a = some (.bit true) := by simpa using hh.2.2 0 (by simp)
      have h₁ : read heap (a + 1) = some (.ref key) := by simpa using hh.2.2 1 (by simp)
      have h₂ : read heap (a + 2) = some (.ref answer) := by simpa using hh.2.2 2 (by simp)
      have h₃ : read heap (a + 3) = some (.ref tail) := by simpa using hh.2.2 3 (by simp)
      simp [decodeCacheStore, bind, Option.bind, h₀, h₁, h₂, h₃,
        readKey_correct heap key q hk, readAnswer_correct heap answer ans ha, ih fuel (by omega)]

theorem blobRep_address_lt (heap : Heap) (a : ℕ) (bits : Bits) (h : BlobRep heap a bits) :
    a < heap.size := by
  have hh := h.1
  dsimp only at hh
  omega

theorem cacheRep_address_lt (heap : Heap) (a : ℕ) (cs : WireCache) (h : CacheRep heap a cs) :
    a < heap.size := by
  cases h with
  | nil a hh => have hh' := hh.1; dsimp only at hh'; omega
  | cons a key answer tail q ans cs hh hk ha ht hl =>
    have hh' := hh.1
    dsimp only at hh'
    omega

theorem allocateBlob_wellFormed (heap : Heap) (bits : Bits) (hh : WellFormed heap) :
    WellFormed (allocateBlob heap bits).2 := by
  apply wellFormed_allocateBlock heap _ hh
  intro a ha
  simp [blobSlots] at ha

theorem prependCache_wellFormed (heap : Heap) (key answer tail : ℕ) (hh : WellFormed heap)
    (hk : key < heap.size) (ha : answer < heap.size) (ht : tail < heap.size) :
    WellFormed (prependCache heap key answer tail).2 := by
  apply wellFormed_allocateBlock heap _ hh
  intro a ha'
  simp at ha'
  rcases ha' with rfl | rfl | rfl <;> assumption

/-- The concrete payload schema for the existing vector cache. -/
def wireKey {n : ℕ} (q : TreeBudgetVectorMemoState.KeyV n) : WireKey := (q.1, q.2.toList)
def wireAnswer {n : ℕ} (a : TreeBudgetVectorMemoState.AnswerV n) : WireAnswer :=
  a.map (fun rows => rows.map Vector.toList)
def wireCache {n : ℕ} (cs : TreeBudgetVectorMemoState.CacheV n) : WireCache :=
  cs.map (fun e => (wireKey e.1, wireAnswer e.2))

theorem keyEqB_wire {n : ℕ} (p q : TreeBudgetVectorMemoState.KeyV n) :
    TreeBudgetVectorMemoState.keyEqB p q = decide (wireKey p = wireKey q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [TreeBudgetVectorMemoState.keyEqB_eq_true, decide_eq_true_eq,
    wireKey, TreeBudgetVectorMemoState.decodeKey, Prod.mk.injEq,
    Vector.toList_inj, TreeBudgetVector.decode_injective.eq_iff]

theorem lookupWire_vector {n : ℕ} (cs : TreeBudgetVectorMemoState.CacheV n)
    (q : TreeBudgetVectorMemoState.KeyV n) :
    lookupWire (wireCache cs) (wireKey q) = (TreeBudgetVectorMemoState.lookupV cs q).map wireAnswer := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [wireCache, List.map_cons, lookupWire, TreeBudgetVectorMemoState.lookupV,
      keyEqB_wire, decide_eq_true_eq]
    split
    · rfl
    · exact ih

theorem lookupStore_vector {n : ℕ} (heap : Heap) (a : ℕ)
    (cs : TreeBudgetVectorMemoState.CacheV n) (h : CacheRep heap a (wireCache cs))
    (q : TreeBudgetVectorMemoState.KeyV n) (fuel : ℕ) (hf : a < fuel) :
    lookupStore fuel heap a (encodeKey (wireKey q)) =
      some ((TreeBudgetVectorMemoState.lookupV cs q).map wireAnswer) := by
  rw [lookupStore_correct heap a (wireCache cs) h (wireKey q) fuel hf, lookupWire_vector]

end UAVProof.TreeBudgetSearchStore
