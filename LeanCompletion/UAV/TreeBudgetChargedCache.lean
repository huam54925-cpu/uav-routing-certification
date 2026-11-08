import LeanCompletion.UAV.TreeBudgetSharedAnswerStore
import LeanCompletion.UAV.TreeBudgetStoredCursor

/-! Addressed ordered caches with shared answers. `Costed.allocations` counts
auxiliary workspace cells as well as writes; actual heap growth is proved
separately. The dynamic-width accessors measure their address words before
using the addressed primitives. A uniform input-based width is a later theorem.
Neither cache decoding nor an abstract cache is used by the executable lookup
or filter. Fuel is a control cursor, and every recursive frame is charged. -/
namespace UAVProof.TreeBudgetChargedCache
open TreeBudgetStoredCursor
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetBitMachine
open TreeBudgetAddressedBlocks TreeBudgetSearchStore TreeBudgetSharedAnswerStore
open TreeBudgetBinaryCodec TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing

def ret {α : Type} (a : α) : Costed (Option α) := ⟨some a, 1, 0⟩
def bad {α : Type} : Costed (Option α) := ⟨none, 1, 0⟩

@[simp] theorem costBind_value {α β : Type} (out : Costed α) (f : α → Costed β) :
    (TreeBudgetBitMachine.bind out f).value = (f out.value).value := rfl

/-- Width measurement is executed, including its unary workspace. -/
def load (heap : Heap) (a : ℕ) : Costed (Option Slot) :=
  let w := widthNat a
  let out := readCellD w.value heap a
  ⟨out.value, w.steps + out.steps + 1, w.allocations + out.allocations⟩

@[simp] theorem load_value (heap : Heap) (a : ℕ) (hh : WellFormed heap) :
    (load heap a).value = read heap a := by
  simp [load, (widthNat_spec a).1, readCellD_value _ heap a hh (Nat.lt_size_self a)]

def loadOffset (heap : Heap) (a offset : ℕ) : Costed (Option Slot) :=
  TreeBudgetBitMachine.bind (addNatD a offset) (load heap)

@[simp] theorem loadOffset_value (heap : Heap) (a offset : ℕ) (hh : WellFormed heap) :
    (loadOffset heap a offset).value = read heap (a + offset) := by
  simp [loadOffset, TreeBudgetBitMachine.bind, hh]

def loadRef (heap : Heap) (a offset : ℕ) : Costed (Option ℕ) :=
  thenD (loadOffset heap a offset) fun slot => match slot with
  | .ref r => ret r
  | .bit _ => bad

@[simp] theorem loadRef_value (heap : Heap) (a offset r : ℕ) (hh : WellFormed heap)
    (hr : read heap (a + offset) = some (.ref r)) :
    (loadRef heap a offset).value = some r := by
  simp [loadRef, hh, hr, ret]

/-- Dynamic allocation widths are computed from the actual new endpoint. -/
def alloc (heap : Heap) (slots : List Slot) : Costed (ℕ × Heap) :=
  let len := lengthD slots
  let top := addNatD heap.size len.value
  let w := widthNat top.value
  let out := nodeD w.value heap slots
  ⟨out.value, len.steps + top.steps + w.steps + out.steps + 3,
    len.allocations + top.allocations + w.allocations + out.allocations⟩

theorem alloc_value (heap : Heap) (slots : List Slot)
    (href : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    (alloc heap slots).value = (heap.size, allocateBlock heap slots) := by
  simp only [alloc, lengthD_value, addNatD_value, (widthNat_spec _).1]
  exact nodeD_value _ heap slots (Nat.lt_size_self _) href

def lengthRead (fuel : ℕ) (heap : Heap) (a : ℕ) : Costed (Option (ℕ × ℕ)) :=
  thenD (cursorStep fuel) fun remaining =>
    thenD (load heap a) fun slot =>
    match slot with
    | .ref _ => bad
    | .bit false => TreeBudgetBitMachine.bind (addNatD a 1) fun next => ret (0, next)
    | .bit true => TreeBudgetBitMachine.bind (addNatD a 1) fun next =>
      thenD (lengthRead remaining.val heap next) fun out =>
        TreeBudgetBitMachine.bind (addNatD out.1 1) fun len =>
          charge 1 2 (ret (len, out.2))
termination_by fuel
decreasing_by exact remaining.isLt

theorem lengthRead_succ_value (fuel : ℕ) (heap : Heap) (a : ℕ) :
    (lengthRead (fuel + 1) heap a).value =
      (thenD (load heap a) fun slot =>
    match slot with
    | .ref _ => bad
    | .bit false => TreeBudgetBitMachine.bind (addNatD a 1) fun next => ret (0, next)
    | .bit true => TreeBudgetBitMachine.bind (addNatD a 1) fun next =>
      thenD (lengthRead fuel heap next) fun out =>
        TreeBudgetBitMachine.bind (addNatD out.1 1) fun len =>
          charge 1 2 (ret (len, out.2))).value := by
  rw [lengthRead]
  simp only [thenD_value, cursorStep_succ, Option.bind_some]


theorem lengthRead_value (fuel : ℕ) (heap : Heap) (a : ℕ) (hh : WellFormed heap) :
    (lengthRead fuel heap a).value = readLength fuel heap a := by
  induction fuel generalizing a with
  | zero => rw [lengthRead]; simp [readLength]
  | succ fuel ih =>
    simp only [lengthRead_succ_value, thenD_value, cursorStep_succ, Option.bind_some, load_value _ _ hh, readLength]
    cases hr : read heap a with
    | none => rfl
    | some slot =>
      cases slot with
      | ref r => rfl
      | bit b =>
        cases b <;> simp [TreeBudgetBitMachine.bind, ih, ret, charge]
        cases readLength fuel heap (a + 1) <;> rfl

def blobRead (heap : Heap) (a : ℕ) : Costed (Option Bits) :=
  TreeBudgetBitMachine.bind (addNatD heap.size 1) fun fuel =>
  thenD (lengthRead fuel heap a) fun out =>
    let top := addNatD out.2 out.1
    let w := widthNat top.value
    let data := readWordD w.value heap ⟨out.2, out.1⟩
    ⟨data.value, top.steps + w.steps + data.steps + 2,
      top.allocations + w.allocations + data.allocations⟩

theorem blobRead_value (heap : Heap) (a : ℕ) (hh : WellFormed heap) :
    (blobRead heap a).value = readBlob heap a := by
  simp only [blobRead, costBind_value, addNatD_value, thenD_value, lengthRead_value _ _ _ hh, readBlob]
  cases he : readLength (heap.size + 1) heap a with
  | none => rfl
  | some out =>
    simp only [Option.bind_some, addNatD_value, (widthNat_spec _).1,
      readWordD, readBlockD_value _ _ _ _ hh (Nat.lt_size_self _).le, readWord]
    simp only [Bind.bind, Option.bind_some]
    cases readSlots heap out.2 out.1 <;> simp [decodeWordD_value]

theorem blobRead_correct (heap : Heap) (a : ℕ) (bits : Bits) (hh : WellFormed heap)
    (hr : BlobRep heap a bits) : (blobRead heap a).value = some bits := by
  rw [blobRead_value _ _ hh, readBlob_correct _ _ _ hr]

def keyRead (heap : Heap) (a : ℕ) : Costed (Option WireKey) :=
  thenD (blobRead heap a) fun bits =>
    thenD (parseNatD bits) fun count =>
      thenD (parseNatsD count.2) fun row =>
        match row.2 with
        | [] => ret (count.1, row.1)
        | _ :: _ => bad

theorem keyRead_correct (heap : Heap) (a : ℕ) (q : WireKey)
    (hh : WellFormed heap) (hr : KeyRep heap a q) :
    (keyRead heap a).value = some q := by
  rcases q with ⟨k, row⟩
  have hp := parseNats_append row []
  simp only [List.append_nil] at hp
  simp [keyRead, blobRead_correct _ _ _ hh hr, encodeKey, parseNat_append, hp, ret]

inductive CacheRep (heap : Heap) : ℕ → WireCache → Prop
  | nil (a : ℕ) (header : Represents heap ⟨a, 1⟩ [.bit false]) : CacheRep heap a []
  | cons (a key answer tail : ℕ) (q : WireKey) (ans : WireAnswer) (cs : WireCache)
      (header : Represents heap ⟨a, 4⟩ [.bit true, .ref key, .ref answer, .ref tail])
      (key_rep : KeyRep heap key q) (answer_rep : SharedAnswerRep heap answer ans)
      (tail_rep : CacheRep heap tail cs) (tail_lt : tail < a) :
      CacheRep heap a ((q, ans) :: cs)

theorem cacheRep_persist {before after : Heap} (he : Extends before after)
    {a : ℕ} {cs : WireCache} (h : CacheRep before a cs) : CacheRep after a cs := by
  induction h with
  | nil a hh => exact .nil a (represents_of_extends he _ _ hh)
  | cons a k v t q ans cs hh hk hv ht hl ih =>
    exact .cons a k v t q ans cs (represents_of_extends he _ _ hh)
      (blobRep_persist he _ _ hk) (answerRep_persist he _ _ hv) ih hl

theorem cacheRep_address_lt {heap : Heap} {a : ℕ} {cs : WireCache}
    (h : CacheRep heap a cs) : a < heap.size := by
  cases h with
  | nil a hh => have hb := hh.1; dsimp at hb; omega
  | cons a k v t q ans cs hh hk hv ht hl => have hb := hh.1; dsimp at hb; omega

def headRead (heap : Heap) (a : ℕ) : Costed (Option (Option (ℕ × ℕ × ℕ))) :=
  thenD (load heap a) fun slot => match slot with
  | .ref _ => bad
  | .bit false => ret none
  | .bit true => thenD (loadRef heap a 1) fun k =>
      thenD (loadRef heap a 2) fun v => thenD (loadRef heap a 3) fun t =>
        ret (some (k, v, t))

theorem headRead_nil (heap : Heap) (a : ℕ) (hh : WellFormed heap)
    (hr : Represents heap ⟨a, 1⟩ [.bit false]) :
    (headRead heap a).value = some none := by
  have h₀ : read heap a = some (.bit false) := by simpa using hr.2.2 0 (by simp)
  simp [headRead, hh, h₀, ret]

theorem headRead_cons (heap : Heap) (a k v t : ℕ) (hh : WellFormed heap)
    (hr : Represents heap ⟨a, 4⟩ [.bit true, .ref k, .ref v, .ref t]) :
    (headRead heap a).value = some (some (k, v, t)) := by
  have h₀ : read heap a = some (.bit true) := by simpa using hr.2.2 0 (by simp)
  have h₁ : read heap (a + 1) = some (.ref k) := hr.2.2 1 (by simp)
  have h₂ : read heap (a + 2) = some (.ref v) := hr.2.2 2 (by simp)
  have h₃ : read heap (a + 3) = some (.ref t) := hr.2.2 3 (by simp)
  simp [headRead, hh, h₀, loadRef_value _ _ _ _ hh h₁,
    loadRef_value _ _ _ _ hh h₂, loadRef_value _ _ _ _ hh h₃, ret]

def lookupD (fuel : ℕ) (heap : Heap) (a : ℕ) (query : Bits) : Costed (Option (Option ℕ × ℕ)) :=
  thenD (cursorStep fuel) fun remaining =>
    thenD (headRead heap a) fun node =>
    match node with
    | none => ret (none, 0)
    | some (k, v, t) => thenD (blobRead heap k) fun bits =>
      TreeBudgetBitMachine.bind (eqBitsD bits query) fun same =>
        if same then ret (some v, 1) else
          thenD (lookupD remaining.val heap t query) fun out => ret (out.1, out.2 + 1)
termination_by fuel
decreasing_by exact remaining.isLt

theorem lookupD_succ_value (fuel : ℕ) (heap : Heap) (a : ℕ) (query : Bits) :
    (lookupD (fuel + 1) heap a query).value =
      (thenD (headRead heap a) fun node =>
    match node with
    | none => ret (none, 0)
    | some (k, v, t) => thenD (blobRead heap k) fun bits =>
      TreeBudgetBitMachine.bind (eqBitsD bits query) fun same =>
        if same then ret (some v, 1) else
          thenD (lookupD fuel heap t query) fun out => ret (out.1, out.2 + 1)).value := by
  rw [lookupD]
  simp only [thenD_value, cursorStep_succ, Option.bind_some]


def lookupCount : WireCache → WireKey → ℕ
  | [], _ => 0
  | (k, _) :: cs, q => if k = q then 1 else lookupCount cs q + 1

def FoundRep (heap : Heap) : Option ℕ → Option WireAnswer → Prop
  | none, none => True
  | some r, some ans => SharedAnswerRep heap r ans
  | _, _ => False

theorem lookupD_correct (heap : Heap) (a : ℕ) (cs : WireCache)
    (hh : WellFormed heap) (hr : CacheRep heap a cs) (q : WireKey)
    (fuel : ℕ) (hf : a < fuel) :
    ∃ result, (lookupD fuel heap a (encodeKey q)).value = some (result, lookupCount cs q) ∧
      FoundRep heap result (lookupWire cs q) := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨none, by simp [lookupD_succ_value, headRead_nil _ _ hh header, ret, lookupCount], trivial⟩
  | cons a k v t key ans cs header hk hv ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [lookupD_succ_value, thenD_value, cursorStep_succ, headRead_cons _ _ _ _ _ hh header, Option.bind_some,
        blobRead_correct _ _ _ hh hk, TreeBudgetBitMachine.bind, eqBitsD_value,
        encodeKey_injective.eq_iff]
      by_cases he : key = q
      · exact ⟨some v, by simp [he, ret, lookupCount], by simpa [FoundRep, lookupWire, he] using hv⟩
      · obtain ⟨result, hresult, hrep⟩ := ih fuel (by omega)
        exact ⟨result, by simp [he, hresult, ret, lookupCount], by simpa [lookupWire, he] using hrep⟩

def keep (cs : WireCache) (q : WireKey) : WireCache := cs.filter (fun e => decide (e.1 ≠ q))

def filterD (fuel : ℕ) (heap : Heap) (a : ℕ) (query : Bits) : Costed (Option ((ℕ × Heap) × ℕ)) :=
  thenD (cursorStep fuel) fun remaining =>
    thenD (headRead heap a) fun node =>
    match node with
    | none => ret ((a, heap), 0)
    | some (k, v, t) => thenD (blobRead heap k) fun bits =>
      TreeBudgetBitMachine.bind (eqBitsD bits query) fun same =>
        charge 1 4 <| thenD (filterD remaining.val heap t query) fun out =>
          if same then ret (out.1, out.2 + 1) else
            TreeBudgetBitMachine.bind
              (alloc out.1.2 [.bit true, .ref k, .ref v, .ref out.1.1]) fun fresh =>
                ret (fresh, out.2 + 1)
termination_by fuel
decreasing_by exact remaining.isLt

theorem filterD_succ_value (fuel : ℕ) (heap : Heap) (a : ℕ) (query : Bits) :
    (filterD (fuel + 1) heap a query).value =
      (thenD (headRead heap a) fun node =>
    match node with
    | none => ret ((a, heap), 0)
    | some (k, v, t) => thenD (blobRead heap k) fun bits =>
      TreeBudgetBitMachine.bind (eqBitsD bits query) fun same =>
        charge 1 4 <| thenD (filterD fuel heap t query) fun out =>
          if same then ret (out.1, out.2 + 1) else
            TreeBudgetBitMachine.bind
              (alloc out.1.2 [.bit true, .ref k, .ref v, .ref out.1.1]) fun fresh =>
                ret (fresh, out.2 + 1)).value := by
  rw [filterD]
  simp only [thenD_value, cursorStep_succ, Option.bind_some]


theorem cons_correct (heap : Heap) (k v t : ℕ) (q : WireKey) (ans : WireAnswer)
    (cs : WireCache) (hk : KeyRep heap k q) (hv : SharedAnswerRep heap v ans)
    (ht : CacheRep heap t cs) :
    CacheRep (allocateBlock heap [.bit true, .ref k, .ref v, .ref t]) heap.size ((q, ans) :: cs) := by
  have he := allocateBlock_extends heap [.bit true, .ref k, .ref v, .ref t]
  exact .cons heap.size k v t q ans cs (allocateTyped_represents heap [.bit true, .ref k, .ref v, .ref t])
    (blobRep_persist he _ _ hk) (answerRep_persist he _ _ hv)
    (cacheRep_persist he ht) (cacheRep_address_lt ht)

theorem filterD_correct (heap : Heap) (a : ℕ) (cs : WireCache)
    (hh : WellFormed heap) (hr : CacheRep heap a cs) (q : WireKey)
    (fuel : ℕ) (hf : a < fuel) :
    ∃ root after, (filterD fuel heap a (encodeKey q)).value = some ((root, after), cs.length) ∧
      CacheRep after root (keep cs q) ∧ WellFormed after ∧ Extends heap after ∧
      after.size = heap.size + 4 * (keep cs q).length := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      refine ⟨a, heap, ?_, .nil a header, hh, extends_refl heap, ?_⟩
      · simp [filterD_succ_value, headRead_nil _ _ hh header, ret]
      · simp [keep]
  | cons a k v t key ans cs header hk hv ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨root, after, hout, hrep, hwf, hext, hsize⟩ := ih fuel (by omega)
      have hk' := blobRep_persist hext _ _ hk
      have hv' := answerRep_persist hext _ _ hv
      have hbK := blobRep_address_lt _ _ _ hk'
      have hbV := answerRep_address_lt hv'
      have hbT := cacheRep_address_lt hrep
      have href : ∀ r, Slot.ref r ∈ [.bit true, .ref k, .ref v, .ref root] → r < after.size := by
        intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> assumption
      have ha := alloc_value after [.bit true, .ref k, .ref v, .ref root] href
      simp only [filterD_succ_value, thenD_value, cursorStep_succ, headRead_cons _ _ _ _ _ hh header, Option.bind_some,
        blobRead_correct _ _ _ hh hk, TreeBudgetBitMachine.bind, eqBitsD_value,
        encodeKey_injective.eq_iff, charge, hout]
      by_cases hsame : key = q
      · refine ⟨root, after, ?_, ?_, hwf, hext, ?_⟩
        · simp [hsame, ret]
        · simpa [keep, hsame] using hrep
        · simpa [keep, hsame] using hsize
      · refine ⟨after.size, allocateBlock after [.bit true, .ref k, .ref v, .ref root],
          ?_, ?_, wellFormed_allocateBlock after _ hwf href,
          extends_trans hext (allocateBlock_extends ..), ?_⟩
        · simp [hsame, ha, ret]
        · simpa [keep, hsame] using cons_correct after k v root key ans (keep cs q) hk' hv' hrep
        · simp only [allocateBlock_size, List.length_cons, List.length_nil]
          simp [keep, hsame] at hsize ⊢
          omega

def insertD (heap : Heap) (a key answer : ℕ) : Costed (Option ((ℕ × Heap) × ℕ)) :=
  thenD (blobRead heap key) fun query =>
    TreeBudgetBitMachine.bind (addNatD heap.size 1) fun fuel =>
    thenD (filterD fuel heap a query) fun out =>
      TreeBudgetBitMachine.bind
        (alloc out.1.2 [.bit true, .ref key, .ref answer, .ref out.1.1]) fun fresh =>
          ret (fresh, out.2)

theorem insertD_correct (heap : Heap) (a key answer : ℕ) (cs : WireCache)
    (q : WireKey) (ans : WireAnswer) (hh : WellFormed heap)
    (hc : CacheRep heap a cs) (hk : KeyRep heap key q) (hv : SharedAnswerRep heap answer ans) :
    ∃ root after, (insertD heap a key answer).value = some ((root, after), cs.length) ∧
      CacheRep after root ((q, ans) :: keep cs q) ∧ WellFormed after ∧ Extends heap after ∧
      after.size = heap.size + 4 * (keep cs q).length + 4 := by
  obtain ⟨root, after, hout, hrep, hwf, hext, hsize⟩ :=
    filterD_correct heap a cs hh hc q (heap.size + 1) (by have := cacheRep_address_lt hc; omega)
  have hk' := blobRep_persist hext _ _ hk
  have hv' := answerRep_persist hext _ _ hv
  have hbK := blobRep_address_lt _ _ _ hk'
  have hbV := answerRep_address_lt hv'
  have hbT := cacheRep_address_lt hrep
  have href : ∀ r, Slot.ref r ∈ [.bit true, .ref key, .ref answer, .ref root] → r < after.size := by
    intro r hr; simp at hr; rcases hr with rfl | rfl | rfl <;> assumption
  refine ⟨after.size, allocateBlock after [.bit true, .ref key, .ref answer, .ref root],
    ?_, cons_correct after key answer root q ans (keep cs q) hk' hv' hrep,
    wellFormed_allocateBlock after _ hwf href, extends_trans hext (allocateBlock_extends ..), ?_⟩
  · simp [insertD, blobRead_correct _ _ _ hh hk, hout, TreeBudgetBitMachine.bind,
      alloc_value after _ href, ret]
  · simp [allocateBlock_size, hsize]

theorem keep_vector {n : ℕ} (cs : TreeBudgetVectorMemoState.CacheV n)
    (q : TreeBudgetVectorMemoState.KeyV n) :
    keep (wireCache cs) (wireKey q) =
      wireCache (cs.filter (fun e => !(TreeBudgetVectorMemoState.keyEqB e.1 q))) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [keep, wireCache, List.map_cons, List.filter_cons, keyEqB_wire] at *
    by_cases h : wireKey e.1 = wireKey q <;> simpa [h] using ih

end UAVProof.TreeBudgetChargedCache
