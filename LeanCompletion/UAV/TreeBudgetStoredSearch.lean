import LeanCompletion.UAV.TreeBudgetChargedCache
import LeanCompletion.UAV.TreeBudgetCostedSearch

/-! Pointer-driven search. Persistent vectors, keys, candidates, answers, caches
and continuation frames live in the append-only heap. Binary arithmetic and
codec buffers use the existing costed auxiliary workspace semantics. Events
are proof observations, not machine output. This file does not assert a total
time bound or an input-bitstream refinement. -/
namespace UAVProof.TreeBudgetStoredSearch
open TreeBudgetStoredCursor
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetBitMachine
open TreeBudgetSearchStore TreeBudgetSharedAnswerStore TreeBudgetChargedCache
open TreeBudgetBinaryCodec TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetSearchStats TreeBudgetVectorMemoState

def vectorRead (n : ℕ) (heap : Heap) (a : ℕ) : Costed (Option (Vector ℕ n)) :=
  thenD (blobRead heap a) fun bits => thenD (parseNatsD bits) fun out =>
    match out.2 with
    | _ :: _ => bad
    | [] =>
      let len := lengthD out.1
      let same := eqNatD len.value n
      if h : same.value = true then
        ⟨some ⟨out.1.toArray, by simpa [same, len] using h⟩,
          len.steps + same.steps + out.1.length + 1,
          len.allocations + same.allocations + out.1.length⟩
      else ⟨none, len.steps + same.steps + 1, len.allocations + same.allocations⟩

theorem vectorRead_correct {n : ℕ} (heap : Heap) (a : ℕ) (v : Vector ℕ n)
    (hh : WellFormed heap) (hr : RowRep heap a v.toList) :
    (vectorRead n heap a).value = some v := by
  have hp := parseNats_append v.toList []
  simp only [List.append_nil] at hp
  simp [vectorRead, blobRead_correct _ _ _ hh hr, hp]
  simp [Vector.toList]

def blobWrite (heap : Heap) (bits : Bits) : Costed (ℕ × Heap) :=
  let len := lengthD bits
  let slots := blobSlots bits
  let out := alloc heap slots
  ⟨out.value, len.steps + 2 * len.value + 1 + out.steps,
    len.allocations + 2 * len.value + 1 + out.allocations⟩

theorem blobWrite_value (heap : Heap) (bits : Bits) :
    (blobWrite heap bits).value = allocateBlob heap bits := by
  apply alloc_value
  simp [blobSlots]

def vectorWrite {n : ℕ} (heap : Heap) (v : Vector ℕ n) : Costed (ℕ × Heap) :=
  TreeBudgetBitMachine.bind (encodeNatsD v.toList) (blobWrite heap)

theorem vectorWrite_value {n : ℕ} (heap : Heap) (v : Vector ℕ n) :
    (vectorWrite heap v).value = allocateBlob heap (encodeNats v.toList) := by
  simp [vectorWrite, TreeBudgetBitMachine.bind, blobWrite_value]

def keyWrite {n : ℕ} (heap : Heap) (k : ℕ) (v : Vector ℕ n) : Costed (ℕ × Heap) :=
  TreeBudgetBitMachine.bind (encodeNatD k) fun count =>
    TreeBudgetBitMachine.bind (encodeNatsD v.toList) fun row =>
      TreeBudgetBitMachine.bind (appendD count row) (blobWrite heap)

theorem keyWrite_value {n : ℕ} (heap : Heap) (k : ℕ) (v : Vector ℕ n) :
    (keyWrite heap k v).value = allocateBlob heap (encodeKey (k, v.toList)) := by
  simp [keyWrite, TreeBudgetBitMachine.bind, blobWrite_value, encodeKey]

/-- Shared row chains also represent the fixed candidate list and its suffixes. -/
abbrev CandidatesRep := RowsRep

def rowsHead (heap : Heap) (a : ℕ) : Costed (Option (Option (ℕ × ℕ))) :=
  thenD (load heap a) fun slot => match slot with
  | .ref _ => bad
  | .bit false => ret none
  | .bit true => thenD (loadRef heap a 1) fun row =>
      thenD (loadRef heap a 2) fun tail => ret (some (row, tail))

def answerHead (heap : Heap) (a : ℕ) : Costed (Option (Option ℕ)) :=
  thenD (load heap a) fun slot => match slot with
  | .ref _ => bad
  | .bit false => ret none
  | .bit true => thenD (loadRef heap a 1) fun rows => ret (some rows)

structure Result where
  answer : ℕ
  cache : ℕ
  heap : Heap
  events : Counts

def addEvents (events : Counts) (out : Costed (Option Result)) : Costed (Option Result) :=
  ⟨out.value.map (fun r => { r with events := events.add r.events }), out.steps, out.allocations⟩

/-- Frames borrow existing objects. The frame is reloaded after the child
returns, so the continuation uses the stored addresses. -/
def frameSlots (row tail residual parent : ℕ) : List Slot :=
  [.bit true, .ref row, .ref tail, .ref residual, .ref parent]

def FrameRep (heap : Heap) (frame row tail residual parent : ℕ) : Prop :=
  Represents heap ⟨frame, 5⟩ (frameSlots row tail residual parent)

inductive FramesRep (heap : Heap) : ℕ → Prop
  | root (a : ℕ) (header : Represents heap ⟨a, 1⟩ [.bit false]) : FramesRep heap a
  | memo (a key parent : ℕ)
      (header : Represents heap ⟨a, 3⟩ [.bit true, .ref key, .ref parent])
      (key_lt : key < a) (parent_lt : parent < a) (tail : FramesRep heap parent) : FramesRep heap a
  | scan (a row suffix residual parent : ℕ)
      (header : FrameRep heap a row suffix residual parent)
      (row_lt : row < a) (suffix_lt : suffix < a) (residual_lt : residual < a)
      (parent_lt : parent < a) (tail : FramesRep heap parent) : FramesRep heap a

theorem framesRep_persist {before after : Heap} (he : Extends before after)
    {a : ℕ} (hf : FramesRep before a) : FramesRep after a := by
  induction hf with
  | root a h => exact .root a (represents_of_extends he _ _ h)
  | memo a k p h hk hp ht ih => exact .memo a k p (represents_of_extends he _ _ h) hk hp ih
  | scan a r s v p h hr hs hv hp ht ih =>
    exact .scan a r s v p (represents_of_extends he _ _ h) hr hs hv hp ih

theorem allocate_scan_frame (heap : Heap) (row suffix residual parent : ℕ)
    (hr : row < heap.size) (hs : suffix < heap.size) (hv : residual < heap.size)
    (hp : parent < heap.size) (hf : FramesRep heap parent) :
    FramesRep (allocateBlock heap (frameSlots row suffix residual parent)) heap.size := by
  exact .scan heap.size row suffix residual parent (allocateTyped_represents heap (frameSlots row suffix residual parent))
    hr hs hv hp (framesRep_persist (allocateBlock_extends ..) hf)

theorem allocate_memo_frame (heap : Heap) (key parent : ℕ)
    (hk : key < heap.size) (hp : parent < heap.size) (hf : FramesRep heap parent) :
    FramesRep (allocateBlock heap [.bit true, .ref key, .ref parent]) heap.size := by
  exact .memo heap.size key parent (allocateTyped_represents heap [.bit true, .ref key, .ref parent])
    hk hp (framesRep_persist (allocateBlock_extends ..) hf)

def frameRead (heap : Heap) (frame : ℕ) : Costed (Option (ℕ × ℕ × ℕ × ℕ)) :=
  thenD (loadRef heap frame 1) fun row => thenD (loadRef heap frame 2) fun tail =>
    thenD (loadRef heap frame 3) fun residual => thenD (loadRef heap frame 4) fun parent =>
      ret (row, tail, residual, parent)

theorem frameRead_correct (heap : Heap) (frame row tail residual parent : ℕ)
    (hh : WellFormed heap) (hr : FrameRep heap frame row tail residual parent) :
    (frameRead heap frame).value = some (row, tail, residual, parent) := by
  have h₁ : read heap (frame + 1) = some (.ref row) := hr.2.2 1 (by simp [frameSlots])
  have h₂ : read heap (frame + 2) = some (.ref tail) := hr.2.2 2 (by simp [frameSlots])
  have h₃ : read heap (frame + 3) = some (.ref residual) := hr.2.2 3 (by simp [frameSlots])
  have h₄ : read heap (frame + 4) = some (.ref parent) := hr.2.2 4 (by simp [frameSlots])
  simp [frameRead, loadRef_value _ _ _ _ hh h₁, loadRef_value _ _ _ _ hh h₂,
    loadRef_value _ _ _ _ hh h₃, loadRef_value _ _ _ _ hh h₄, ret]

def failResult (heap : Heap) (cache : ℕ) : Costed (Option Result) :=
  TreeBudgetBitMachine.bind (alloc heap [.bit false]) fun out => ret ⟨out.1, cache, out.2, {}⟩

def zeroResult (n : ℕ) (heap : Heap) (residual cache : ℕ) : Costed (Option Result) :=
  thenD (vectorRead n heap residual) fun r => TreeBudgetBitMachine.bind (zeroV r) fun z =>
    if z then TreeBudgetBitMachine.bind (alloc heap [.bit false]) fun rows =>
      TreeBudgetBitMachine.bind (alloc rows.2 [.bit true, .ref rows.1]) fun answer =>
        ret ⟨answer.1, cache, answer.2, {}⟩
    else failResult heap cache

def prependResult (heap : Heap) (row rows cache : ℕ) (events : Counts) : Costed (Option Result) :=
  TreeBudgetBitMachine.bind (alloc heap [.bit true, .ref row, .ref rows]) fun chain =>
    TreeBudgetBitMachine.bind (alloc chain.2 [.bit true, .ref chain.1]) fun answer =>
      ret ⟨answer.1, cache, answer.2, events⟩

def scanD (n : ℕ) (solve : Heap → ℕ → ℕ → ℕ → Costed (Option Result))
    (fuel : ℕ) (heap : Heap) (candidates residual cache parent : ℕ) : Costed (Option Result) :=
  thenD (cursorStep fuel) fun remainingFuel =>
    thenD (rowsHead heap candidates) fun node => match node with
    | none => failResult heap cache
    | some (row, tail) => addEvents { candidates := 1 } <|
      thenD (vectorRead n heap row) fun p => thenD (vectorRead n heap residual) fun r =>
        TreeBudgetBitMachine.bind (guardV p r) fun guarded =>
          if guarded then
            TreeBudgetBitMachine.bind (subV r p) fun remaining =>
              TreeBudgetBitMachine.bind (vectorWrite heap remaining) fun child =>
                TreeBudgetBitMachine.bind (alloc child.2 (frameSlots row tail residual parent)) fun frame =>
                  thenD (solve frame.2 child.1 cache frame.1) fun out =>
                    thenD (frameRead out.heap frame.1) fun saved =>
                      thenD (answerHead out.heap out.answer) fun answer => match answer with
                      | some rows => prependResult out.heap saved.1 rows out.cache out.events
                      | none => addEvents out.events
                          (scanD n solve remainingFuel.val out.heap saved.2.1 saved.2.2.1 out.cache saved.2.2.2)
          else scanD n solve remainingFuel.val heap tail residual cache parent
termination_by fuel
decreasing_by all_goals exact remainingFuel.isLt

theorem scanD_succ_value (n : ℕ) (solve : Heap → ℕ → ℕ → ℕ → Costed (Option Result))
    (fuel : ℕ) (heap : Heap) (candidates residual cache parent : ℕ) :
    (scanD n solve (fuel + 1) heap candidates residual cache parent).value =
      (thenD (rowsHead heap candidates) fun node => match node with
    | none => failResult heap cache
    | some (row, tail) => addEvents { candidates := 1 } <|
      thenD (vectorRead n heap row) fun p => thenD (vectorRead n heap residual) fun r =>
        TreeBudgetBitMachine.bind (guardV p r) fun guarded =>
          if guarded then
            TreeBudgetBitMachine.bind (subV r p) fun remaining =>
              TreeBudgetBitMachine.bind (vectorWrite heap remaining) fun child =>
                TreeBudgetBitMachine.bind (alloc child.2 (frameSlots row tail residual parent)) fun frame =>
                  thenD (solve frame.2 child.1 cache frame.1) fun out =>
                    thenD (frameRead out.heap frame.1) fun saved =>
                      thenD (answerHead out.heap out.answer) fun answer => match answer with
                      | some rows => prependResult out.heap saved.1 rows out.cache out.events
                      | none => addEvents out.events
                          (scanD n solve fuel out.heap saved.2.1 saved.2.2.1 out.cache saved.2.2.2)
          else scanD n solve fuel heap tail residual cache parent).value := by
  rw [scanD]
  simp only [thenD_value, cursorStep_succ, Option.bind_some]


def saveResult (out : Result) (frame : ℕ) (events : Counts) : Costed (Option Result) :=
  thenD (loadRef out.heap frame 1) fun savedKey =>
    thenD (insertD out.heap out.cache savedKey out.answer) fun saved =>
      ret ⟨out.answer, saved.1.1, saved.1.2, events.add
        (out.events.add { insertionScans := saved.2 })⟩

def memoLayer (n k : ℕ) (heap : Heap) (residual cache parent : ℕ)
    (expand : Heap → ℕ → Costed (Option Result)) : Costed (Option Result) :=
  thenD (vectorRead n heap residual) fun r =>
    TreeBudgetBitMachine.bind (keyWrite heap k r) fun key =>
      thenD (blobRead key.2 key.1) fun query =>
        TreeBudgetBitMachine.bind (addNatD key.2.size 1) fun fuel =>
        thenD (lookupD fuel key.2 cache query) fun found =>
          match found.1 with
          | some answer => ret ⟨answer, cache, key.2,
              { calls := 1, hits := 1, lookupComparisons := found.2 }⟩
          | none =>
            TreeBudgetBitMachine.bind (alloc key.2 [.bit true, .ref key.1, .ref parent]) fun frame =>
              thenD (expand frame.2 frame.1) fun out => saveResult out frame.1
                { calls := 1, expansions := 1, lookupComparisons := found.2 }

/-- The depth test and predecessor are actual digit primitives. Recursion fuel
for candidate/cache chains uses charged binary initialization and predecessor. -/
def memoD (n : ℕ) (candidates : ℕ) (k : ℕ) (heap : Heap)
    (residual cache parent : ℕ) : Costed (Option Result) :=
  memoLayer n k heap residual cache parent fun framed frame =>
    let test := zeroNatD k
    charge test.steps test.allocations <|
      if hbase : test.value then zeroResult n framed residual cache else
        let depth := subNatD k 1
        charge depth.steps depth.allocations <|
          TreeBudgetBitMachine.bind (addNatD framed.size 1) fun fuel =>
          scanD n (memoD n candidates depth.value) fuel
            framed candidates residual cache frame
termination_by k
decreasing_by
  simp_wf
  have hk : k ≠ 0 := by simpa only [test, zeroNatD_value, decide_eq_true_eq] using hbase
  omega

theorem rowsHead_nil (heap : Heap) (a : ℕ) (hh : WellFormed heap)
    (hr : Represents heap ⟨a, 1⟩ [.bit false]) :
    (rowsHead heap a).value = some none := by
  have h₀ : read heap a = some (.bit false) := by simpa using hr.2.2 0 (by simp)
  simp [rowsHead, hh, h₀, ret]

theorem rowsHead_cons (heap : Heap) (a row tail : ℕ) (hh : WellFormed heap)
    (hr : Represents heap ⟨a, 3⟩ [.bit true, .ref row, .ref tail]) :
    (rowsHead heap a).value = some (some (row, tail)) := by
  have h₀ : read heap a = some (.bit true) := by simpa using hr.2.2 0 (by simp)
  have h₁ : read heap (a + 1) = some (.ref row) := hr.2.2 1 (by simp)
  have h₂ : read heap (a + 2) = some (.ref tail) := hr.2.2 2 (by simp)
  simp [rowsHead, hh, h₀, loadRef_value _ _ _ _ hh h₁, loadRef_value _ _ _ _ hh h₂, ret]

theorem answerHead_failure (heap : Heap) (a : ℕ) (hh : WellFormed heap)
    (hr : SharedAnswerRep heap a none) : (answerHead heap a).value = some none := by
  cases hr with
  | failure header =>
    have h₀ : read heap a = some (.bit false) := by simpa using header.2.2 0 (by simp)
    simp [answerHead, hh, h₀, ret]

theorem answerHead_success (heap : Heap) (a : ℕ) (rows : Matrix) (hh : WellFormed heap)
    (hr : SharedAnswerRep heap a (some rows)) :
    ∃ r, (answerHead heap a).value = some (some r) ∧ RowsRep heap r rows := by
  cases hr with
  | success r rows header hrows hl =>
    have h₀ : read heap a = some (.bit true) := by simpa using header.2.2 0 (by simp)
    have h₁ : read heap (a + 1) = some (.ref r) := header.2.2 1 (by simp)
    exact ⟨r, by simp [answerHead, hh, h₀, loadRef_value _ _ _ _ hh h₁, ret], hrows⟩

def ResultRep (before : Heap) (out : Costed (Option Result))
    (answer : WireAnswer) (cache : WireCache) (events : Counts) : Prop :=
  ∃ result, out.value = some result ∧ SharedAnswerRep result.heap result.answer answer ∧
    TreeBudgetChargedCache.CacheRep result.heap result.cache cache ∧
    WellFormed result.heap ∧ Extends before result.heap ∧ result.events = events

theorem failResult_correct (heap : Heap) (cache : ℕ) (cs : WireCache)
    (hh : WellFormed heap) (hc : TreeBudgetChargedCache.CacheRep heap cache cs) :
    ResultRep heap (failResult heap cache) none cs {} := by
  have ha := alloc_value heap [.bit false] (by simp)
  refine ⟨⟨heap.size, cache, allocateBlock heap [.bit false], {}⟩, ?_,
    failure_correct heap, TreeBudgetChargedCache.cacheRep_persist (allocateBlock_extends ..) hc,
    failure_wellFormed heap hh, allocateBlock_extends .., rfl⟩
  simp [failResult, TreeBudgetBitMachine.bind, ha, ret]

theorem prependResult_correct (heap : Heap) (row rows cache : ℕ)
    (p : List ℕ) (ps : Matrix) (cs : WireCache) (events : Counts)
    (hh : WellFormed heap) (hp : RowRep heap row p) (hps : RowsRep heap rows ps)
    (hc : TreeBudgetChargedCache.CacheRep heap cache cs) :
    ResultRep heap (prependResult heap row rows cache events) (some (p :: ps)) cs events := by
  have hpBound := blobRep_address_lt _ _ _ hp
  have hpsBound := rowsRep_address_lt hps
  have hslots : ∀ r, Slot.ref r ∈ [.bit true, .ref row, .ref rows] → r < heap.size := by
    intro r hr; simp at hr; rcases hr with rfl | rfl <;> assumption
  have hchain := prependRows_correct heap row rows p ps hp hps
  have hchainBound := rowsRep_address_lt hchain
  have hchainWF := prependRows_wellFormed heap row rows hh hpBound hpsBound
  have he₁ := allocateBlock_extends heap [.bit true, .ref row, .ref rows]
  have he₂ := allocateBlock_extends (prependRows heap row rows).2 [.bit true, .ref heap.size]
  have he := extends_trans he₁ he₂
  have ha₁ := alloc_value heap [.bit true, .ref row, .ref rows] hslots
  have ha₂ := alloc_value (prependRows heap row rows).2 [.bit true, .ref heap.size]
    (by simpa [prependRows] using hchainBound)
  refine ⟨⟨(prependRows heap row rows).2.size, cache,
    (success (prependRows heap row rows).2 heap.size).2, events⟩, ?_,
    success_correct _ _ _ hchain, TreeBudgetChargedCache.cacheRep_persist he hc,
    success_wellFormed _ _ hchainWF hchainBound, he, rfl⟩
  simp only [prependResult, TreeBudgetBitMachine.bind, ha₁]
  change (ret (show Result from ⟨(alloc (prependRows heap row rows).2 [.bit true, .ref heap.size]).value.1,
    cache, (alloc (prependRows heap row rows).2 [.bit true, .ref heap.size]).value.2, events⟩)).value = _
  rw [ha₂]
  rfl

theorem zeroResult_correct {n : ℕ} (heap : Heap) (residual cache : ℕ)
    (r : Vector ℕ n) (cs : WireCache) (hh : WellFormed heap)
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache cs) :
    ResultRep heap (zeroResult n heap residual cache)
      (if TreeBudgetVector.isZero r then some [] else none) cs {} := by
  unfold ResultRep
  simp only [zeroResult, thenD_value, vectorRead_correct _ _ _ hh hr,
    costBind_value, zeroV_value, Option.bind_some]
  by_cases hz : TreeBudgetVector.isZero r = true
  · have ha₁ := alloc_value heap [.bit false] (by simp)
    have he₁ := allocateBlock_extends heap [.bit false]
    have hrows := emptyRows_correct heap
    have hb := rowsRep_address_lt hrows
    have ha₂ := alloc_value (emptyRows heap).2 [.bit true, .ref heap.size] (by simpa using hb)
    have he₂ := allocateBlock_extends (emptyRows heap).2 [.bit true, .ref heap.size]
    have he := extends_trans he₁ he₂
    have hwf : WellFormed (emptyRows heap).2 := failure_wellFormed heap hh
    refine ⟨⟨(emptyRows heap).2.size, cache, (success (emptyRows heap).2 heap.size).2, {}⟩,
      ?_, ?_, TreeBudgetChargedCache.cacheRep_persist he hc,
      success_wellFormed _ _ hwf hb, he, rfl⟩
    · simp only [hz, ↓reduceIte, costBind_value, ha₁]
      change (ret (show Result from ⟨(alloc (emptyRows heap).2 [.bit true, .ref heap.size]).value.1, cache,
        (alloc (emptyRows heap).2 [.bit true, .ref heap.size]).value.2, {}⟩)).value = _
      rw [ha₂]; rfl
    · simpa [hz] using success_correct (emptyRows heap).2 heap.size [] hrows
  · simpa [ResultRep, hz, Option.bind_some] using failResult_correct heap cache cs hh hc

theorem addEvents_correct (heap : Heap) (out : Costed (Option Result))
    (ans : WireAnswer) (cs : WireCache) (events extra : Counts)
    (h : ResultRep heap out ans cs events) :
    ResultRep heap (addEvents extra out) ans cs (extra.add events) := by
  obtain ⟨result, hv, ha, hc, hh, he, hev⟩ := h
  exact ⟨{ result with events := extra.add result.events },
    by simp [addEvents, hv], ha, hc, hh, he, by simp [hev]⟩

theorem resultRep_extends {before middle : Heap} (he : Extends before middle)
    {out : Costed (Option Result)} {ans : WireAnswer} {cs : WireCache} {events : Counts}
    (h : ResultRep middle out ans cs events) : ResultRep before out ans cs events := by
  obtain ⟨r, hv, ha, hc, hh, he', hev⟩ := h
  exact ⟨r, hv, ha, hc, hh, extends_trans he he', hev⟩

open TreeBudgetVectorSearchStats in
theorem scanD_correct {n : ℕ} (origin : Heap)
    (solve : Heap → ℕ → ℕ → ℕ → Costed (Option Result))
    (spec : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (hsolve : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → ResultRep heap (solve heap residual cache parent)
        (wireAnswer (spec r cs).1.1) (wireCache (spec r cs).1.2) (spec r cs).2)
    (ps : List (Vector ℕ n)) (heap : Heap) (candidates residual cache parent : ℕ)
    (r : Vector ℕ n) (cs : CacheV n) (fuel : ℕ)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hf : candidates < fuel) (hbase : Extends origin heap) :
    ResultRep heap (scanD n solve fuel heap candidates residual cache parent)
      (wireAnswer (scanStatV spec r ps cs).1.1) (wireCache (scanStatV spec r ps cs).1.2)
      (scanStatV spec r ps cs).2 := by
  induction ps generalizing heap candidates residual cache parent cs fuel with
  | nil =>
    cases hp with
    | nil a header =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        simpa [ResultRep, addEvents, scanD_succ_value, rowsHead_nil _ _ hh header, thenD_value, scanStatV, wireAnswer]
          using failResult_correct heap cache (wireCache cs) hh hc
  | cons p ps ih =>
    cases hp with
    | cons a row tail _ _ header hrow htail hrl htl =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hread := rowsHead_cons heap candidates row tail hh header
        have hpread := vectorRead_correct heap row p hh hrow
        have hrread := vectorRead_correct heap residual r hh hr
        by_cases hg : TreeBudgetVector.leB p r = true
        · let child := allocateBlob heap (encodeNats (TreeBudgetVector.sub r p).toList)
          have hchild := allocateBlob_correct heap (encodeNats (TreeBudgetVector.sub r p).toList)
          have hech : Extends heap child.2 := allocateBlock_extends ..
          have hwch : WellFormed child.2 := allocateBlob_wellFormed heap _ hh
          have hchSize := hech.size_le
          have hbrow := blobRep_address_lt _ _ _ hrow
          have hbtail := rowsRep_address_lt htail
          have hbres := blobRep_address_lt _ _ _ hr
          have href : ∀ x, Slot.ref x ∈ frameSlots row tail residual parent → x < child.2.size := by
            intro x hx
            simp [frameSlots] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> omega
          let framed := allocateBlock child.2 (frameSlots row tail residual parent)
          have hefr : Extends child.2 framed := allocateBlock_extends ..
          have hehf := extends_trans hech hefr
          have hwfr : WellFormed framed := wellFormed_allocateBlock _ _ hwch href
          have hframe : FrameRep framed child.2.size row tail residual parent :=
            allocateTyped_represents child.2 (frameSlots row tail residual parent)
          have hbframe : child.2.size < framed.size := by
            simp [framed, allocateBlock_size, frameSlots]
          have hsub := hsolve framed child.1 cache child.2.size (TreeBudgetVector.sub r p) cs hwfr
            (blobRep_persist hefr _ _ hchild)
            (TreeBudgetChargedCache.cacheRep_persist hehf hc) hbframe (extends_trans hbase hehf)
          obtain ⟨out, hout, hans, hcache, hwout, heout, hevents⟩ := hsub
          have he := extends_trans hehf heout
          have hframeRead := frameRead_correct out.heap child.2.size row tail residual parent hwout
            (represents_of_extends heout _ _ hframe)
          have halloc := alloc_value child.2 (frameSlots row tail residual parent) href
          cases hspec : spec (TreeBudgetVector.sub r p) cs with
          | mk pair events =>
            rcases pair with ⟨ans, cs'⟩
            simp only [hspec] at hans hcache hevents
            cases ans with
            | none =>
              have hanswerRead := answerHead_failure _ _ hwout hans
              have htailRun := ih out.heap tail residual out.cache parent cs' fuel hwout
                (rowsRep_persist he _ _ htail) (blobRep_persist he _ _ hr) hcache
                (hparent.trans_le he.size_le) (by omega) (extends_trans hbase he)
              have hres := addEvents_correct heap _ _ _ _ { candidates := 1 }
                (addEvents_correct heap _ _ _ _ events (resultRep_extends he htailRun))
              simpa [ResultRep, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
                hg, subV_value, vectorWrite_value, child, halloc, framed, hout,
                hframeRead, hanswerRead, hevents, scanStatV, hspec, bump, wireAnswer]
                using hres
            | some rows =>
              obtain ⟨rowsRef, hanswerRead, hrows⟩ := answerHead_success _ _ _ hwout hans
              have hprepend := prependResult_correct out.heap row rowsRef out.cache p.toList
                (rows.map Vector.toList) (wireCache cs') events hwout
                (blobRep_persist he _ _ hrow) hrows hcache
              have hres := addEvents_correct heap _ _ _ _ { candidates := 1 }
                (resultRep_extends he hprepend)
              simpa [ResultRep, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
                hg, subV_value, vectorWrite_value, child, halloc, framed, hout,
                hframeRead, hanswerRead, hevents, scanStatV, hspec, bump, wireAnswer]
                using hres
        · have htailRun := ih heap tail residual cache parent cs fuel hh htail hr hc hparent (by omega) hbase
          have hres := addEvents_correct heap _ _ _ _ { candidates := 1 } htailRun
          simpa [ResultRep, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
            hg, scanStatV, bump] using hres

theorem lookupCount_vector {n : ℕ} (cs : CacheV n) (q : KeyV n) :
    lookupCount (wireCache cs) (wireKey q) = (TreeBudgetVectorSearchStats.lookupStatV cs q).2 := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [wireCache, List.map_cons, lookupCount, TreeBudgetVectorSearchStats.lookupStatV, keyEqB_wire]
    by_cases h : wireKey e.1 = wireKey q
    · simp [h]
    · simpa [h, wireCache] using ih

theorem saveResult_correct {n : ℕ} (out : Result) (frame key : ℕ) (q : KeyV n)
    (ans : AnswerV n) (cs : CacheV n) (events : Counts)
    (hh : WellFormed out.heap) (hf : read out.heap (frame + 1) = some (.ref key))
    (hk : KeyRep out.heap key (wireKey q)) (ha : SharedAnswerRep out.heap out.answer (wireAnswer ans))
    (hc : TreeBudgetChargedCache.CacheRep out.heap out.cache (wireCache cs)) :
    ResultRep out.heap (saveResult out frame events) (wireAnswer ans)
      (wireCache (insertV cs q ans))
      (events.add (out.events.add { insertionScans := cs.length })) := by
  obtain ⟨root, after, hout, hrep, hwf, he, hsize⟩ := insertD_correct out.heap out.cache key out.answer
    (wireCache cs) (wireKey q) (wireAnswer ans) hh hc hk ha
  refine ⟨⟨out.answer, root, after, events.add (out.events.add { insertionScans := cs.length })⟩,
    ?_, answerRep_persist he _ _ ha, ?_, hwf, he, rfl⟩
  · simp [saveResult, loadRef_value _ _ _ _ hh hf, hout, wireCache, ret]
  · rw [keep_vector] at hrep
    simpa [insertV, wireCache] using hrep

set_option maxHeartbeats 2000000 in
open TreeBudgetVectorSearchStats in
theorem memoD_correct {n : ℕ} (ps : List (Vector ℕ n)) (candidates k : ℕ)
    (heap : Heap) (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) :
    ResultRep heap (memoD n candidates k heap residual cache parent)
      (wireAnswer (memoStatV ps k r cs).1.1) (wireCache (memoStatV ps k r cs).1.2)
      (memoStatV ps k r cs).2 := by
  induction k generalizing heap residual cache parent r cs with
  | zero =>
    rw [memoD, memoLayer]
    let key := allocateBlob heap (encodeKey (0, r.toList))
    have hk := allocateBlob_correct heap (encodeKey (0, r.toList))
    have he : Extends heap key.2 := allocateBlock_extends ..
    have hw : WellFormed key.2 := allocateBlob_wellFormed heap _ hh
    have hc' := TreeBudgetChargedCache.cacheRep_persist he hc
    have hwrite : (keyWrite heap 0 r).value = key := keyWrite_value heap 0 r
    have hreadKey : (blobRead key.2 key.1).value = some (encodeKey (wireKey (0, r))) :=
      blobRead_correct key.2 key.1 _ hw hk
    obtain ⟨found, hfound, hfoundRep⟩ := lookupD_correct key.2 cache (wireCache cs) hw hc'
      (wireKey (0, r)) (key.2.size + 1) (by have := TreeBudgetChargedCache.cacheRep_address_lt hc'; omega)
    rw [lookupWire_vector, ← lookupStatV_erase] at hfoundRep
    rw [lookupCount_vector] at hfound
    cases hlookup : (lookupStatV cs (0, r)).1 with
    | some ans =>
      simp only [memoStatV, hlookup]
      cases found with
      | none => simp only [hlookup, Option.map_some, FoundRep] at hfoundRep
      | some answer =>
        refine ⟨⟨answer, cache, key.2, { calls := 1, hits := 1, lookupComparisons := (lookupStatV cs (0, r)).2 }⟩, ?_, ?_, hc', hw, he, ?_⟩
        · simp only [thenD_value, Option.bind_some, vectorRead_correct _ _ _ hh hr, costBind_value,
            addNatD_value, hwrite, hreadKey, hfound, ret]
        · simpa only [hlookup, Option.map_some, FoundRep] using hfoundRep
        · rfl
    | none =>
      have hlookupV := hlookup
      rw [lookupStatV_erase] at hlookupV
      have hnone : found = none := by cases found <;> simp_all only [Option.map_none, FoundRep]
      subst found
      have hbkey := blobRep_address_lt _ _ _ hk
      have href : ∀ x, Slot.ref x ∈ [.bit true, .ref key.1, .ref parent] → x < key.2.size := by
        intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact hbkey
        · exact hparent.trans_le he.size_le
      let framed := allocateBlock key.2 [.bit true, .ref key.1, .ref parent]
      have hefr : Extends key.2 framed := allocateBlock_extends ..
      have heall := extends_trans he hefr
      have hwfr : WellFormed framed := wellFormed_allocateBlock _ _ hw href
      obtain ⟨out, hout, ha, hcache, hwout, heout, hev⟩ := zeroResult_correct framed residual cache r
        (wireCache cs) hwfr (blobRep_persist heall _ _ hr)
        (TreeBudgetChargedCache.cacheRep_persist heall hc)
      have hframe : read out.heap (key.2.size + 1) = some (.ref key.1) := by
        rw [heout.read_old _ (by simp [framed, allocateBlock_size])]
        exact read_allocateBlock_new key.2 _ 1 (by simp)
      have hkey := blobRep_persist (extends_trans hefr heout) _ _ hk
      have hs := saveResult_correct out key.2.size key.1 (0, r)
        (if TreeBudgetVector.isZero r then some [] else none) cs
        { calls := 1, expansions := 1, lookupComparisons := (lookupStatV cs (0, r)).2 }
        hwout hframe hkey (by simpa [wireAnswer] using ha) hcache
      have hres := resultRep_extends (extends_trans heall heout) hs
      simpa [ResultRep, vectorRead_correct _ _ _ hh hr, costBind_value,
        hwrite, hreadKey, hfound, alloc_value _ _ href,
        framed, thenD_value, charge, zeroNatD_value, subNatD_value, hout, memoStatV, hlookup, hlookupV, insertStatV, hev,
        TreeBudgetCostedSearch.counts_add_assoc, Counts.add] using hres
  | succ k ih =>
    rw [memoD, memoLayer]
    let key := allocateBlob heap (encodeKey (k + 1, r.toList))
    have hk := allocateBlob_correct heap (encodeKey (k + 1, r.toList))
    have he : Extends heap key.2 := allocateBlock_extends ..
    have hw : WellFormed key.2 := allocateBlob_wellFormed heap _ hh
    have hc' := TreeBudgetChargedCache.cacheRep_persist he hc
    have hwrite : (keyWrite heap (k + 1) r).value = key := keyWrite_value heap (k + 1) r
    have hreadKey : (blobRead key.2 key.1).value = some (encodeKey (wireKey (k + 1, r))) :=
      blobRead_correct key.2 key.1 _ hw hk
    obtain ⟨found, hfound, hfoundRep⟩ := lookupD_correct key.2 cache (wireCache cs) hw hc'
      (wireKey (k + 1, r)) (key.2.size + 1) (by have := TreeBudgetChargedCache.cacheRep_address_lt hc'; omega)
    rw [lookupWire_vector, ← lookupStatV_erase] at hfoundRep
    rw [lookupCount_vector] at hfound
    cases hlookup : (lookupStatV cs (k + 1, r)).1 with
    | some ans =>
      simp only [memoStatV, hlookup]
      cases found with
      | none => simp only [hlookup, Option.map_some, FoundRep] at hfoundRep
      | some answer =>
        refine ⟨⟨answer, cache, key.2, { calls := 1, hits := 1, lookupComparisons := (lookupStatV cs (k + 1, r)).2 }⟩, ?_, ?_, hc', hw, he, ?_⟩
        · simp only [thenD_value, Option.bind_some, vectorRead_correct _ _ _ hh hr, costBind_value,
            addNatD_value, hwrite, hreadKey, hfound, ret]
        · simpa only [hlookup, Option.map_some, FoundRep] using hfoundRep
        · rfl
    | none =>
      have hlookupV := hlookup
      rw [lookupStatV_erase] at hlookupV
      have hnone : found = none := by cases found <;> simp_all only [Option.map_none, FoundRep]
      subst found
      have hbkey := blobRep_address_lt _ _ _ hk
      have href : ∀ x, Slot.ref x ∈ [.bit true, .ref key.1, .ref parent] → x < key.2.size := by
        intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact hbkey
        · exact hparent.trans_le he.size_le
      let framed := allocateBlock key.2 [.bit true, .ref key.1, .ref parent]
      have hefr : Extends key.2 framed := allocateBlock_extends ..
      have heall := extends_trans he hefr
      have hwfr : WellFormed framed := wellFormed_allocateBlock _ _ hw href
      have hpc := rowsRep_persist heall _ _ hp
      have hsolver : ∀ h rr cc pp rv csv, WellFormed h → RowRep h rr rv.toList →
          TreeBudgetChargedCache.CacheRep h cc (wireCache csv) → pp < h.size →
          Extends framed h → ResultRep h (memoD n candidates k h rr cc pp)
            (wireAnswer (memoStatV ps k rv csv).1.1) (wireCache (memoStatV ps k rv csv).1.2)
            (memoStatV ps k rv csv).2 := by
        intro h rr cc pp rv csv hhw hrr hcc hpp hext
        exact ih h rr cc pp rv csv hhw (rowsRep_persist hext _ _ hpc) hrr hcc hpp
      obtain ⟨out, hout, ha, hcache, hwout, heout, hev⟩ := scanD_correct framed _ _ hsolver
        ps framed candidates residual cache key.2.size r cs (framed.size + 1) hwfr hpc
        (blobRep_persist heall _ _ hr) (TreeBudgetChargedCache.cacheRep_persist heall hc)
        (by simp [framed, allocateBlock_size]) (by have := rowsRep_address_lt hpc; omega) (extends_refl framed)
      have hframe : read out.heap (key.2.size + 1) = some (.ref key.1) := by
        rw [heout.read_old _ (by simp [framed, allocateBlock_size])]
        exact read_allocateBlock_new key.2 _ 1 (by simp)
      have hkey := blobRep_persist (extends_trans hefr heout) _ _ hk
      have hs := saveResult_correct out key.2.size key.1 (k + 1, r)
        (scanStatV (memoStatV ps k) r ps cs).1.1 (scanStatV (memoStatV ps k) r ps cs).1.2
        { calls := 1, expansions := 1, lookupComparisons := (lookupStatV cs (k + 1, r)).2 }
        hwout hframe hkey ha hcache
      have hres := resultRep_extends (extends_trans heall heout) hs
      simpa [ResultRep, vectorRead_correct _ _ _ hh hr, costBind_value,
        hwrite, hreadKey, hfound, alloc_value _ _ href,
        framed, thenD_value, charge, zeroNatD_value, subNatD_value, hout, memoStatV, hlookup, hlookupV, insertStatV, hev,
        TreeBudgetCostedSearch.counts_add_assoc, Counts.add] using hres

theorem memoD_refines_cost {n : ℕ} (B : TreeBudgetCostedSearch.Backend n)
    (ps : List (Vector ℕ n)) (candidates k : ℕ) (heap : Heap)
    (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) :
    ResultRep heap (memoD n candidates k heap residual cache parent)
      (wireAnswer (TreeBudgetCostedSearch.memoCost B ps k r cs).value.1)
      (wireCache (TreeBudgetCostedSearch.memoCost B ps k r cs).value.2)
      (TreeBudgetCostedSearch.memoCost B ps k r cs).events := by
  have h := TreeBudgetCostedSearch.memoCost_observe B ps k r cs
  have hv := congrArg Prod.fst h
  have he := congrArg Prod.snd h
  simp only [TreeBudgetCostedSearch.observe] at hv he
  rw [hv, he]
  exact memoD_correct ps candidates k heap residual cache parent r cs hh hp hr hc hparent

/-- Joint postcondition also preserves the caller's continuation stack and
the fixed candidate list; duplicate or conflicting cache entries are allowed. -/
theorem memoD_preserves {n : ℕ} (ps : List (Vector ℕ n)) (candidates k : ℕ)
    (heap : Heap) (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hf : FramesRep heap parent) :
    ∃ out, (memoD n candidates k heap residual cache parent).value = some out ∧
      SharedAnswerRep out.heap out.answer (wireAnswer (TreeBudgetVectorSearchStats.memoStatV ps k r cs).1.1) ∧
      TreeBudgetChargedCache.CacheRep out.heap out.cache (wireCache (TreeBudgetVectorSearchStats.memoStatV ps k r cs).1.2) ∧
      out.events = (TreeBudgetVectorSearchStats.memoStatV ps k r cs).2 ∧
      WellFormed out.heap ∧ Extends heap out.heap ∧ FramesRep out.heap parent ∧
      RowsRep out.heap candidates (ps.map Vector.toList) ∧ RowRep out.heap residual r.toList := by
  obtain ⟨out, hv, ha, hc', hw, he, hev⟩ := memoD_correct ps candidates k heap residual cache parent r cs hh hp hr hc hparent
  exact ⟨out, hv, ha, hc', hev, hw, he, framesRep_persist he hf,
    rowsRep_persist he _ _ hp, blobRep_persist he _ _ hr⟩

end UAVProof.TreeBudgetStoredSearch
