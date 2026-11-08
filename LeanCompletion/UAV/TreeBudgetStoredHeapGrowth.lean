import LeanCompletion.UAV.TreeBudgetStoredAllocation
import LeanCompletion.UAV.TreeBudgetCostedSearchBounds

namespace UAVProof.TreeBudgetStoredHeapGrowth
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedParsing
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetSearchStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetStoredAllocation TreeBudgetVectorMemoState TreeBudgetSearchStats
open TreeBudgetBinaryCodec TreeBudgetCostedSearchBounds TreeBudgetVectorSearchStats

def Growth (heap : Heap) (out : Costed (Option Result)) (budget : ℕ) : Prop :=
  ∀ result, out.value = some result → result.heap.size ≤ heap.size + budget

theorem growth_mono {heap : Heap} {out : Costed (Option Result)} {a b : ℕ}
    (h : Growth heap out a) (hab : a ≤ b) : Growth heap out b := by
  intro result hv
  exact (h result hv).trans (Nat.add_le_add_left hab _)

theorem growth_start {before middle : Heap} {out : Costed (Option Result)} {a b : ℕ}
    (hm : middle.size ≤ before.size + a) (h : Growth middle out b) :
    Growth before out (a + b) := by
  intro result hv
  have := h result hv
  omega

theorem growth_addEvents (heap : Heap) (out : Costed (Option Result)) (events : Counts)
    (budget : ℕ) (h : Growth heap out budget) : Growth heap (addEvents events out) budget := by
  intro result hv
  obtain ⟨old, ho, he⟩ := Option.map_eq_some_iff.mp hv
  subst result
  exact h old ho

theorem failResult_growth (heap : Heap) (cache : ℕ) : Growth heap (failResult heap cache) 1 := by
  intro result hv
  simp only [failResult, costBind_value, alloc_value heap [.bit false] (by simp), ret,
    Option.some.injEq] at hv
  subst result
  simp [allocateBlock_size]

theorem zeroResult_growth {n : ℕ} (heap : Heap) (residual cache : ℕ)
    (r : Vector ℕ n) (hh : WellFormed heap) (hr : RowRep heap residual r.toList) :
    Growth heap (zeroResult n heap residual cache) 3 := by
  intro result hv
  simp only [zeroResult, thenD_value, vectorRead_correct _ _ _ hh hr,
    Option.bind_some, costBind_value, zeroV_value] at hv
  by_cases hz : TreeBudgetVector.isZero r = true
  · have h₁ := alloc_value heap [.bit false] (by simp)
    have h₂ := alloc_value (allocateBlock heap [.bit false]) [.bit true, .ref heap.size]
      (by simp [allocateBlock_size])
    simp only [hz, ↓reduceIte, costBind_value, h₁, h₂, ret, Option.some.injEq] at hv
    subst result
    simp [allocateBlock_size]
  · simp only [hz, ↓reduceIte] at hv
    have h := failResult_growth heap cache result hv
    omega

theorem prependResult_growth (heap : Heap) (row rows cache : ℕ) (events : Counts)
    (hr : row < heap.size) (ht : rows < heap.size) :
    Growth heap (prependResult heap row rows cache events) 5 := by
  have h₁ := alloc_value heap [.bit true, .ref row, .ref rows] (by
    intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)
  have h₂ := alloc_value (allocateBlock heap [.bit true, .ref row, .ref rows])
    [.bit true, .ref heap.size] (by simp [allocateBlock_size])
  intro result hv
  simp only [prependResult, costBind_value, h₁, h₂, ret, Option.some.injEq] at hv
  subst result
  simp [allocateBlock_size]

theorem saveResult_growth {n : ℕ} (out : Result) (frame key : ℕ) (q : KeyV n)
    (ans : AnswerV n) (cs : CacheV n) (events : Counts)
    (hh : WellFormed out.heap) (hf : read out.heap (frame + 1) = some (.ref key))
    (hk : KeyRep out.heap key (wireKey q)) (ha : SharedAnswerRep out.heap out.answer (wireAnswer ans))
    (hc : TreeBudgetChargedCache.CacheRep out.heap out.cache (wireCache cs)) :
    Growth out.heap (saveResult out frame events) (4 * cs.length + 4) := by
  obtain ⟨root, after, hv, hs⟩ := insert_heap_growth out.heap out.cache key out.answer
    (wireCache cs) (wireKey q) (wireAnswer ans) hh hc hk ha
  intro result hr
  simp only [saveResult, thenD_value, loadRef_value _ _ _ _ hh hf,
    Option.bind_some, hv, ret, Option.some.injEq] at hr
  subst result
  simpa [wireCache] using hs

set_option maxHeartbeats 2000000 in
-- The scan cases combine representation persistence with allocation arithmetic.
theorem scanD_growth {n : ℕ} (origin : Heap)
    (solve : Heap → ℕ → ℕ → ℕ → Costed (Option Result))
    (spec : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (hsolve : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → ResultRep heap (solve heap residual cache parent)
        (wireAnswer (spec r cs).1.1) (wireCache (spec r cs).1.2) (spec r cs).2)
    (H : Vector ℕ n) (B : ℕ)
    (hrows : ∀ v, VecSmall H v → rowSlots v ≤ B)
    (hbudget : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → VecSmall H r →
      Growth heap (solve heap residual cache parent) ((B + 20) * eventWeight (spec r cs).2))
    (ps : List (Vector ℕ n)) (heap : Heap) (candidates residual cache parent : ℕ)
    (r : Vector ℕ n) (cs : CacheV n) (fuel : ℕ)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hf : candidates < fuel) (hbase : Extends origin heap)
    (hsmall : VecSmall H r) :
    Growth heap (scanD n solve fuel heap candidates residual cache parent)
      ((B + 20) * (1 + eventWeight (scanStatV spec r ps cs).2)) := by
  induction ps generalizing heap candidates residual cache parent cs fuel with
  | nil =>
    cases hp with
    | nil a header =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hg := growth_mono (failResult_growth heap cache) (show 1 ≤ B + 20 by omega)
        simpa [Growth, scanD_succ_value, rowsHead_nil _ _ hh header, scanStatV, eventWeight]
          using hg
  | cons p ps ih =>
    cases hp with
    | cons a row tail _ _ header hrow htail hrl htl =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hread := rowsHead_cons heap candidates row tail hh header
        have hpread := vectorRead_correct heap row p hh hrow
        have hrread := vectorRead_correct heap residual r hh hr
        by_cases hguard : TreeBudgetVector.leB p r = true
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
          have hsmall' := vecSmall_sub H r p hsmall
          have hgrowth := hbudget framed child.1 cache child.2.size (TreeBudgetVector.sub r p) cs hwfr
            (blobRep_persist hefr _ _ hchild)
            (TreeBudgetChargedCache.cacheRep_persist hehf hc) hbframe (extends_trans hbase hehf) hsmall'
          obtain ⟨out, hout, hans, hcache, hwout, heout, hevents⟩ := hsub
          have hchildSize := hgrowth out hout
          have hslots := hrows (TreeBudgetVector.sub r p) hsmall'
          have hfrSize : framed.size ≤ heap.size + B + 5 := by
            simp only [framed, child, allocateBlob, allocateBlock_size, blobSlots_length,
              frameSlots, List.length_cons, List.length_nil]
            dsimp [rowSlots] at hslots
            omega
          have he := extends_trans hehf heout
          have hframeRead := frameRead_correct out.heap child.2.size row tail residual parent hwout
            (represents_of_extends heout _ _ hframe)
          have halloc := alloc_value child.2 (frameSlots row tail residual parent) href
          cases hspec : spec (TreeBudgetVector.sub r p) cs with
          | mk pair events =>
            rcases pair with ⟨ans, cs'⟩
            simp only [hspec] at hans hcache hevents hchildSize
            cases ans with
            | none =>
              have hanswerRead := answerHead_failure _ _ hwout hans
              have htailRun := ih out.heap tail residual out.cache parent cs' fuel hwout
                (rowsRep_persist he _ _ htail) (blobRep_persist he _ _ hr) hcache
                (hparent.trans_le he.size_le) (by omega) (extends_trans hbase he)
              have hstart : out.heap.size ≤ heap.size + (B + 5 + (B + 20) * eventWeight events) := by
                omega
              have hg := growth_start hstart htailRun
              have hg' := growth_addEvents heap _ events _ hg
              have hres := growth_addEvents heap _ { candidates := 1 } _ hg'
              have hres' := growth_mono hres (show
                B + 5 + (B + 20) * eventWeight events +
                  (B + 20) * (1 + eventWeight (scanStatV spec r ps cs').2) ≤
                (B + 20) * (1 + eventWeight
                  ({ candidates := 1 : Counts }.add (events.add (scanStatV spec r ps cs').2))) by
                    simp only [eventWeight, Counts.add]
                    nlinarith only [])
              simpa [Growth, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
                hguard, subV_value, vectorWrite_value, child, halloc, framed, hout,
                hframeRead, hanswerRead, hevents, scanStatV, hspec, bump, wireAnswer]
                using hres'
            | some rows =>
              obtain ⟨rowsRef, hanswerRead, hrows⟩ := answerHead_success _ _ _ hwout hans
              have hprepend := prependResult_growth out.heap row rowsRef out.cache events
                ((blobRep_address_lt _ _ _ hrow).trans_le he.size_le) (rowsRep_address_lt hrows)
              have hstart : out.heap.size ≤ heap.size + (B + 5 + (B + 20) * eventWeight events) := by
                omega
              have hg := growth_start hstart hprepend
              have hres := growth_addEvents heap _ { candidates := 1 } _ hg
              have hres' := growth_mono hres (show
                B + 5 + (B + 20) * eventWeight events + 5 ≤
                  (B + 20) * (1 + eventWeight ({ candidates := 1 : Counts }.add events)) by
                    simp only [eventWeight, Counts.add]
                    nlinarith only [])
              simpa [Growth, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
                hguard, subV_value, vectorWrite_value, child, halloc, framed, hout,
                hframeRead, hanswerRead, hevents, scanStatV, hspec, bump, wireAnswer]
                using hres'
        · have htailRun := ih heap tail residual cache parent cs fuel hh htail hr hc hparent (by omega) hbase
          have hg' := growth_addEvents heap _ { candidates := 1 } _ htailRun
          have hres := growth_mono hg' (show
            (B + 20) * (1 + eventWeight (scanStatV spec r ps cs).2) ≤
              (B + 20) * (1 + eventWeight
                ({ candidates := 1 : Counts }.add (scanStatV spec r ps cs).2)) by
                  simp only [eventWeight, Counts.add]
                  nlinarith only [])
          simpa [Growth, addEvents, scanD_succ_value, hread, thenD_value, hpread, hrread, costBind_value, guardV_value,
            hguard, scanStatV, bump] using hres

set_option maxHeartbeats 2000000 in
-- The recursive proof composes the complete scan and cache insertion contracts.
theorem memoD_growth {n : ℕ} (ps : List (Vector ℕ n)) (candidates k : ℕ)
    (H : Vector ℕ n) (K B : ℕ)
    (hrows : ∀ v, VecSmall H v → rowSlots v ≤ B)
    (hkeys : ∀ k v, k ≤ K → VecSmall H v → keySlots k v ≤ B)
    (heap : Heap) (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hsmall : VecSmall H r) (hkBound : k ≤ K) :
    Growth heap (memoD n candidates k heap residual cache parent)
      ((B + 20) * eventWeight (memoStatV ps k r cs).2) := by
  induction k generalizing heap residual cache parent r cs with
  | zero =>
    rw [memoD, memoLayer]
    let key := allocateBlob heap (encodeKey (0, r.toList))
    have hk := allocateBlob_correct heap (encodeKey (0, r.toList))
    have hkeySize : key.2.size ≤ heap.size + B := by
      have hs := hkeys (0) r hkBound hsmall
      simpa only [key, allocateBlob, allocateBlock_size, blobSlots_length, keySlots] using
        Nat.add_le_add_left hs heap.size
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
        intro result hv
        simp only [thenD_value, Option.bind_some, vectorRead_correct _ _ _ hh hr, costBind_value,
          addNatD_value, hwrite, hreadKey, hfound, ret, Option.some.injEq] at hv
        subst result
        have hs := hkeys (0) r hkBound hsmall
        simp only [key, allocateBlob, allocateBlock_size, blobSlots_length]
        dsimp only [keySlots] at hs
        simp only [eventWeight]
        nlinarith only [hs]
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
      have hzero := zeroResult_growth framed residual cache r hwfr (blobRep_persist heall _ _ hr)
      have hzeroSize := hzero out hout
      have hfrSize : framed.size = key.2.size + 3 := by simp [framed, allocateBlock_size]
      have hframe : read out.heap (key.2.size + 1) = some (.ref key.1) := by
        rw [heout.read_old _ (by simp [framed, allocateBlock_size])]
        exact read_allocateBlock_new key.2 _ 1 (by simp)
      have hkey := blobRep_persist (extends_trans hefr heout) _ _ hk
      have hs := saveResult_growth out key.2.size key.1 (0, r)
        (if TreeBudgetVector.isZero r then some [] else none) cs
        { calls := 1, expansions := 1, lookupComparisons := (lookupStatV cs (0, r)).2 }
        hwout hframe hkey (by simpa [wireAnswer] using ha) hcache
      have hstart : out.heap.size ≤ heap.size + (B + 6) := by omega
      have hg := growth_start hstart hs
      have hres := growth_mono hg (show B + 6 + (4 * cs.length + 4) ≤
        (B + 20) * eventWeight (memoStatV ps 0 r cs).2 by
          simp only [memoStatV, hlookup, insertStatV, eventWeight, Counts.add]
          nlinarith only [])
      simpa [Growth, vectorRead_correct _ _ _ hh hr, costBind_value,
        hwrite, hreadKey, hfound, alloc_value _ _ href,
        framed, thenD_value, charge, zeroNatD_value, subNatD_value, hout, memoStatV, hlookup, hlookupV, insertStatV, hev,
        TreeBudgetCostedSearch.counts_add_assoc, Counts.add] using hres
  | succ k ih =>
    rw [memoD, memoLayer]
    let key := allocateBlob heap (encodeKey (k + 1, r.toList))
    have hk := allocateBlob_correct heap (encodeKey (k + 1, r.toList))
    have hkeySize : key.2.size ≤ heap.size + B := by
      have hs := hkeys (k + 1) r hkBound hsmall
      simpa only [key, allocateBlob, allocateBlock_size, blobSlots_length, keySlots] using
        Nat.add_le_add_left hs heap.size
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
        intro result hv
        simp only [thenD_value, Option.bind_some, vectorRead_correct _ _ _ hh hr, costBind_value,
          addNatD_value, hwrite, hreadKey, hfound, ret, Option.some.injEq] at hv
        subst result
        have hs := hkeys (k + 1) r hkBound hsmall
        simp only [key, allocateBlob, allocateBlock_size, blobSlots_length]
        dsimp only [keySlots] at hs
        simp only [eventWeight]
        nlinarith only [hs]
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
        exact memoD_correct ps candidates k h rr cc pp rv csv hhw (rowsRep_persist hext _ _ hpc) hrr hcc hpp
      obtain ⟨out, hout, ha, hcache, hwout, heout, hev⟩ := scanD_correct framed _ _ hsolver
        ps framed candidates residual cache key.2.size r cs (framed.size + 1) hwfr hpc
        (blobRep_persist heall _ _ hr) (TreeBudgetChargedCache.cacheRep_persist heall hc)
        (by simp [framed, allocateBlock_size]) (by have := rowsRep_address_lt hpc; omega) (extends_refl framed)
      have hbudget : ∀ h rr cc pp rv csv, WellFormed h → RowRep h rr rv.toList →
          TreeBudgetChargedCache.CacheRep h cc (wireCache csv) → pp < h.size →
          Extends framed h → VecSmall H rv →
          Growth h (memoD n candidates k h rr cc pp)
            ((B + 20) * eventWeight (memoStatV ps k rv csv).2) := by
        intro h rr cc pp rv csv hhw hrr hcc hpp hext hsv
        exact ih h rr cc pp rv csv hhw (rowsRep_persist hext _ _ hpc) hrr hcc hpp hsv (by omega)
      have hscan := scanD_growth framed _ _ hsolver H B hrows hbudget
        ps framed candidates residual cache key.2.size r cs (framed.size + 1) hwfr hpc
        (blobRep_persist heall _ _ hr) (TreeBudgetChargedCache.cacheRep_persist heall hc)
        (by simp [framed, allocateBlock_size]) (by have := rowsRep_address_lt hpc; omega)
        (extends_refl framed) hsmall
      have hscanSize := hscan out hout
      have hfrSize : framed.size = key.2.size + 3 := by simp [framed, allocateBlock_size]
      have hframe : read out.heap (key.2.size + 1) = some (.ref key.1) := by
        rw [heout.read_old _ (by simp [framed, allocateBlock_size])]
        exact read_allocateBlock_new key.2 _ 1 (by simp)
      have hkey := blobRep_persist (extends_trans hefr heout) _ _ hk
      have hs := saveResult_growth out key.2.size key.1 (k + 1, r)
        (scanStatV (memoStatV ps k) r ps cs).1.1 (scanStatV (memoStatV ps k) r ps cs).1.2
        { calls := 1, expansions := 1, lookupComparisons := (lookupStatV cs (k + 1, r)).2 }
        hwout hframe hkey ha hcache
      have hstart : out.heap.size ≤ heap.size +
          (B + 3 + (B + 20) * (1 + eventWeight (scanStatV (memoStatV ps k) r ps cs).2)) := by omega
      have hg := growth_start hstart hs
      have hres := growth_mono hg (show
        B + 3 + (B + 20) * (1 + eventWeight (scanStatV (memoStatV ps k) r ps cs).2) +
          (4 * (scanStatV (memoStatV ps k) r ps cs).1.2.length + 4) ≤
        (B + 20) * eventWeight (memoStatV ps (k + 1) r cs).2 by
          simp only [memoStatV, hlookup, insertStatV, eventWeight, Counts.add]
          nlinarith only [])
      simpa [Growth, vectorRead_correct _ _ _ hh hr, costBind_value,
        hwrite, hreadKey, hfound, alloc_value _ _ href,
        framed, thenD_value, charge, zeroNatD_value, subNatD_value, hout, memoStatV, hlookup, hlookupV, insertStatV, hev,
        TreeBudgetCostedSearch.counts_add_assoc, Counts.add] using hres

end UAVProof.TreeBudgetStoredHeapGrowth
