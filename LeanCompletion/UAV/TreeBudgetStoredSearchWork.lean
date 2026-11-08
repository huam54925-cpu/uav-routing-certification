import LeanCompletion.UAV.TreeBudgetStoredControlWork

namespace UAVProof.TreeBudgetStoredSearchWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredCursor
open TreeBudgetStoredSearch TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredNodeWork
open TreeBudgetStoredPayloadWork TreeBudgetStoredCacheWork TreeBudgetStoredControlWork
open TreeBudgetStoredWorkInvariant TreeBudgetStoredHeapGrowth TreeBudgetStoredAllocation
open TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetCostedSearchBounds
open TreeBudgetVectorMemoState TreeBudgetVectorSearchStats TreeBudgetSearchStats

def searchRate (B W : ℕ) : ℕ := 1048576 * (B + 1) ^ 3 * (W + 2)

@[simp] theorem work_addEvents (events : Counts) (out : Costed (Option Result)) :
    work (addEvents events out) = work out := rfl

theorem scan_envelope (B W : ℕ) :
    144 * (W + 1) + 1 + 256 * (W + 1) +
      2 * (16384 * (B + 1) ^ 2 * (W + 2)) + 1024 * (B + 1) ^ 2 +
      8192 * (B + 1) ^ 3 * (W + 2) + 18432 * (W + 2) +
      512 * (W + 1) + 128 * (W + 1) + 16384 * (W + 2) + 30 ≤ searchRate B W := by
  have hpow : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul := Nat.mul_le_mul_right (W + 2) hpow
  have hprod : (B + 1) ^ 2 ≤ (B + 1) ^ 3 * (W + 2) :=
    hpow.trans (Nat.le_mul_of_pos_right _ (by omega))
  have h1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have hw := Nat.mul_le_mul_right (W + 2) h1
  dsimp [searchRate]
  nlinarith only [hmul, hprod, hw, Nat.zero_le W]

theorem memo_envelope (B W lc sc : ℕ) :
    16384 * (B + 1) ^ 2 * (W + 2) + 16384 * (B + 1) ^ 3 * (W + 2) +
      4096 * (B + 1) * (W + 2) + cacheUnit B W * (lc + 1) + 8192 * (W + 2) +
      144 * (B + 1) + 144 * (W + 1) + cacheUnit B W * (sc + 2) +
      512 * (W + 2) + 30 ≤ searchRate B W * (1 + lc + sc) := by
  have hpow : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlin : B + 1 ≤ (B + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ B + 1 by omega) (show 1 ≤ 3 by omega)
  have hmul := Nat.mul_le_mul_right (W + 2) hpow
  have hlinmul := Nat.mul_le_mul_right (W + 2) hlin
  have hlin' := hlin.trans (Nat.le_mul_of_pos_right ((B + 1) ^ 3) (by omega : 0 < W + 2))
  have h1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have hw := Nat.mul_le_mul_right (W + 2) h1
  have hcache := Nat.mul_le_mul_right (lc + sc + 3) hlinmul
  have hnonneg := Nat.zero_le ((B + 1) ^ 3 * (W + 2) * (lc + sc))
  dsimp [searchRate, cacheUnit]
  nlinarith only [hmul, hlinmul, hlin', hw, hcache, hnonneg, Nat.zero_le W]

theorem width_in_capacity (B N W a : ℕ) (hw : (8 * (N + B + 1)).size ≤ W)
    (ha : a ≤ 8 * (N + B + 1)) : a.size ≤ W := (Nat.size_le_size ha).trans hw

theorem child_capacity (a framed B child tail N : ℕ)
    (hf : framed ≤ a + B + 5) (hc : a + (B + 20) * (2 + child + tail) ≤ N) :
    framed + (B + 20) * child ≤ N := by
  nlinarith only [hf, hc, Nat.zero_le ((B + 20) * tail)]

theorem tail_capacity (a framed after B child tail N : ℕ)
    (hf : framed ≤ a + B + 5) (ha : after ≤ framed + (B + 20) * child)
    (hc : a + (B + 20) * (2 + child + tail) ≤ N) :
    after + (B + 20) * (1 + tail) ≤ N := by nlinarith only [hf, ha, hc]

theorem cache_small_stat {n : ℕ} (K : ℕ) (H : Vector ℕ n) (ps : List (Vector ℕ n))
    (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) (hk : k ≤ K) (hr : VecSmall H r)
    (hc : CacheSmall K H cs) : CacheSmall K H (memoStatV ps k r cs).1.2 := by
  have h := TreeBudgetCostedSearch.memoCost_observe (TreeBudgetBinarySearch.backend n) ps k r cs
  have hv := congrArg (fun out => out.1.2) h
  dsimp [TreeBudgetCostedSearch.observe] at hv
  rw [← hv]
  exact memoCost_small _ K H ps k r cs hk hr hc


set_option maxHeartbeats 4000000 in
-- Replays the exact pointer-driven branches, with a capacity already derived from allocation.
theorem scanD_work {n : ℕ} (origin : Heap)
    (solve : Heap → ℕ → ℕ → ℕ → Costed (Option Result))
    (spec : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (hsolve : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → ResultRep heap (solve heap residual cache parent)
        (wireAnswer (spec r cs).1.1) (wireCache (spec r cs).1.2) (spec r cs).2)
    (K B N W : ℕ) (H : Vector ℕ n) (hb : PayloadBounds K H B)
    (hW : 1 ≤ W) (hwidth : (8 * (N + B + 1)).size ≤ W)
    (hsmallSpec : ∀ r cs, VecSmall H r → CacheSmall K H cs → CacheSmall K H (spec r cs).1.2)
    (hgrowth : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → VecSmall H r →
      Growth heap (solve heap residual cache parent) ((B + 20) * eventWeight (spec r cs).2))
    (hbudget : ∀ heap residual cache parent r cs,
      WellFormed heap → RowRep heap residual r.toList →
      TreeBudgetChargedCache.CacheRep heap cache (wireCache cs) → parent < heap.size →
      Extends origin heap → VecSmall H r → CacheSmall K H cs →
      heap.size + (B + 20) * eventWeight (spec r cs).2 ≤ N →
      work (solve heap residual cache parent) ≤ searchRate B W * eventWeight (spec r cs).2)
    (ps : List (Vector ℕ n)) (heap : Heap) (candidates residual cache parent : ℕ)
    (r : Vector ℕ n) (cs : CacheV n) (fuel : ℕ)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hf : candidates < fuel) (hbase : Extends origin heap)
    (hsmall : VecSmall H r) (hps : ∀ p ∈ ps, VecSmall H p) (hcs : CacheSmall K H cs)
    (hfw : fuel.size ≤ W)
    (hcap : heap.size + (B + 20) * (1 + eventWeight (scanStatV spec r ps cs).2) ≤ N) :
    work (scanD n solve fuel heap candidates residual cache parent) ≤
      searchRate B W * (1 + eventWeight (scanStatV spec r ps cs).2) := by
  have hrows := hb.rows
  induction ps generalizing heap candidates residual cache parent cs fuel with
  | nil =>
    cases hp with
    | nil a header =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hheap : heap.size ≤ N := by omega
        have ha := rowsRep_address_lt (RowsRep.nil candidates header)
        have hhead := rowsHead_work heap candidates W (width_in_capacity B N W _ hwidth (by omega))
        have hcursor := cursor_work (fuel + 1) W hfw hW
        have hfail := TreeBudgetStoredControlWork.failResult_work heap cache W
          (width_in_capacity B N W _ hwidth (by omega))
        have henv := scan_envelope B W
        rw [scanD, work_then_some _ _ _ (cursorStep_succ fuel),
          work_then_some _ _ _ (rowsHead_nil _ _ hh header)]
        simp only [scanStatV, eventWeight, Nat.zero_add, Nat.mul_one]
        omega
  | cons p ps ih =>
    cases hp with
    | cons a row tail _ _ header hrow htail hrl htl =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hheap : heap.size ≤ N := by omega
        have hsp := hps p (by simp)
        have hsps : ∀ p ∈ ps, VecSmall H p := fun p hp => hps p (by simp [hp])
        have hread := rowsHead_cons heap candidates row tail hh header
        have hpread := vectorRead_correct heap row p hh hrow
        have hrread := vectorRead_correct heap residual r hh hr
        have ha := rowsRep_address_lt (RowsRep.cons candidates row tail p.toList
          (ps.map Vector.toList) header hrow htail hrl htl)
        have hhead := rowsHead_work heap candidates W (width_in_capacity B N W _ hwidth (by omega))
        have hcursor := cursor_work (fuel + 1) W hfw hW
        have hwheap : (heap.size + 1).size ≤ W := width_in_capacity B N W _ hwidth (by omega)
        have hpwork := vectorRead_work heap row p B W hh hrow hb.dimension (rows_bytes hb hsp) hW hwheap
        have hrwork := vectorRead_work heap residual r B W hh hr hb.dimension (rows_bytes hb hsmall) hW hwheap
        have hpw : ∀ i : Fin n, p[i].size ≤ B := fun i => (Nat.size_le_size (hsp i)).trans (hb.coordinates i)
        have hrw : ∀ i : Fin n, r[i].size ≤ B := fun i => (Nat.size_le_size (hsmall i)).trans (hb.coordinates i)
        have hdim := Nat.mul_le_mul_right (B + 1) (Nat.add_le_add_right hb.dimension 1)
        have hguardWork : work (guardV p r) ≤ 512 * (B + 1) ^ 2 := by
          have hs := guardV_steps p r B hpw hrw
          have ha := (vector_allocations_le_steps p r).1
          unfold work
          nlinarith only [hs, ha, hdim]
        have henv := scan_envelope B W
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
          have hgrowthRun := hgrowth framed child.1 cache child.2.size (TreeBudgetVector.sub r p) cs hwfr
            (blobRep_persist hefr _ _ hchild)
            (TreeBudgetChargedCache.cacheRep_persist hehf hc) hbframe (extends_trans hbase hehf) hsmall'
          obtain ⟨out, hout, hans, hcache, hwout, heout, hevents⟩ := hsub
          have hchildSize := hgrowthRun out hout
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
          dsimp only [child] at halloc
          have hsubWork : work (subV r p) ≤ 512 * (B + 1) ^ 2 := by
            have hs := subV_steps r p B hrw hpw
            have ha := (vector_allocations_le_steps r p).2.2.1
            unfold work
            nlinarith only [hs, ha, hdim]
          have hremaining := vecSmall_sub H r p hsmall
          have hvecWork := vectorWrite_work heap (TreeBudgetVector.sub r p) B W hb.dimension
            (fun i => (Nat.size_le_size (hremaining i)).trans (hb.coordinates i))
            (rows_bytes hb hremaining)
            (width_in_capacity B N W _ hwidth (by have hs := hb.rows _ hremaining; omega))
          have hallocWork := alloc_work child.2 (frameSlots row tail residual parent) W
            (width_in_capacity B N W _ hwidth (by
              have hs := hb.rows (TreeBudgetVector.sub r p) hremaining
              simp only [child, allocateBlob, allocateBlock_size, blobSlots_length,
                frameSlots, List.length_cons, List.length_nil]
              dsimp only [rowSlots] at hs
              omega))
          have hallocWork' : work (alloc child.2 (frameSlots row tail residual parent)) ≤ 18432 * (W + 2) := by
            simpa [frameSlots] using hallocWork
          cases hspec : spec (TreeBudgetVector.sub r p) cs with
          | mk pair events =>
            rcases pair with ⟨ans, cs'⟩
            simp only [hspec] at hans hcache hevents hchildSize
            have hcs' := hsmallSpec (TreeBudgetVector.sub r p) cs hremaining hcs
            simp only [hspec] at hcs'
            cases ans with
            | none =>
              have hweight : eventWeight (scanStatV spec r (p :: ps) cs).2 =
                  1 + eventWeight events + eventWeight (scanStatV spec r ps cs').2 := by
                simp [scanStatV, hguard, hspec, bump, eventWeight, Counts.add]
                omega
              rw [hweight] at hcap ⊢
              have hcap' : heap.size + (B + 20) *
                  (2 + eventWeight events + eventWeight (scanStatV spec r ps cs').2) ≤ N := by nlinarith only [hcap]
              have hchildCap := child_capacity _ _ _ _ _ _ hfrSize hcap'
              have hchildWork := hbudget framed child.1 cache child.2.size (TreeBudgetVector.sub r p) cs hwfr
                (blobRep_persist hefr _ _ hchild) (TreeBudgetChargedCache.cacheRep_persist hehf hc)
                hbframe (extends_trans hbase hehf) hremaining hcs (by simpa only [hspec] using hchildCap)
              simp only [hspec] at hchildWork
              have htailCap := tail_capacity _ _ _ _ _ _ _ hfrSize hchildSize hcap'
              have houtSize : out.heap.size ≤ N := by omega
              have hanswerRead := answerHead_failure _ _ hwout hans
              have htailWork := ih out.heap tail residual out.cache parent cs' fuel hwout
                (rowsRep_persist he _ _ htail) (blobRep_persist he _ _ hr) hcache
                (hparent.trans_le he.size_le) (by omega) (extends_trans hbase he) hsps hcs'
                ((Nat.size_le_size (Nat.le_succ fuel)).trans hfw) htailCap
              have hfrBound : child.2.size < out.heap.size := hbframe.trans_le heout.size_le
              have hframeWork := frameRead_work out.heap child.2.size W
                (width_in_capacity B N W _ hwidth (by omega))
              have hansBound := answerRep_address_lt hans
              have hansWork := answerHead_work out.heap out.answer W
                (width_in_capacity B N W _ hwidth (by omega))
              rw [scanD, work_then_some _ _ _ (cursorStep_succ fuel), work_then_some _ _ _ hread]
              simp only [work_addEvents]
              rw [work_then_some _ _ _ hpread, work_then_some _ _ _ hrread, work_bind, guardV_value]
              simp only [hguard, ↓reduceIte, work_bind, subV_value, vectorWrite_value, halloc]
              rw [work_then_some _ _ _ hout, work_then_some _ _ _ hframeRead, work_then_some _ _ _ hanswerRead]
              simp only [work_addEvents]
              nlinarith only [hhead, hcursor, hpwork, hrwork, hguardWork, hsubWork, hvecWork,
                hallocWork', hchildWork, hframeWork, hansWork, htailWork, henv]
            | some rows =>
              have hweight : eventWeight (scanStatV spec r (p :: ps) cs).2 = 1 + eventWeight events := by
                simp [scanStatV, hguard, hspec, bump, eventWeight, Counts.add]
                omega
              rw [hweight] at hcap ⊢
              have hcap' : heap.size + (B + 20) * (2 + eventWeight events + 0) ≤ N := by nlinarith only [hcap]
              have hchildCap := child_capacity _ _ _ _ _ _ hfrSize hcap'
              have hchildWork := hbudget framed child.1 cache child.2.size (TreeBudgetVector.sub r p) cs hwfr
                (blobRep_persist hefr _ _ hchild) (TreeBudgetChargedCache.cacheRep_persist hehf hc)
                hbframe (extends_trans hbase hehf) hremaining hcs (by simpa only [hspec] using hchildCap)
              simp only [hspec] at hchildWork
              have houtSize : out.heap.size ≤ N := by omega
              obtain ⟨rowsRef, hanswerRead, hrowsRep⟩ := answerHead_success _ _ _ hwout hans
              have hfrBound : child.2.size < out.heap.size := hbframe.trans_le heout.size_le
              have hframeWork := frameRead_work out.heap child.2.size W
                (width_in_capacity B N W _ hwidth (by omega))
              have hansBound := answerRep_address_lt hans
              have hansWork := answerHead_work out.heap out.answer W
                (width_in_capacity B N W _ hwidth (by omega))
              have hpreWork := TreeBudgetStoredControlWork.prependResult_work out.heap row rowsRef out.cache W events
                ((blobRep_address_lt _ _ _ hrow).trans_le he.size_le) (rowsRep_address_lt hrowsRep)
                (width_in_capacity B N W _ hwidth (by omega))
              rw [scanD, work_then_some _ _ _ (cursorStep_succ fuel), work_then_some _ _ _ hread]
              simp only [work_addEvents]
              rw [work_then_some _ _ _ hpread, work_then_some _ _ _ hrread, work_bind, guardV_value]
              simp only [hguard, ↓reduceIte, work_bind, subV_value, vectorWrite_value, halloc]
              rw [work_then_some _ _ _ hout, work_then_some _ _ _ hframeRead, work_then_some _ _ _ hanswerRead]
              rw [hevents]
              nlinarith only [hhead, hcursor, hpwork, hrwork, hguardWork, hsubWork, hvecWork,
                hallocWork', hchildWork, hframeWork, hansWork, hpreWork, henv]
        · have hweight : eventWeight (scanStatV spec r (p :: ps) cs).2 = 1 + eventWeight (scanStatV spec r ps cs).2 := by
            simp [scanStatV, hguard, bump, eventWeight, Counts.add]
            omega
          rw [hweight] at hcap ⊢
          have htailCap : heap.size + (B + 20) * (1 + eventWeight (scanStatV spec r ps cs).2) ≤ N := by
            nlinarith only [hcap]
          have htailWork := ih heap tail residual cache parent cs fuel hh htail hr hc hparent (by omega) hbase
            hsps hcs ((Nat.size_le_size (Nat.le_succ fuel)).trans hfw) htailCap
          rw [scanD, work_then_some _ _ _ (cursorStep_succ fuel), work_then_some _ _ _ hread]
          simp only [work_addEvents]
          rw [work_then_some _ _ _ hpread, work_then_some _ _ _ hrread, work_bind, guardV_value]
          simp only [hguard, Bool.false_eq_true, ↓reduceIte]
          simp only [Nat.mul_add, Nat.mul_one] at htailWork ⊢
          omega

end UAVProof.TreeBudgetStoredSearchWork
