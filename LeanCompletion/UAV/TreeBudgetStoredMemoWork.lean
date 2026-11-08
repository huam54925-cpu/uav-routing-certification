import LeanCompletion.UAV.TreeBudgetStoredSearchWork

namespace UAVProof.TreeBudgetStoredMemoWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredCursor
open TreeBudgetStoredSearch TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredNodeWork
open TreeBudgetStoredPayloadWork TreeBudgetStoredCacheWork TreeBudgetStoredControlWork
open TreeBudgetStoredWorkInvariant TreeBudgetStoredHeapGrowth TreeBudgetStoredAllocation
open TreeBudgetStoredSearchWork TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetCostedSearchBounds
open TreeBudgetVectorMemoState TreeBudgetVectorSearchStats TreeBudgetSearchStats

set_option maxHeartbeats 2000000 in
theorem memoLayer_work {n : ℕ} (k K B N W : ℕ) (H : Vector ℕ n)
    (hb : PayloadBounds K H B) (hW : 1 ≤ W) (hw : (8 * (N + B + 1)).size ≤ W)
    (heap : Heap) (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (expand : Heap → ℕ → Costed (Option Result)) (ans : AnswerV n) (cs' : CacheV n) (ev : Counts)
    (hh : WellFormed heap) (hr : RowRep heap residual r.toList)
    (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs)) (hparent : parent < heap.size)
    (hsmall : VecSmall H r) (hkBound : k ≤ K) (hcs : CacheSmall K H cs)
    (hnew : CacheSmall K H cs') (hheap : heap.size ≤ N)
    (hcap : (lookupStatV cs (k, r)).1 = none →
      heap.size + (B + 20) * (2 + (lookupStatV cs (k, r)).2 + eventWeight ev + cs'.length) ≤ N)
    (hexpand : ∀ framed frame,
      WellFormed framed → Extends heap framed →
      framed.size ≤ heap.size + B + 3 → frame < framed.size →
      (lookupStatV cs (k, r)).1 = none →
      ResultRep framed (expand framed frame) (wireAnswer ans) (wireCache cs') ev ∧
      Growth framed (expand framed frame) ((B + 20) * (1 + eventWeight ev)) ∧
      work (expand framed frame) ≤ searchRate B W * (1 + eventWeight ev) +
        144 * (B + 1) + 72 * (W + 1)) :
    work (memoLayer n k heap residual cache parent expand) ≤ searchRate B W *
      (match (lookupStatV cs (k, r)).1 with
       | some _ => 1 + (lookupStatV cs (k, r)).2
       | none => 2 + (lookupStatV cs (k, r)).2 + eventWeight ev + cs'.length) := by
  let key := allocateBlob heap (encodeKey (k, r.toList))
  have hk := allocateBlob_correct heap (encodeKey (k, r.toList))
  have hkeySize : key.2.size ≤ heap.size + B := by
    have hs := hb.keys k r hkBound hsmall
    simpa only [key, allocateBlob, allocateBlock_size, blobSlots_length, keySlots] using
      Nat.add_le_add_left hs heap.size
  have he : Extends heap key.2 := allocateBlock_extends ..
  have hkeyWF : WellFormed key.2 := allocateBlob_wellFormed heap _ hh
  have hc' := TreeBudgetChargedCache.cacheRep_persist he hc
  have hwrite : (keyWrite heap k r).value = key := keyWrite_value heap k r
  have hreadKey : (blobRead key.2 key.1).value = some (encodeKey (wireKey (k, r))) :=
    blobRead_correct key.2 key.1 _ hkeyWF hk
  have hbytes := keys_bytes hb hkBound hsmall
  have hreadWork := vectorRead_work heap residual r B W hh hr hb.dimension (rows_bytes hb hsmall) hW
    (width_in_capacity B N W _ hw (by omega))
  have hwriteWork := keyWrite_work heap k r B W hb.dimension
    ((Nat.size_le_size hkBound).trans hb.depth)
    (fun i => (Nat.size_le_size (hsmall i)).trans (hb.coordinates i)) hbytes
    (width_in_capacity B N W _ hw (by have hs := hb.keys k r hkBound hsmall; omega))
  have hkeyWork := blobRead_work key.2 key.1 (encodeKey (wireKey (k, r))) W hkeyWF hk hW
    (width_in_capacity B N W _ hw (by omega))
  have hkeyWork' : work (blobRead key.2 key.1) ≤ 4096 * (B + 1) * (W + 2) :=
    hkeyWork.trans (by gcongr; exact hbytes)
  have hinit := (arithmetic_work key.2.size 1 W
    (width_in_capacity B N W _ hw (by omega)) (by simpa using hW)).2.2
  have hlookupWork := lookupD_work key.2 cache (wireCache cs) (wireKey (k, r)) (key.2.size + 1) B W
    hkeyWF hc' (by have := TreeBudgetChargedCache.cacheRep_address_lt hc'; omega) hW
    (width_in_capacity B N W _ hw (by omega))
    (width_in_capacity B N W _ hw (by omega)) (cache_keys_bytes hb cs hcs) hbytes
  rw [lookupCount_vector] at hlookupWork
  obtain ⟨found, hfound, hfoundRep⟩ := lookupD_correct key.2 cache (wireCache cs) hkeyWF hc'
    (wireKey (k, r)) (key.2.size + 1) (by have := TreeBudgetChargedCache.cacheRep_address_lt hc'; omega)
  rw [lookupWire_vector, ← lookupStatV_erase] at hfoundRep
  rw [lookupCount_vector] at hfound
  cases hlookup : (lookupStatV cs (k, r)).1 with
  | some answer =>
    cases found with
    | none => simp only [hlookup, Option.map_some, FoundRep] at hfoundRep
    | some a =>
      have henv := memo_envelope B W (lookupStatV cs (k, r)).2 0
      rw [memoLayer, work_then_some _ _ _ (vectorRead_correct _ _ _ hh hr), work_bind, hwrite,
        work_then_some _ _ _ hreadKey, work_bind, addNatD_value, work_then_some _ _ _ hfound]
      simp only [work_ret, hlookup]
      simp only [Nat.add_zero, Nat.mul_add, Nat.mul_one] at hreadWork hwriteWork hkeyWork' hlookupWork henv ⊢
      omega
  | none =>
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
    have hwfr : WellFormed framed := wellFormed_allocateBlock _ _ hkeyWF href
    have hfrSize : framed.size = key.2.size + 3 := by simp [framed, allocateBlock_size]
    have hfrBound : framed.size ≤ heap.size + B + 3 := by omega
    have hbframe : key.2.size < framed.size := by omega
    obtain ⟨hspec, hgrowth, hwork⟩ := hexpand framed key.2.size hwfr heall hfrBound hbframe hlookup
    obtain ⟨out, hout, ha, hcache, hwout, heout, hev⟩ := hspec
    have houtGrowth := hgrowth out hout
    have hcap' := hcap hlookup
    have houtSize : out.heap.size ≤ N := by nlinarith only [houtGrowth, hfrBound, hcap']
    have hframe : read out.heap (key.2.size + 1) = some (.ref key.1) := by
      rw [heout.read_old _ (by omega)]
      exact read_allocateBlock_new key.2 _ 1 (by simp)
    have hkey := blobRep_persist (extends_trans hefr heout) _ _ hk
    have hlen := cacheLength_le_heap out.heap out.cache (wireCache cs') hcache
    simp only [wireCache, List.length_map] at hlen
    have hs := saveResult_work out key.2.size key.1 (k, r) ans cs'
      { calls := 1, expansions := 1, lookupComparisons := (lookupStatV cs (k, r)).2 } B W
      hwout hframe hkey ha hcache hW
      (width_in_capacity B N W _ hw (by omega))
      (width_in_capacity B N W _ hw (by omega)) (cache_keys_bytes hb cs' hnew) hbytes
    have halloc := alloc_value key.2 [.bit true, .ref key.1, .ref parent] href
    have hallocWork := alloc_work key.2 [.bit true, .ref key.1, .ref parent] W
      (width_in_capacity B N W _ hw (by simp only [List.length_cons, List.length_nil]; omega))
    norm_num only [List.length_cons, List.length_nil] at hallocWork
    have henv := memo_envelope B W (lookupStatV cs (k, r)).2 cs'.length
    rw [memoLayer, work_then_some _ _ _ (vectorRead_correct _ _ _ hh hr), work_bind, hwrite,
      work_then_some _ _ _ hreadKey, work_bind, addNatD_value, work_then_some _ _ _ hfound]
    simp only [work_bind, halloc, hlookup]
    rw [work_then_some _ _ _ hout]
    simp only [Nat.mul_add, Nat.mul_one] at hreadWork hwriteWork hkeyWork' hlookupWork hallocWork hs hwork henv ⊢
    omega


theorem scan_small_stat {n : ℕ} (K : ℕ) (H : Vector ℕ n) (ps : List (Vector ℕ n))
    (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) (hk : k ≤ K) (hr : VecSmall H r)
    (hc : CacheSmall K H cs) :
    CacheSmall K H (scanStatV (memoStatV ps k) r ps cs).1.2 := by
  have ho := TreeBudgetCostedSearch.scanCost_observe (TreeBudgetBinarySearch.backend n)
    (TreeBudgetCostedSearch.memoCost (TreeBudgetBinarySearch.backend n) ps k)
    (memoStatV ps k) (TreeBudgetCostedSearch.memoCost_observe (TreeBudgetBinarySearch.backend n) ps k) r ps cs
  have hv := congrArg (fun out => out.1.2) ho
  dsimp [TreeBudgetCostedSearch.observe] at hv
  rw [← hv]
  exact scanCost_small _ K H _ (fun r cs hr hc => memoCost_small _ K H ps k r cs hk hr hc) r ps cs hr hc

set_option maxHeartbeats 4000000 in
theorem memoD_work {n : ℕ} (ps : List (Vector ℕ n)) (candidates k : ℕ)
    (H : Vector ℕ n) (K B N W : ℕ) (hb : PayloadBounds K H B)
    (hW : 1 ≤ W) (hwidth : (8 * (N + B + 1)).size ≤ W)
    (hps : ∀ p ∈ ps, VecSmall H p)
    (heap : Heap) (residual cache parent : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hh : WellFormed heap) (hp : RowsRep heap candidates (ps.map Vector.toList))
    (hr : RowRep heap residual r.toList) (hc : TreeBudgetChargedCache.CacheRep heap cache (wireCache cs))
    (hparent : parent < heap.size) (hsmall : VecSmall H r) (hkBound : k ≤ K)
    (hcs : CacheSmall K H cs)
    (hcap : heap.size + (B + 20) * eventWeight (memoStatV ps k r cs).2 ≤ N) :
    work (memoD n candidates k heap residual cache parent) ≤
      searchRate B W * eventWeight (memoStatV ps k r cs).2 := by
  induction k generalizing heap residual cache parent r cs with
  | zero =>
    have hstats : eventWeight (memoStatV ps 0 r cs).2 =
        (match (lookupStatV cs (0, r)).1 with
        | some _ => 1 + (lookupStatV cs (0, r)).2
        | none => 2 + (lookupStatV cs (0, r)).2 + eventWeight ({} : Counts) + cs.length) := by
      cases hl : (lookupStatV cs (0, r)).1 <;> simp only [memoStatV, hl, insertStatV, eventWeight, Counts.add] <;> ring
    rw [hstats] at hcap ⊢
    rw [memoD]
    simp only [zeroNatD_value, decide_true, ↓reduceDIte]
    apply memoLayer_work 0 K B N W H hb hW hwidth heap residual cache parent r cs _
      (if TreeBudgetVector.isZero r then some [] else none) cs {} hh hr hc hparent hsmall
      hkBound hcs hcs (by omega) (by intro hl; simpa only [hl] using hcap)
    intro framed frame hwfr he hfr hframe hl
    have hzero := zeroResult_correct framed residual cache r (wireCache cs) hwfr
      (blobRep_persist he _ _ hr) (TreeBudgetChargedCache.cacheRep_persist he hc)
    have hg := zeroResult_growth framed residual cache r hwfr (blobRep_persist he _ _ hr)
    have hfrCap : framed.size + 3 ≤ N := by
      simp only [hl, eventWeight] at hcap
      nlinarith only [hcap, hfr]
    have hz := zeroResult_work framed residual cache B W r hwfr (blobRep_persist he _ _ hr)
      hb.dimension (fun i => (Nat.size_le_size (hsmall i)).trans (hb.coordinates i))
      (rows_bytes hb hsmall) hW (width_in_capacity B N W _ hwidth (by omega))
    refine ⟨?_, ?_, ?_⟩
    · simpa [ResultRep, charge, wireAnswer] using hzero
    · simpa only [Growth, charge, eventWeight, Nat.add_zero, Nat.mul_one] using
        growth_mono hg (show 3 ≤ B + 20 by omega)
    · have ht := (arithmetic_work 0 0 B (by simp) (by simp)).1
      change work (zeroNatD 0) ≤ 72 * (B + 1) at ht
      rw [work_charge]
      change work (zeroNatD 0) + _ ≤ _
      dsimp only [eventWeight, searchRate]
      nlinarith only [ht, hz]
  | succ k ih =>
    let spec := scanStatV (memoStatV ps k) r ps cs
    have hstats : eventWeight (memoStatV ps (k + 1) r cs).2 =
        (match (lookupStatV cs (k + 1, r)).1 with
        | some _ => 1 + (lookupStatV cs (k + 1, r)).2
        | none => 2 + (lookupStatV cs (k + 1, r)).2 + eventWeight spec.2 + spec.1.2.length) := by
      cases hl : (lookupStatV cs (k + 1, r)).1 <;>
        simp only [memoStatV, hl, insertStatV, eventWeight, Counts.add, spec, Nat.succ_eq_add_one] <;> ring
    rw [hstats] at hcap ⊢
    rw [memoD]
    simp only [zeroNatD_value, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      decide_false, Bool.false_eq_true, ↓reduceDIte, subNatD_value, Nat.add_sub_cancel]
    apply memoLayer_work (k + 1) K B N W H hb hW hwidth heap residual cache parent r cs _
      spec.1.1 spec.1.2 spec.2 hh hr hc hparent hsmall hkBound hcs
      (scan_small_stat K H ps k r cs (by omega) hsmall hcs) (by omega)
      (by intro hl; simpa only [hl] using hcap)
    intro framed frame hwfr he hfr hframe hl
    have hpc := rowsRep_persist he _ _ hp
    have hrc := blobRep_persist he _ _ hr
    have hcc := TreeBudgetChargedCache.cacheRep_persist he hc
    have hsolver : ∀ h rr cc pp rv csv, WellFormed h → RowRep h rr rv.toList →
        TreeBudgetChargedCache.CacheRep h cc (wireCache csv) → pp < h.size →
        Extends framed h → ResultRep h (memoD n candidates k h rr cc pp)
          (wireAnswer (memoStatV ps k rv csv).1.1) (wireCache (memoStatV ps k rv csv).1.2)
          (memoStatV ps k rv csv).2 := by
      intro h rr cc pp rv csv hhw hrr hcc hpp hext
      exact memoD_correct ps candidates k h rr cc pp rv csv hhw (rowsRep_persist hext _ _ hpc) hrr hcc hpp
    have hscan := scanD_correct framed _ _ hsolver ps framed candidates residual cache frame r cs
      (framed.size + 1) hwfr hpc hrc hcc hframe
      (by have := rowsRep_address_lt hpc; omega) (extends_refl framed)
    have hgrowth : ∀ h rr cc pp rv csv, WellFormed h → RowRep h rr rv.toList →
        TreeBudgetChargedCache.CacheRep h cc (wireCache csv) → pp < h.size →
        Extends framed h → VecSmall H rv →
        Growth h (memoD n candidates k h rr cc pp) ((B + 20) * eventWeight (memoStatV ps k rv csv).2) := by
      intro h rr cc pp rv csv hhw hrr hcc hpp hext hsv
      exact memoD_growth ps candidates k H K B hb.rows hb.keys h rr cc pp rv csv hhw
        (rowsRep_persist hext _ _ hpc) hrr hcc hpp hsv (by omega)
    have hscanGrowth := scanD_growth framed _ _ hsolver H B hb.rows hgrowth ps framed
      candidates residual cache frame r cs (framed.size + 1) hwfr hpc hrc hcc hframe
      (by have := rowsRep_address_lt hpc; omega) (extends_refl framed) hsmall
    have hbudget : ∀ h rr cc pp rv csv, WellFormed h → RowRep h rr rv.toList →
        TreeBudgetChargedCache.CacheRep h cc (wireCache csv) → pp < h.size →
        Extends framed h → VecSmall H rv → CacheSmall K H csv →
        h.size + (B + 20) * eventWeight (memoStatV ps k rv csv).2 ≤ N →
        work (memoD n candidates k h rr cc pp) ≤ searchRate B W * eventWeight (memoStatV ps k rv csv).2 := by
      intro h rr cc pp rv csv hhw hrr hcc hpp hext hsv hcsv hcapacity
      exact ih h rr cc pp rv csv hhw (rowsRep_persist hext _ _ hpc) hrr hcc hpp hsv (by omega) hcsv hcapacity
    have hscanCap : framed.size + (B + 20) * (1 + eventWeight spec.2) ≤ N := by
      simp only [hl] at hcap
      nlinarith only [hcap, hfr]
    have hfrN : framed.size ≤ N := by omega
    have hscanWork := scanD_work framed _ _ hsolver K B N W H hb hW hwidth
      (fun r cs hr hc => cache_small_stat K H ps k r cs (by omega) hr hc) hgrowth hbudget
      ps framed candidates residual cache frame r cs (framed.size + 1) hwfr hpc hrc hcc hframe
      (by have := rowsRep_address_lt hpc; omega) (extends_refl framed) hsmall hps hcs
      (width_in_capacity B N W _ hwidth (by omega)) hscanCap
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ResultRep, charge, costBind_value, addNatD_value] using hscan
    · simpa only [Growth, charge, costBind_value, addNatD_value] using hscanGrowth
    · have hkw := (Nat.size_le_size hkBound).trans hb.depth
      have ht := (arithmetic_work (k + 1) 0 B hkw (by simp)).1
      change work (zeroNatD (k + 1)) ≤ 72 * (B + 1) at ht
      have hd := (arithmetic_work (k + 1) 1 B hkw (by simpa using hb.positive)).2.1
      have hfuel := (arithmetic_work framed.size 1 W
        (width_in_capacity B N W _ hwidth (by omega)) (by simpa using hW)).2.2
      simp only [work_charge, work_bind, addNatD_value]
      change work (zeroNatD (k + 1)) + (work (subNatD (k + 1) 1) + _) ≤ _
      change work (scanD n (memoD n candidates k) (framed.size + 1) framed candidates residual cache frame) ≤ searchRate B W * (1 + eventWeight spec.2) at hscanWork
      omega

end UAVProof.TreeBudgetStoredMemoWork
