import LeanCompletion.UAV.TreeBudgetCostedSearch

/-! Local primitive-work bounds for the actual ordered recursion. Bounds on
primitive executions are explicit hypotheses here; this is a composition
lemma, not a completed binary-input time theorem. -/
namespace UAVProof.TreeBudgetCostedSearchBounds
open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetCostedSearch TreeBudgetSearchStats
variable {n : ℕ}

def eventWeight (c : Counts) : ℕ :=
  c.calls + c.expansions + c.candidates + c.lookupComparisons + c.insertionScans

@[simp] theorem eventWeight_add (a b : Counts) :
    eventWeight (a.add b) = eventWeight a + eventWeight b := by
  simp only [eventWeight, Counts.add]
  omega

def VecSmall (H p : Vector ℕ n) : Prop := ∀ i : Fin n, p[i] ≤ H[i]
def KeySmall (K : ℕ) (H : Vector ℕ n) (q : KeyV n) : Prop :=
  q.1 ≤ K ∧ VecSmall H q.2
def CacheSmall (K : ℕ) (H : Vector ℕ n) (cs : CacheV n) : Prop :=
  ∀ e ∈ cs, KeySmall K H e.1

theorem vecSmall_sub (H r p : Vector ℕ n) (hr : VecSmall H r) :
    VecSmall H (sub r p) := by
  intro i
  change decode (sub r p) i ≤ decode H i
  rw [decode_sub]
  exact (Nat.sub_le r[i] p[i]).trans (hr i)

structure BackendBounded (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ) : Prop where
  keyEq : ∀ p q, KeySmall K H p → KeySmall K H q → (B.keyEq p q).2 ≤ W
  guard : ∀ p q, VecSmall H p → VecSmall H q → (B.guard p q).2 ≤ W
  subtract : ∀ p q, VecSmall H p → VecSmall H q → (B.subtract p q).2 ≤ W
  zero : ∀ p, VecSmall H p → (B.zero p).2 ≤ W

theorem lookupCost_work (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ)
    (hb : BackendBounded B K H W) (cs : CacheV n) (q : KeyV n)
    (hc : CacheSmall K H cs) (hq : KeySmall K H q) :
    (lookupCost B cs q).work ≤
      (W + 1) * (1 + (lookupCost B cs q).events.lookupComparisons) := by
  induction cs with
  | nil => simp [lookupCost]
  | cons e cs ih =>
    have he := hc e (by simp)
    have ht : CacheSmall K H cs := fun e h => hc e (by simp [h])
    have hw := hb.keyEq e.1 q he hq
    have hi := ih ht
    simp only [lookupCost]
    split
    · simp only
      nlinarith
    · simp only [addWork, addEvents, Counts.add] at *
      nlinarith

theorem filterCost_work (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ)
    (hb : BackendBounded B K H W) (cs : CacheV n) (q : KeyV n)
    (hc : CacheSmall K H cs) (hq : KeySmall K H q) :
    (filterCost B cs q).work ≤ (W + 2) * cs.length + 1 := by
  induction cs with
  | nil => simp [filterCost]
  | cons e cs ih =>
    have hw := hb.keyEq e.1 q (hc e (by simp)) hq
    have ht : CacheSmall K H cs := fun e h => hc e (by simp [h])
    have hi := ih ht
    simp only [filterCost, List.length_cons]
    nlinarith

theorem insertCost_work (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ)
    (hb : BackendBounded B K H W) (cs : CacheV n) (q : KeyV n) (a : AnswerV n)
    (hc : CacheSmall K H cs) (hq : KeySmall K H q) :
    (insertCost B cs q a).work ≤ (W + 2) * cs.length + 2 := by
  have h := filterCost_work B K H W hb cs q hc hq
  simp only [insertCost]
  omega

theorem insertCost_small (B : Backend n) (K : ℕ) (H : Vector ℕ n)
    (cs : CacheV n) (q : KeyV n) (a : AnswerV n)
    (hc : CacheSmall K H cs) (hq : KeySmall K H q) :
    CacheSmall K H (insertCost B cs q a).value := by
  rw [insertCost_value]
  intro e he
  simp only [insertV, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | he
  · exact hq
  · exact hc e he.1

theorem lookupCost_weight (B : Backend n) (cs : CacheV n) (q : KeyV n) :
    eventWeight (lookupCost B cs q).events =
      (lookupCost B cs q).events.lookupComparisons := by
  have h := congrArg Prod.snd (lookupCost_observe B cs q)
  change (lookupCost B cs q).events = _ at h
  rw [h]
  simp [eventWeight]

theorem insertCost_weight (B : Backend n) (cs : CacheV n) (q : KeyV n) (a : AnswerV n) :
    eventWeight (insertCost B cs q a).events = cs.length := by
  simp [insertCost, filterCost_events, eventWeight]

theorem scanCost_small (B : Backend n) (K : ℕ) (H : Vector ℕ n)
    (solve : Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n))
    (hs : ∀ r cs, VecSmall H r → CacheSmall K H cs →
      CacheSmall K H (solve r cs).value.2)
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n)
    (hr : VecSmall H r) (hc : CacheSmall K H cs) :
    CacheSmall K H (scanCost B solve r ps cs).value.2 := by
  induction ps generalizing cs with
  | nil => exact hc
  | cons p ps ih =>
    have hsub : VecSmall H (B.subtract r p).1 := by
      rw [B.subtract_value]
      exact vecSmall_sub H r p hr
    have hchild := hs (B.subtract r p).1 cs hsub hc
    simp only [scanCost, addWork, addEvents]
    split
    · split
      · exact hchild
      · exact ih _ hchild
    · exact ih _ hc

theorem memoCost_small (B : Backend n) (K : ℕ) (H : Vector ℕ n)
    (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hk : k ≤ K) (hr : VecSmall H r) (hc : CacheSmall K H cs) :
    CacheSmall K H (memoCost B ps k r cs).value.2 := by
  induction k generalizing r cs with
  | zero =>
    simp only [memoCost]
    split
    · exact hc
    · exact insertCost_small B K H _ _ _ hc ⟨hk, hr⟩
  | succ k ih =>
    have hs := scanCost_small B K H (memoCost B ps k)
      (fun r cs hr hc => ih r cs (by omega) hr hc) r ps cs hr hc
    simp only [memoCost]
    split
    · exact hc
    · exact insertCost_small B K H _ _ _ hs ⟨hk, hr⟩

theorem scanCost_work (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ)
    (hb : BackendBounded B K H W)
    (solve : Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n))
    (hs : ∀ r cs, VecSmall H r → CacheSmall K H cs →
      CacheSmall K H (solve r cs).value.2)
    (hw : ∀ r cs, VecSmall H r → CacheSmall K H cs →
      (solve r cs).work ≤ (4 * W + 8) * eventWeight (solve r cs).events)
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n)
    (hp : ∀ p ∈ ps, VecSmall H p) (hr : VecSmall H r) (hc : CacheSmall K H cs) :
    (scanCost B solve r ps cs).work ≤
      (4 * W + 8) * (1 + eventWeight (scanCost B solve r ps cs).events) := by
  induction ps generalizing cs with
  | nil => simp [scanCost, eventWeight]
  | cons p ps ih =>
    have hp0 := hp p (by simp)
    have hpt : ∀ p ∈ ps, VecSmall H p := fun p h => hp p (by simp [h])
    have hguard := hb.guard p r hp0 hr
    have hsubwork := hb.subtract r p hr hp0
    have hsub : VecSmall H (B.subtract r p).1 := by
      rw [B.subtract_value]
      exact vecSmall_sub H r p hr
    have hchild := hw (B.subtract r p).1 cs hsub hc
    have hsmall := hs (B.subtract r p).1 cs hsub hc
    have htail := ih (solve (B.subtract r p).1 cs).value.2 hpt hsmall
    have hskip := ih cs hpt hc
    simp only [scanCost, addWork, addEvents]
    split
    · split <;> simp only [eventWeight, Counts.add, Nat.zero_add]
      · simp only [eventWeight] at hchild
        nlinarith
      · simp only [eventWeight] at hchild htail
        nlinarith
    · simp only [eventWeight, Counts.add, Nat.zero_add]
      simp only [eventWeight] at hskip
      nlinarith

theorem memoCost_work (B : Backend n) (K : ℕ) (H : Vector ℕ n) (W : ℕ)
    (hb : BackendBounded B K H W)
    (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n)
    (hp : ∀ p ∈ ps, VecSmall H p) (hk : k ≤ K) (hr : VecSmall H r)
    (hc : CacheSmall K H cs) :
    (memoCost B ps k r cs).work ≤
      (4 * W + 8) * eventWeight (memoCost B ps k r cs).events := by
  induction k generalizing r cs with
  | zero =>
    have hl := lookupCost_work B K H W hb cs (0, r) hc ⟨hk, hr⟩
    rw [← lookupCost_weight] at hl
    have hi := insertCost_work B K H W hb cs (0, r)
      (if (B.zero r).1 then some [] else none) hc ⟨hk, hr⟩
    have hz := hb.zero r hr
    simp only [memoCost]
    split <;> simp only [eventWeight, Counts.add, Nat.zero_add]
    · simp only [eventWeight] at hl
      nlinarith
    · have hw := insertCost_weight B cs (0, r)
        (if (B.zero r).1 then some [] else none)
      simp only [eventWeight] at hl hw
      nlinarith
  | succ k ih =>
    have hs := scanCost_work B K H W hb (memoCost B ps k)
      (fun r cs hr hc => memoCost_small B K H ps k r cs (by omega) hr hc)
      (fun r cs hr hc => ih r cs (by omega) hr hc) r ps cs hp hr hc
    have hc' := scanCost_small B K H (memoCost B ps k)
      (fun r cs hr hc => memoCost_small B K H ps k r cs (by omega) hr hc)
      r ps cs hr hc
    have hl := lookupCost_work B K H W hb cs (k + 1, r) hc ⟨hk, hr⟩
    rw [← lookupCost_weight] at hl
    have hi := insertCost_work B K H W hb
      (scanCost B (memoCost B ps k) r ps cs).value.2 (k + 1, r)
      (scanCost B (memoCost B ps k) r ps cs).value.1 hc' ⟨hk, hr⟩
    have hw := insertCost_weight B (scanCost B (memoCost B ps k) r ps cs).value.2
      (k + 1, r) (scanCost B (memoCost B ps k) r ps cs).value.1
    simp only [memoCost]
    split <;> simp only [eventWeight, Counts.add, Nat.zero_add]
    · simp only [eventWeight] at hl
      nlinarith
    · simp only [eventWeight] at hl hw hs
      nlinarith

open TreeFlowExistence TreeBudgetVectorCandidates TreeBudgetVectorMemoIntegration
open TreeBudgetPatterns TreeBudgetMemoBounds

theorem candidates_small (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    ∀ p ∈ candidatesV R H A AT, VecSmall H p := by
  intro p hp i
  have hm : decode p ∈ TreeBudgetFiniteSearch.candidates R (decode H) s T := by
    rw [← map_decode_candidatesV R H A AT s T D hD hA hAT]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hv := (TreeBudgetFiniteSearch.mem_candidates ..).mp hm
  by_cases hi : i = R.root
  · subst i
    change decode p R.root ≤ decode H R.root
    rw [hv.1]
    exact Nat.zero_le _
  · exact hv.2.1 i hi

/-- Search entry after preprocessing and candidate generation. Its `work`
does not yet include those phases or output serialization. -/
def initialCost (B : Backend n) (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) : Run (AnswerV n × CacheV n) :=
  let H0 := TreeBudgetVector.normalize R H
  memoCost B (candidatesV R H0 A AT) (rootCount R (decode H0)) H0 []

theorem initialCost_observe (B : Backend n) (R : RootedTree (Fin n))
    (H : Vector ℕ n) (A : Vector ℤ n) (AT : ℤ) :
    observe (initialCost B R H A AT) =
      initialRowsStatV R H A AT
        (rootCount R (TreeBudgetPatterns.normalize R (decode H))) := by
  simp only [initialCost, initialRowsStatV, memoRowsStatV, memoCost_observe,
    decode_normalize]

theorem eventWeight_le_cube {out : Measured (AnswerV n × CacheV n)} {S : ℕ}
    (h : EventBoundsV out S) : eventWeight out.2 ≤ 7 * (S + 1) ^ 3 := by
  have hi : out.2.insertionScans ≤ S ^ 2 := by
    have hdiv := Nat.div_le_self (S * (S - 1)) 2
    have hmul := Nat.mul_le_mul_left S (Nat.sub_le S 1)
    have hh := h.insertionScans
    nlinarith
  have hc := h.calls
  have he := h.expansions
  have hq := h.candidates
  have hl := h.lookupComparisons
  simp only [eventWeight]
  nlinarith [Nat.zero_le (S ^ 3)]

theorem initialCost_work (B : Backend n) (R : RootedTree (Fin n))
    (H : Vector ℕ n) (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (W : ℕ)
    (hb : BackendBounded B
      (rootCount R (decode (TreeBudgetVector.normalize R H)))
      (TreeBudgetVector.normalize R H) W) :
    (initialCost B R H A AT).work ≤
      (4 * W + 8) * 7 *
        (stateBound R (TreeBudgetPatterns.normalize R (decode H)) + 1) ^ 3 := by
  have hw := memoCost_work B _ _ W hb
    (candidatesV R (TreeBudgetVector.normalize R H) A AT)
    (rootCount R (decode (TreeBudgetVector.normalize R H)))
    (TreeBudgetVector.normalize R H) []
    (candidates_small R _ A AT s T D hD hA hAT) le_rfl
    (fun _ => le_rfl) (by intro e he; simp at he)
  have he := congrArg Prod.snd (initialCost_observe B R H A AT)
  change (initialCost B R H A AT).events = _ at he
  have hc := eventWeight_le_cube
    (initial_eventBoundsV_stateBound R H A AT s T D hD hA hAT)
  rw [← he] at hc
  exact hw.trans (by simpa only [initialCost, Nat.mul_assoc] using
    Nat.mul_le_mul_left (4 * W + 8) hc)

end UAVProof.TreeBudgetCostedSearchBounds
