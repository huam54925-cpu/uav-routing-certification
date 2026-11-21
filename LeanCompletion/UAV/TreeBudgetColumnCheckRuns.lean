import LeanCompletion.UAV.TreeBudgetColumnCheckTM2

namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def copyData (l next : PC) (p : Ports K) (h : code l=.copy p false next)
    (d : Data) (ht : store d p.scratch=[]) :
    Run (cfg l d) (cfg next (put d p.dst (store d p.src++store d p.dst)))
      (2*(store d p.src).length+3) := by
  simpa only [cfg,store_put,Bool.false_eq_true,ite_false] using
    TreeBudgetSemanticRegisterTM2.copy_run code l next p false h (store d) ht

def clearData (l next : PC) (p : Ports K) (h : code l=.clear p next)
    (d : Data) (ht : store d p.scratch=[]) :
    Run (cfg l d) (cfg next (put d p.src [])) ((store d p.src).length+2) := by
  simpa only [cfg,store_put] using TreeBudgetSemanticRegisterTM2.clear_run code l next p h (store d) ht

def readData (l next : PC) (p : Ports K) (h : code l=.read p next)
    (d : Data) (u t : Bits) (hs : store d p.src=word u++t)
    (ht : store d p.scratch=[]) (hd : store d p.dst=[]) :
    Run (cfg l d) (cfg next (put (put d p.src t) p.dst u)) (3*u.length+3) := by
  simpa only [cfg,store_put] using TreeBudgetSemanticRegisterTM2.read_run code l next p h (store d) u t hs ht hd

def testData (l empty more : PC) (src : K) (h : code l=.test src empty more) (d : Data) :
    Run (cfg l d) (cfg (if (store d src).isEmpty then empty else more) d) 1 :=
  TreeBudgetSemanticRegisterTM2.test_run code l empty more src h (store d)

def incData (l next : PC) (p : Ports K) (h : code l=.inc p next)
    (d : Data) (ht : store d p.scratch=[]) :
    Run (cfg l d) (cfg next (put d p.src (TreeBudgetStackRoutine.increment (store d p.src))))
      (2*(store d p.src).length+3) := by
  simpa only [cfg,store_put] using TreeBudgetSemanticRegisterTM2.inc_run code l next p h (store d) ht

def weightedData (d : Data) (ha : d.reg .a=[]) (hb : d.reg .b=[]) :
    Run (cfg .clearRow d)
      (cfg .sumB (put (put (put d (wr .count) []) (wr .coord) []) (wr .acc)
        (TreeBudgetWeightedTM2.weighted (d.reg .count) (d.reg .coord) (d.reg .acc))))
      (16*((d.reg .count).length+(d.reg .coord).length+(d.reg .acc).length+1)^2+3) := by
  have h₀ : bank mw (store d)
      (TreeBudgetWeightedTM2.cfg 0 false (d.reg .count) (d.reg .coord) (d.reg .acc) [] [] (d.reg .ctx)).stk=store d := by
    funext k; cases k with
    | inl c => rfl
    | inr r => cases r <;> simp [bank,mw,store,TreeBudgetWeightedTM2.cfg,ha,hb]
  have h₁ : bank mw (store d)
      (TreeBudgetWeightedTM2.stopped
        (TreeBudgetWeightedTM2.weighted (d.reg .count) (d.reg .coord) (d.reg .acc)) (d.reg .ctx)).stk=
      store (put (put (put d (wr .count) []) (wr .coord) []) (wr .acc)
        (TreeBudgetWeightedTM2.weighted (d.reg .count) (d.reg .coord) (d.reg .acc))) := by
    funext k; cases k with
    | inl c => rfl
    | inr r => cases r <;> simp [bank,mw,store,put,TreeBudgetWeightedTM2.stopped,
        TreeBudgetWeightedTM2.cfg,Function.update_apply,ha,hb]
  have run := TreeBudgetSemanticRegisterTM2.weighted_run code .clearRow .sumB mw rfl (store d)
    (d.reg .count) (d.reg .coord) (d.reg .acc) (d.reg .ctx)
  rw [h₀,h₁] at run
  exact run

def leData (l yes no : PC) (h : code l=.le cw yes no) (d : Data)
    (hc : d.reg .c=[]) (hd : d.reg .d=[]) :
    Run (cfg l d)
      (cfg (if value (d.reg .a)≤value (d.reg .b) then yes else no)
        (put (put d (wr .a) []) (wr .b) []))
      ((d.reg .a).length+(d.reg .b).length+3) := by
  have h₀ : bank cw (store d) (TreeBudgetLeWordsTM2.cfg none true (d.reg .a) (d.reg .b)).stk=store d := by
    funext k; cases k with
    | inl c => rfl
    | inr r => cases r <;> simp [bank,cw,store,TreeBudgetLeWordsTM2.cfg,
        TreeBudgetAddWordsTM2.tapes,hc,hd]
  have h₁ : bank cw (store d) (TreeBudgetAddWordsTM2.tapes [] [] [] [])=
      store (put (put d (wr .a) []) (wr .b) []) := by
    funext k; cases k with
    | inl c => rfl
    | inr r => cases r <;> simp [bank,cw,store,put,TreeBudgetAddWordsTM2.tapes,
        Function.update_apply,hc,hd]
  have run := TreeBudgetSemanticRegisterTM2.le_run code l yes no cw h (store d) (d.reg .a) (d.reg .b)
  rw [h₀,h₁] at run
  exact run

def lookupData (d : Data) (out : Bits) (n : ℕ)
    (hc : ∀ c, d.child c=[]) (hs : d.reg .scratch=[]) (ho : d.reg .coord=[])
    (sub : A4NaturalLookup.Run (A4NaturalLookup.start (d.reg .row) (d.reg .index))
      (A4NaturalLookup.stopped (d.reg .row) (d.reg .index) out) n) :
    Run (cfg .update d) (cfg .clearRow (put d (wr .coord) out)) (n+2) := by
  have h₀ : bank lw (store d) (A4NaturalLookup.start (d.reg .row) (d.reg .index)).stk=store d := by
    funext k; rcases k with (i|b)|r
    · fin_cases i <;> simp [bank,lw,store,A4NaturalLookup.start,A4NaturalLookup.store,hc]
    · cases b <;> simp [bank,lw,store,A4NaturalLookup.start,A4NaturalLookup.store,hc]
    · cases r <;> simp [bank,lw,store,A4NaturalLookup.start,A4NaturalLookup.store,hs,ho]
  have h₁ : bank lw (store d) (A4NaturalLookup.stopped (d.reg .row) (d.reg .index) out).stk=
      store (put d (wr .coord) out) := by
    funext k; rcases k with (i|b)|r
    · fin_cases i <;> simp [bank,lw,store,put,A4NaturalLookup.stopped,A4NaturalLookup.store,hc]
    · cases b <;> simp [bank,lw,store,put,A4NaturalLookup.stopped,A4NaturalLookup.store,hc]
    · cases r <;> simp [bank,lw,store,put,A4NaturalLookup.stopped,A4NaturalLookup.store,
        Function.update_apply,hs]
  have run := TreeBudgetSemanticRegisterTM2.lookup_run code .update .clearRow lw rfl (store d) _ _ out n sub
  rw [h₀,h₁] at run
  exact run

def entryData (d : Data) (e : RawEntry) (tail : Bits)
    (hc : ∀ c, d.child c=[]) (hr : d.reg .row=[]) (hm : d.reg .count=[])
    (hp : parseEntry (d.reg .cursor)=some (e,tail)) :
    Run (cfg .lookup d)
      (cfg .update (put (put (put d (wr .cursor) tail) (wr .row) (e.2.flatMap encodeNat))
        (wr .count) e.1.bits)) (24*((d.reg .cursor).length+1)^2+2) := by
  have h₀ : bank ew (store d) (TreeBudgetEntryTM2.start (d.reg .cursor) (d.reg .ctx)).stk=store d := by
    funext k; rcases k with (i|b)|r
    · fin_cases i <;> simp [bank,ew,store,TreeBudgetEntryTM2.start,TreeBudgetEntryTM2.base,
        TreeBudgetTM2Call.banks,TreeBudgetFrameRoutineTM2.cfg,TreeBudgetFrameRoutineTM2.tapes,
        TreeBudgetEntryTM2.ports,hc]
    · cases b <;> rfl
    · cases r <;> simp [bank,ew,store,TreeBudgetEntryTM2.start,TreeBudgetEntryTM2.base,
        TreeBudgetTM2Call.banks,TreeBudgetFrameRoutineTM2.cfg,TreeBudgetFrameRoutineTM2.tapes,
        TreeBudgetEntryTM2.ports,hr,hm]
  have h₁ : bank ew (store d) (TreeBudgetEntryTM2.returned e tail (d.reg .ctx)).stk=
      store (put (put (put d (wr .cursor) tail) (wr .row) (e.2.flatMap encodeNat)) (wr .count) e.1.bits) := by
    funext k; rcases k with (i|b)|r
    · fin_cases i <;> simp [bank,ew,store,put,TreeBudgetEntryTM2.returned,
        TreeBudgetCountedNatsTM2.returned,TreeBudgetTM2Call.banks,TreeBudgetListCleanup.tapes,hc]
    · cases b <;> rfl
    · cases r <;> simp [bank,ew,store,put,TreeBudgetEntryTM2.returned,
        TreeBudgetCountedNatsTM2.returned,TreeBudgetTM2Call.banks,TreeBudgetListCleanup.tapes,
        Function.update_apply]
  have run := TreeBudgetSemanticRegisterTM2.entry_run code .lookup .update ew rfl (store d)
    (d.reg .cursor) (d.reg .ctx) tail e hp
  rw [h₀,h₁] at run
  exact run

end UAVProof.A4ColumnCheck
