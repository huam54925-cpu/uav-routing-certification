import LeanCompletion.UAV.TreeBudgetNaturalLookupTM2

namespace UAVProof.A4NaturalLookup
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

theorem counted_layout (before : List ℕ) (tail : Bits) :
    TreeBudgetCountedNatsTM2.stopped (encodeNats before ++ tail) [] =
      {TreeBudgetNatListLoop.conf 17 tail (before.flatMap encodeNat) [] [] [] with l := none} := by
  have hb : before.length ≤ (before.flatMap encodeNat ++ tail).length := by
    rw [List.length_append, sum_size_encodeNat]
    omega
  have hm := parseMany_append encodeNat parseNat parseNat_append before tail
  have hl := TreeBudgetNatListLoop.loop_contract before.length
    (before.flatMap encodeNat ++ tail) [] []
  simp only [hm, List.reverse_nil, List.nil_append] at hl
  simp only [TreeBudgetCountedNatsTM2.stopped, TreeBudgetCountedNatsTM2.result,
    encodeNats, encodeList, List.append_assoc, parseNat_append, hb, ite_true, hl]
  rfl

def childStore (s f d : Bits) : Child → Bits
  | .inl k => match k.val with | 0 => s | 2 => f | _ => []
  | .inr b => if b then d else []

theorem lookup_layout (before after : List ℕ) (a : ℕ) :
    TreeBudgetParentLookupTM2.finish (encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat) [] =
      ⟨none,(none,true),childStore (after.flatMap encodeNat) (before.flatMap encodeNat) a.bits⟩ := by
  have he : encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat =
      encodeNats before ++ (encodeNat a ++ after.flatMap encodeNat) := by
    simp [encodeNats, encodeList, List.flatMap_append, List.append_assoc]
  rw [he]
  unfold TreeBudgetParentLookupTM2.finish
  rw [counted_layout]
  simp only [TreeBudgetNatListLoop.conf, cfg]
  change TreeBudgetParentLookupTM2.terminalField _ (encodeNat a ++ after.flatMap encodeNat) = _
  simp only [TreeBudgetParentLookupTM2.terminalField, TreeBudgetParentLookupTM2.field, parseNat_append, Option.isSome_some]
  congr 1
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr b => cases b <;> rfl

theorem store_update_src (t i s f d o v : Bits) :
    Function.update (store t i s f d o) src v = store t i v f d o := by
  funext k; rcases k with (k|b)|j
  · fin_cases k <;> simp [store,src,Function.update_apply]
  · cases b <;> rfl
  · fin_cases j <;> rfl
theorem store_update_front (t i s f d o v : Bits) :
    Function.update (store t i s f d o) front v = store t i s v d o := by
  funext k; rcases k with (k|b)|j
  · fin_cases k <;> simp [store,front,Function.update_apply]
  · cases b <;> rfl
  · fin_cases j <;> rfl
theorem store_update_digits (t i s f d o v : Bits) :
    Function.update (store t i s f d o) digits v = store t i s f v o := by
  funext k; rcases k with (k|b)|j
  · fin_cases k <;> rfl
  · cases b <;> simp [store,digits,Function.update_apply]
  · fin_cases j <;> rfl
theorem store_update_output (t i s f d o v : Bits) :
    Function.update (store t i s f d o) output v = store t i s f d v := by
  funext k; rcases k with (k|b)|j
  · fin_cases k <;> rfl
  · cases b <;> rfl
  · fin_cases j <;> simp [store,output,Function.update_apply]

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,scratch,$d,by decide,by decide,by decide⟩ : Ports K))

def prepare_run (t i : Bits) : TreeBudgetRegisterTM2.Run prep
    (TreeBudgetRegisterTM2.cfg 0 (store t i [] [] [] []))
    (TreeBudgetRegisterTM2.stopped (store t i (word i ++ t) [] [] [])) (2*t.length+2*i.length+7) := by
  have a := TreeBudgetRegisterTM2.copy_run prep 0 1 port(table,src) false rfl (store t i [] [] [] []) rfl
  have b := TreeBudgetRegisterTM2.copy_run prep 1 2 port(index,src) true rfl (store t i t [] [] []) rfl
  simp only [Bool.false_eq_true, ite_false, List.append_nil] at a
  change TreeBudgetRegisterTM2.Run prep _ (TreeBudgetRegisterTM2.cfg 1 (Function.update (store t i [] [] [] []) src (t++[]))) (2*t.length+3) at a
  simp only [List.append_nil] at a
  change TreeBudgetRegisterTM2.Run prep _ (TreeBudgetRegisterTM2.cfg 2 (Function.update (store t i t [] [] []) src (word i++t))) (2*i.length+3) at b
  rw [store_update_src] at a b
  have c := TreeBudgetRegisterTM2.halt_run prep 2 rfl (store t i (word i ++ t) [] [] [])
  convert TreeBudgetRegisterTM2.seq prep (TreeBudgetRegisterTM2.seq prep a b) c using 1 <;> omega

def cleanup_run (t i s f d : Bits) : TreeBudgetRegisterTM2.Run clean
    (TreeBudgetRegisterTM2.cfg 0 (store t i s f d []))
    (TreeBudgetRegisterTM2.stopped (store t i [] [] [] d)) (3*d.length+s.length+f.length+10) := by
  have a := TreeBudgetRegisterTM2.copy_run clean 0 1 port(digits,output) false rfl (store t i s f d []) rfl
  have b := TreeBudgetRegisterTM2.clear_run clean 1 2 port(src,output) rfl (store t i s f d d) rfl
  have c := TreeBudgetRegisterTM2.clear_run clean 2 3 port(front,output) rfl (store t i [] f d d) rfl
  have e := TreeBudgetRegisterTM2.clear_run clean 3 4 port(digits,output) rfl (store t i [] [] d d) rfl
  simp only [Bool.false_eq_true, ite_false, List.append_nil] at a
  change TreeBudgetRegisterTM2.Run clean _ (TreeBudgetRegisterTM2.cfg 1 (Function.update (store t i s f d []) output (d++[]))) (2*d.length+3) at a
  simp only [List.append_nil] at a
  change TreeBudgetRegisterTM2.Run clean _ (TreeBudgetRegisterTM2.cfg 2 (Function.update (store t i s f d d) src [])) (s.length+2) at b
  change TreeBudgetRegisterTM2.Run clean _ (TreeBudgetRegisterTM2.cfg 3 (Function.update (store t i [] f d d) front [])) (f.length+2) at c
  change TreeBudgetRegisterTM2.Run clean _ (TreeBudgetRegisterTM2.cfg 4 (Function.update (store t i [] [] d d) digits [])) (d.length+2) at e
  rw [store_update_output] at a
  rw [store_update_src] at b
  rw [store_update_front] at c
  rw [store_update_digits] at e
  have z := TreeBudgetRegisterTM2.halt_run clean 4 rfl (store t i [] [] [] d)
  convert TreeBudgetRegisterTM2.seq clean (TreeBudgetRegisterTM2.seq clean (TreeBudgetRegisterTM2.seq clean (TreeBudgetRegisterTM2.seq clean a b) c) e) z using 1 <;> omega

theorem identity_bank (base s : K → Bits) : bank iw base s=s := rfl

theorem child_bank (t i s f d : Bits) :
    bank cw (store t i [] [] [] []) (childStore s f d)=store t i s f d [] := by
  funext k; rcases k with (k|b)|j <;> rfl

theorem child_start (t i : Bits) :
    TreeBudgetParentLookupTM2.start (word i++t) [] =
      ⟨some TreeBudgetParentLookupTM2.machine.main,(none,true),childStore (word i++t) [] []⟩ := by
  unfold TreeBudgetParentLookupTM2.start TreeBudgetParentLookupTM2.liftCfg TreeBudgetTM2Call.embed
  congr 1
  funext k
  cases k with
  | inl j => fin_cases j <;> rfl
  | inr b => cases b <;> rfl

/-- Lookup preserves its table and canonical binary index, returns the exact
canonical payload, and empties every private work stack. -/
def lookup_run (before after : List ℕ) (a : ℕ) :
    Run (start ((before++a::after).flatMap encodeNat) before.length.bits)
      (stopped ((before++a::after).flatMap encodeNat) before.length.bits a.bits)
      (256*(((before++a::after).flatMap encodeNat).length + before.length.bits.length+1)^2) := by
  let t := (before++a::after).flatMap encodeNat
  let i := before.length.bits
  let s := encodeNat before.length++t
  have head := call_run iw L.prepare (.lookup TreeBudgetParentLookupTM2.machine.main)
    (fun _ => []) (TreeBudgetRegisterTM2.program prep) program (fun _ => rfl)
    (prepare_run t i)
  have middle := call_run cw L.lookup (.cleanup (.pc 0)) (store t i [] [] [] [])
    TreeBudgetParentLookupTM2.program program (fun _ => rfl)
    (TreeBudgetParentLookupTM2.lookup_run s [])
  have tail := call_run iw L.cleanup .done (fun _ => [])
    (TreeBudgetRegisterTM2.program clean) program (fun _ => rfl)
    (cleanup_run t i (after.flatMap encodeNat) (before.flatMap encodeNat) a.bits)
  rw [show s=encodeNat before.length++(before++a::after).flatMap encodeNat from rfl,
    lookup_layout] at middle
  change EvalsToInTime (TM2.step program)
    (embed cw L.lookup (.cleanup (.pc 0)) (store t i [] [] [] [])
      (TreeBudgetParentLookupTM2.start (word i++t) [])) _ _ at middle
  rw [child_start] at middle
  simp only [embed,TreeBudgetRegisterTM2.cfg,TreeBudgetRegisterTM2.stopped,
    Option.elim_some,Option.elim_none,identity_bank,child_bank] at head middle tail
  have last : machine.step ⟨some L.done,(none,true),store t i [] [] [] a.bits⟩ =
      some (stopped t i a.bits) := rfl
  have run := EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (EvalsToInTime.trans (TM2.step program) _ _ _ _ _ head middle) tail) (once last)
  apply weaken run
  have ht : t.length=(before.flatMap encodeNat).length+(2*a.bits.length+1)+
      (after.flatMap encodeNat).length := by
    simp [t,List.flatMap_append,encodeNat,word_length,Nat.add_assoc]
  have hs : s.length=2*i.length+1+t.length := by simp [s,i,encodeNat,word_length]
  have hsum : s.length+1≤2*(t.length+i.length+1) := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  have hpos : 1≤t.length+i.length+1 := by omega
  change 1+((3*a.bits.length+(after.flatMap encodeNat).length+(before.flatMap encodeNat).length+10)+
    (24*(s.length+1)^2+(2*t.length+2*i.length+7))) ≤
      256*(t.length+i.length+1)^2
  nlinarith

end UAVProof.A4NaturalLookup
