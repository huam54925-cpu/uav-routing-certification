import LeanCompletion.UAV.TreeBudgetVerifierPrepRuns

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

private def empty : {α : Type} → α → Bits := fun _ => []
private def original (s : A4FeeScaling.K → Bits) := store s empty empty empty empty
private def signed (u : Bits) := TreeBudgetSignedTableTM2.store u [] [] [] [] [] []
private def loaded (s : A4FeeScaling.K → Bits) (u v : Bits) :=
  store s empty empty (signed u) (signed v)

private theorem load_fees (s : A4FeeScaling.K → Bits) (u : Bits) :
    Function.update (original s) (fk 0) u=loaded s u [] := by
  funext k
  rcases k with k|((r|c)|((f|b)|u'))
  all_goals try rfl
  all_goals first | (fin_cases f <;> rfl) | (fin_cases b <;> rfl)

private theorem load_budget (s : A4FeeScaling.K → Bits) (u v : Bits) :
    Function.update (loaded s u []) (bk 0) v=loaded s u v := by
  funext k
  rcases k with k|((r|c)|((f|b)|u'))
  all_goals try rfl
  fin_cases b <;> rfl

private def load_run (s : A4FeeScaling.K → Bits) (u v : Bits)
    (hu : s (A4FeeScaling.wr .fees)=u) (hv : s (A4FeeScaling.wr .budget)=v) :
    TreeBudgetRegisterTM2.Run setup
      (TreeBudgetRegisterTM2.cfg .fees (original s))
      (TreeBudgetRegisterTM2.stopped (loaded s u v))
      (2*u.length+2*v.length+7) := by
  let p : Ports K := ⟨sk (A4FeeScaling.wr .fees),scratch,fk 0,by decide,by decide,by decide⟩
  let q : Ports K := ⟨sk (A4FeeScaling.wr .budget),scratch,bk 0,by decide,by decide,by decide⟩
  have hpu : original s p.src=u := hu
  have hqv : loaded s u [] q.src=v := hv
  have hpd : original s p.dst=[] := rfl
  have hqd : loaded s u [] q.dst=[] := rfl
  have a := TreeBudgetRegisterTM2.copy_run setup .fees .budget p false rfl (original s) rfl
  have b := TreeBudgetRegisterTM2.copy_run setup .budget .done q false rfl (loaded s u []) rfl
  simp only [Bool.false_eq_true,ite_false,hpu,hpd,List.append_nil] at a
  simp only [Bool.false_eq_true,ite_false,hqv,hqd,List.append_nil] at b
  change TreeBudgetRegisterTM2.Run setup _ (TreeBudgetRegisterTM2.cfg .budget
    (Function.update (original s) (fk 0) u)) _ at a
  change TreeBudgetRegisterTM2.Run setup _ (TreeBudgetRegisterTM2.cfg .done
    (Function.update (loaded s u []) (bk 0) v)) _ at b
  rw [load_fees] at a
  rw [load_budget] at b
  have c := TreeBudgetRegisterTM2.halt_run setup .done rfl (loaded s u v)
  convert TreeBudgetRegisterTM2.seq setup (TreeBudgetRegisterTM2.seq setup a b) c using 1 <;> omega

private theorem fee_bank (s : A4FeeScaling.K → Bits) (r : K → Bits) (v : Bits)
    (h : r=loaded s [] v) (f : Fin 7 → Bits) :
    bank fw r f=store s empty empty f (signed v) := by
  subst r; funext k
  rcases k with k|((r|c)|((p|q)|u)) <;> rfl

private theorem budget_bank (s : A4FeeScaling.K → Bits) (f b : Fin 7 → Bits) :
    bank bw (store s empty empty f empty) b=store s empty empty f b := by
  funext k
  rcases k with k|((r|c)|((p|q)|u)) <;> rfl

private theorem empty_prep (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) :
    prepBank s A AT 0=store s empty empty
      (TreeBudgetSignedTableTM2.stopped (A.flatMap encodeInt)
        (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A) []).stk
      (TreeBudgetSignedTableTM2.stopped (encodeInt AT)
        (encodeNat AT.toNat) (encodeNat (-AT).toNat) []).stk := by
  funext k
  rcases k with k|((r|c)|((p|q)|u))
  · rfl
  · rcases r with ((i|u)|(c|i))|a
    · fin_cases i <;> rfl
    · cases u; rfl
    · rfl
    · fin_cases i <;> rfl
    · cases a <;> rfl
  · rcases c with c|a <;> first | rfl | (cases a <;> rfl)
  · rfl
  · rfl
  · rfl

def from_scaled (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (B : ℕ)
    (st : State) (hst : st.2=true)
    (hu : s (A4FeeScaling.wr .fees)=A.flatMap encodeInt)
    (hv : s (A4FeeScaling.wr .budget)=encodeInt AT)
    (hb : ∀ i, (valueAt s A AT i).length≤B) :
    Run ⟨some .scaledReturn,st,original s⟩ (ready s A AT)
      (5*((A.flatMap encodeInt).length+(encodeInt AT).length)+13*(3*B+3)+19) := by
  let u := A.flatMap encodeInt
  let v := encodeInt AT
  let f := (TreeBudgetSignedTableTM2.stopped u
    (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A) []).stk
  have step : machine.step (⟨some .scaledReturn,st,original s⟩ : Cfg)=
      some ⟨some (.load (.pc .fees)),(none,true),original s⟩ := by
    simp [machine,FinTM2.step,TM2.step,program,TM2.stepAux,hst,TreeBudgetStackRoutine.jump]
    rfl
  have a := call_run iw L.load (.splitFees .sign) empty
    (TreeBudgetRegisterTM2.program setup) program (fun _ => rfl) (load_run s u v hu hv)
  have b := call_run fw L.splitFees (.splitBudget .sign) (loaded s [] v)
    TreeBudgetSignedTableTM2.program program (fun _ => rfl) (TreeBudgetSignedTableTM2.split_run A [])
  have c := call_run bw L.splitBudget (.prepare (.pc .parents)) (store s empty empty f empty)
    TreeBudgetSignedTableTM2.program program (fun _ => rfl) (TreeBudgetSignedTableTM2.split_run [AT] [])
  have d := call_run iw L.prepare (.rows A4RowsCheck.machine.main) empty
    (TreeBudgetRegisterTM2.program setup) program (fun _ => rfl) (prep_suffix s A AT 0 13 B rfl hb)
  simp only [embed,TreeBudgetRegisterTM2.cfg,TreeBudgetRegisterTM2.stopped,
    Option.elim_some,Option.elim_none] at a d
  change Run _ ⟨some (.splitFees .sign),(none,true),loaded s u v⟩ _ at a
  change Run ⟨some (.splitFees .sign),(none,true),
    bank fw (loaded s [] v) (signed u)⟩
    ⟨some (.splitBudget .sign),(none,true),bank fw (loaded s [] v) f⟩ _ at b
  rw [fee_bank s _ v rfl,fee_bank s _ v rfl] at b
  rw [← show loaded s u v=store s empty empty (signed u) (signed v) by rfl] at b
  have cp := TreeBudgetSignedTableTM2.split_run [AT] []
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,TreeBudgetSignedTableTM2.positive,
    TreeBudgetSignedTableTM2.negative,List.map_cons,List.map_nil,
    TreeBudgetSignedTableTM2.pos,TreeBudgetSignedTableTM2.neg] at cp
  change TreeBudgetSignedTableTM2.Run (TreeBudgetSignedTableTM2.start v [])
    (TreeBudgetSignedTableTM2.stopped v (encodeNat AT.toNat) (encodeNat (-AT).toNat) [])
    (3*v.length+5) at cp
  have c := call_run bw L.splitBudget (.prepare (.pc .parents)) (store s empty empty f empty)
    TreeBudgetSignedTableTM2.program program (fun _ => rfl) cp
  change Run ⟨some (.splitBudget .sign),(none,true),
    bank bw (store s empty empty f empty) (signed v)⟩
    ⟨some (.prepare (.pc .parents)),(none,true),
      bank bw (store s empty empty f empty)
        (TreeBudgetSignedTableTM2.stopped v (encodeNat AT.toNat) (encodeNat (-AT).toNat) []).stk⟩ _ at c
  rw [budget_bank,budget_bank,← empty_prep s A AT] at c
  change Run ⟨some (.prepare (.pc .parents)),(none,true),prepBank s A AT 0⟩ (ready s A AT) _ at d
  apply weaken (seq (seq (seq (seq (once step) a) b) c) d)
  change 1+(2*u.length+2*v.length+7)+(3*u.length+5)+(3*v.length+5)+(13*(3*B+3)+1)≤_
  dsimp only [u,v]
  omega

end UAVProof.A4Verifier
