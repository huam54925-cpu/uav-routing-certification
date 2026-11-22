import LeanCompletion.UAV.TreeBudgetVerifierSetupRuns
import LeanCompletion.UAV.TreeBudgetVerifierSemanticRuns
import LeanCompletion.UAV.TreeBudgetStandardOutputTotal

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSparseVerifier TreeBudgetSparseCodec TreeBudgetSparseNPBridge TreeBudgetCertificate
open TreeBudgetVectorChecker

set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def limit (N : ℕ) :=
  A4FeeScaling.Entry.totalBound N+prepBound N+recordsBound N+columnsBound N+2

private def blank (s : A4FeeScaling.K → Bits) : K → Bits :=
  store s (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => [])

private theorem scaled_bank (s : A4FeeScaling.K → Bits) :
    bank sw (fun _ => []) s=blank s := by
  funext k
  rcases k with k|((r|c)|((f|b)|u)) <;> rfl

private theorem initial_eq (w : Bits) :
    TreeBudgetStandardOutputTM2.initial machine.k₀ machine.main w =
      embed sw L.scaled .scaledReturn (fun _ => []) (initList A4FeeScaling.Entry.machine w) := by
  unfold TreeBudgetStandardOutputTM2.initial initList embed machine
  simp only [scaled_bank]
  congr 1
  funext k
  cases k with
  | inl k =>
    simp only [blank,store]
    by_cases h : k=A4FeeScaling.Entry.machine.k₀
    · have h' : (Sum.inl k : K)=sk A4FeeScaling.Entry.machine.k₀ := congrArg sk h
      rw [if_pos h']
      split
      · rfl
      · contradiction
    · have h' : (Sum.inl k : K)≠sk A4FeeScaling.Entry.machine.k₀ :=
        fun he => h (Sum.inl.inj he)
      rw [if_neg h']
      split
      · contradiction
      · rfl
  | inr k => rcases k with (r|c)|((f|b)|u) <;> rfl

private theorem row_bank (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) :
    bank rw (prepBank s A AT 13) (A4RowsCheck.start (rowInputs s A AT)).stk =
      prepBank s A AT 13 := by
  funext k
  rcases k with k|((r|c)|b) <;> rfl

private theorem column_bank (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ)
    (r : A4RowsCheck.Cfg) :
    bank cw (bank rw (prepBank s A AT 13) r.stk) (A4ColumnCheck.start (columnInputs s)).stk =
      bank rw (prepBank s A AT 13) r.stk := by
  funext k
  rcases k with k|((q|c)|b) <;> rfl

/-- The two semantic stages short-circuit on a failed row or count. -/
def after_ready (x y : Bits) (s : A4FeeScaling.K → Bits)
    (I : Instance) (C : Certificate (Fin I.data.n)) (hi : parseInstance x=some I)
    (hc : decodeCertificate I.data.n y=some C) (hs : SavedFields s I C)
    (N : ℕ) (hN : x.length+y.length≤N) :
    ∃ out, Nonempty (Run (ready s (feesOf I).toList (budgetOf I)) out
      (recordsBound N+columnsBound N+2)) ∧ out.l=none ∧ out.var.2=check I C := by
  let A := (feesOf I).toList
  let AT := budgetOf I
  let d := rowInputs s A AT
  let cs := columnInputs s
  let r := A4RowsCheck.outcome d (A4RowsCheckSpec.rowPredicate I) (toRaw C) []
  let c := A4ColumnCheck.output cs I.data.parents.root.val 0 (toRaw C) I.data.H.toList
  let base := prepBank s A AT 13
  have hr : r.l=none := A4RowsCheck.outcome_halted d (A4RowsCheckSpec.rowPredicate I) (toRaw C) []
  have hflag := A4RowsCheck.outcome_public_flag I C d (by
    change value (s mSource)=I.routes
    rw [hs.routes,value_bits])
  have ha : check I C=(r.var.2 && A4ColumnCheck.columns I.data.parents.root.val 0 (toRaw C) I.data.H.toList) := by
    rw [A4ColumnCheck.columns_public]
    change check I C=((A4RowsCheck.outcome d (A4RowsCheckSpec.rowPredicate I) (toRaw C) []).var.2 && _)
    rw [hflag]
    simp only [check,Bool.and_assoc]
  have head := call_run rw L.rows .rowsReturn base A4RowsCheck.program program
    (fun _ => rfl) (rows_run x y s I C hi hc hs N hN)
  have he : embed rw L.rows .rowsReturn base (A4RowsCheck.start d)=ready s A AT := by
    change (⟨some (.rows A4RowsCheck.machine.main),(none,true),
      bank rw base (A4RowsCheck.start d).stk⟩ : Cfg)=_
    rw [row_bank]
    rfl
  rw [he] at head
  let mid : Cfg := ⟨some .rowsReturn,r.var,bank rw base r.stk⟩
  have hm : embed rw L.rows .rowsReturn base r=mid := by simp [embed,mid,hr]
  rw [hm] at head
  cases hv : r.var.2 with
  | false =>
    let out : Cfg := ⟨none,(none,false),mid.stk⟩
    have step : machine.step mid=some out := by
      simp [machine,FinTM2.step,TM2.step,TM2.stepAux,program,mid,hv,reject,out]
    exact ⟨out,⟨weaken (seq head (once step)) (by omega)⟩,rfl,by simp [out,ha,hv]⟩
  | true =>
    let bs := bank rw base r.stk
    have tail := call_run cw L.columns .done bs
      (TreeBudgetSemanticRegisterTM2.program A4ColumnCheck.code) program (fun _ => rfl)
      (columns_run x y s I C hi hc hs N hN)
    have step : machine.step mid=some (embed cw L.columns .done bs (A4ColumnCheck.start cs)) := by
      simp only [machine,FinTM2.step,TM2.step,mid,program,TM2.stepAux,hv,
        TreeBudgetStackRoutine.jump]
      change some (⟨some (.columns A4ColumnCheck.machine.main),(none,true),bs⟩ : Cfg)=_
      change _=some (⟨some (.columns A4ColumnCheck.machine.main),(none,true),
        bank cw bs (A4ColumnCheck.start cs).stk⟩ : Cfg)
      rw [column_bank]
    have layout := A4ColumnCheck.output_layout cs I.data.parents.root.val 0 (toRaw C) I.data.H.toList
    let out : Cfg := ⟨none,c.var,bank cw bs c.stk⟩
    have hc_halt : c.l=none := layout.1
    have last : machine.step (embed cw L.columns .done bs c)=some out := by
      simp only [machine,FinTM2.step,TM2.step,embed,hc_halt,Option.elim_none,program,TM2.stepAux,out]
    refine ⟨out,⟨weaken (seq (seq (seq head (once step)) tail) (once last)) (by omega)⟩,rfl,?_⟩
    change c.var.2=check I C
    rw [ha,hv,Bool.true_and]
    exact layout.2.1

theorem executes (x y : Bits) :
    ∃ out, Nonempty (Run
      (TreeBudgetStandardOutputTM2.initial machine.k₀ machine.main (pairWire (x,y))) out
      (limit (pairWire (x,y)).length)) ∧ out.l=none ∧ out.var.2=verify x y := by
  let N := (pairWire (x,y)).length
  change ∃ out, Nonempty (Run _ out (limit N)) ∧ out.l=none ∧ out.var.2=verify x y
  have hN : x.length+y.length≤N := by simp only [N,pairWire_length]; omega
  obtain ⟨pre,⟨run⟩,hl,hv,hs,hscaled⟩ := A4FeeScaling.Entry.scaled_from_init x y
  have base := call_run sw L.scaled .scaledReturn (fun _ => [])
    A4FeeScaling.Entry.program program (fun _ => rfl) run
  rw [← initial_eq] at base
  let mid : Cfg := ⟨some .scaledReturn,pre.var,blank pre.stk⟩
  have hmid : embed sw L.scaled .scaledReturn (fun _ => []) pre=mid := by
    simp [embed,hl,scaled_bank,mid]
  rw [hmid] at base
  have hbase := Nat.mul_le_mul_left 131072 (Nat.pow_le_pow_left (show x.length+y.length+2≤N+2 by omega) 4)
  change A4FeeScaling.Entry.totalBound (x.length+y.length)≤A4FeeScaling.Entry.totalBound N at hbase
  cases hp : A4PairedParser.accepted x y with
  | false =>
    have hf : pre.var.2=false := hv.trans hp
    have hverify : verify x y=false := by
      cases hi : parseInstance x with
      | none => simp [verify,hi]
      | some I =>
        cases hc : decodeCertificate I.data.n y with
        | none => simp [verify,hi,checkWire,hc]
        | some C => simp [A4PairedParser.accepted,hi,hc] at hp
    let out : Cfg := ⟨none,(none,false),mid.stk⟩
    have step : machine.step mid=some out := by
      simp [machine,FinTM2.step,TM2.step,TM2.stepAux,program,mid,hf,reject,out]
    exact ⟨out,⟨weaken (seq base (once step)) (by unfold limit; omega)⟩,rfl,hverify.symm⟩
  | true =>
    have hi' : (parseInstance x).isSome=true := by cases hi : parseInstance x <;> simp_all [A4PairedParser.accepted]
    obtain ⟨I,hi⟩ := Option.isSome_iff_exists.mp hi'
    have hc' : (decodeCertificate I.data.n y).isSome=true := by
      simpa only [A4PairedParser.accepted,hi,Option.any_some] using hp
    obtain ⟨C,hc⟩ := Option.isSome_iff_exists.mp hc'
    have saved := saved_fields x y pre I C hi hc hs
    have scaled := hscaled I hi hp
    have hf : pre.var.2=true := hv.trans hp
    have prep := from_scaled pre.stk (feesOf I).toList (budgetOf I) (fieldBound N) pre.var hf
      scaled.1 scaled.2 (preparation_bounds x y pre.stk I C hi hc saved N hN)
    have hprep : 5*(((feesOf I).toList.flatMap encodeInt).length+(encodeInt (budgetOf I)).length)+13*(3*fieldBound N+3)+19≤prepBound N := by
      have ha := (A4ScaledWireBounds.fees_wire_length x I hi).trans
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (show x.length+1≤N+1 by omega) 2))
      have hb := A4ScaledWireBounds.budget_wire_length x I hi
      have hh := fieldBound_ge N
      change ((feesOf I).toList.flatMap encodeInt).length≤4*(N+1)^2 at ha
      change (encodeInt (budgetOf I)).length≤4*x.length+4 at hb
      unfold fieldBound at hh
      unfold prepBound fieldBound
      omega
    have p := weaken prep hprep
    change Run mid _ _ at p
    obtain ⟨out,⟨tail⟩,ht,hb⟩ := after_ready x y pre.stk I C hi hc saved N hN
    refine ⟨out,⟨weaken (seq (seq base p) tail) (by unfold limit; omega)⟩,ht,?_⟩
    simpa [verify,hi,checkWire,hc] using hb

end UAVProof.A4Verifier
