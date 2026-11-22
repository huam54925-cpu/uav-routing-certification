import LeanCompletion.UAV.TreeBudgetRowCheckTime
import LeanCompletion.UAV.TreeBudgetRowsCheckLoop
import LeanCompletion.UAV.TreeBudgetRowsCheckSpec

/-! Unconditional all-records and total-multiplicity execution theorem for `A4RowsCheck`,
discharging the `rows` premise of `records_from_start` via `A4RowCheck.row_run_in_time`. -/
namespace UAVProof.A4RowsCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open TreeBudgetSparseVerifier TreeBudgetVectorChecker TreeBudgetCertificate

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def rowTimeBound (B W : ℕ) : ℕ := 8192*(B+W+1)^3

theorem encodeEntry_length_le_flatMap (e : RawEntry) (xs : RawCertificate) (he : e∈xs) :
    (encodeEntry e).length≤(xs.flatMap encodeEntry).length := by
  induction xs with
  | nil => simp at he
  | cons a xs ih =>
    simp only [List.mem_cons] at he
    simp only [List.flatMap_cons,List.length_append]
    rcases he with rfl | hmem
    · omega
    · have h := ih hmem
      omega

theorem rawRow_toList (n : ℕ) (e : RawEntry) (hlen : e.2.length=n) :
    (A4RowsCheckSpec.rawRow n e).toList=e.2 := by
  apply List.ext_getElem (by simp [A4RowsCheckSpec.rawRow,hlen])
  intro i hi₁ hi₂
  simp [A4RowsCheckSpec.rawRow,List.getElem?_eq_getElem hi₂]

def row_evalsToInTime (I : Instance) (Ap An : Vector ℕ I.data.n) (ctx suffix : Bits)
    (B W : ℕ)
    (ha : ∀ v : Fin I.data.n, (Ap[v]:ℤ)-(An[v]:ℤ)=
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)[v])
    (hP : ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat).length≤B)
    (hH : (I.data.H.toList.flatMap encodeNat).length≤B)
    (hAp : (Ap.toList.flatMap encodeNat).length≤B)
    (hAn : (An.toList.flatMap encodeNat).length≤B)
    (hroot : I.data.parents.root.val.bits.length≤B)
    (htp : (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator).toNat.bits.length≤B)
    (htn : (-(scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)).toNat.bits.length≤B)
    (e : RawEntry) (hlen : e.2.length=I.data.n)
    (heW : (e.2.flatMap encodeNat).length≤W) :
    let budget := scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator
    let base := A4RowCheck.store
      ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat)
      (I.data.H.toList.flatMap encodeNat) []
      (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
      I.data.parents.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix
    EvalsToInTime A4RowCheck.machine.step
      ⟨some A4RowCheck.machine.main,(none,true),
        Function.update base (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩
      (some ⟨none,(none,A4RowsCheckSpec.rowPredicate I e),
        Function.update base (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩)
      (rowTimeBound B W) := by
  intro budget base
  let p := A4RowsCheckSpec.rawRow I.data.n e
  have hp_list : p.toList=e.2 := rawRow_toList I.data.n e hlen
  have hupd : Function.update base (A4RowCheck.reg 2) (e.2.flatMap encodeNat)=
      A4RowCheck.store
        ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat)
        (I.data.H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat)
        (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        I.data.parents.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix := by
    rw [hp_list]
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have run := A4RowCheck.row_run_in_time I.data.parents I.data.H Ap An p
    (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
    budget ctx suffix B W ha hP hH hAp hAn hroot htp htn (by simpa only [hp_list] using heW)
  change EvalsToInTime A4RowCheck.machine.step
    ⟨some A4RowCheck.machine.main,(none,true),
      A4RowCheck.store ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat)
        (I.data.H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat)
        (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        I.data.parents.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix⟩
    (some ⟨none,(none,A4RowsCheckSpec.rowPredicate I e),
      A4RowCheck.store ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat)
        (I.data.H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat)
        (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        I.data.parents.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix⟩)
    (rowTimeBound B W) at run
  rw [← hupd] at run
  exact run

def records_from_start_unconditional
    (I : Instance) (Ap An : Vector ℕ I.data.n)
    (d : Data) (xs : RawCertificate) (ctx suffix : Bits) (B W : ℕ)
    (ha : ∀ v : Fin I.data.n, (Ap[v]:ℤ)-(An[v]:ℤ)=
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)[v])
    (hP : ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat).length≤B)
    (hH : (I.data.H.toList.flatMap encodeNat).length≤B)
    (hAp : (Ap.toList.flatMap encodeNat).length≤B)
    (hAn : (An.toList.flatMap encodeNat).length≤B)
    (hroot : I.data.parents.root.val.bits.length≤B)
    (htp : (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator).toNat.bits.length≤B)
    (htn : (-(scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)).toNat.bits.length≤B)
    (hsaved : d.rowSaved=A4RowCheck.store
      ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat)
      (I.data.H.toList.flatMap encodeNat) []
      (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
      I.data.parents.root.val.bits
      (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator).toNat.bits
      (-(scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)).toNat.bits
      ctx suffix)
    (hb : d.body=xs.flatMap encodeEntry)
    (hk : d.markers=List.replicate xs.length true)
    (hw : d.body.length≤W) (hm : d.routes.length≤W)
    (hrows_len : ∀ e∈xs, e.2.length=I.data.n) :
    Run (start d) (outcome d (A4RowsCheckSpec.rowPredicate I) xs [])
      ((xs.length+1)*(rowTimeBound B W+72*(W+1)^2)) := by
  refine records_from_start d (A4RowsCheckSpec.rowPredicate I) xs
    (rowTimeBound B W) W (by simp [hsaved,A4RowCheck.store,A4RowCheck.reg])
    hb hk hw hm ?_
  intro e he
  have heW : (e.2.flatMap encodeNat).length≤W := by
    have h1 := (entry_parts_width e).1
    have h2 := encodeEntry_length_le_flatMap e xs he
    rw [← hb] at h2
    omega
  rw [hsaved]
  exact row_evalsToInTime I Ap An ctx suffix B W ha hP hH hAp hAn hroot htp htn e
    (hrows_len e he) heW

theorem outcome_public_flag (I : Instance) (C : Certificate (Fin I.data.n))
    (d : Data) (hr : value d.routes=I.routes) :
    (outcome d (A4RowsCheckSpec.rowPredicate I) (toRaw C) []).var.2=
      ((List.finRange C.size).all (fun i =>
        (TreeBudgetCostedCandidates.rowCheck I.data.parents I.data.H
          (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
          (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)
          (Vector.ofFn (C.row i))).value) && decide ((List.ofFn C.count).sum=I.routes)) := by
  rw [outcome_flag,show value ([] : Bits)=0 from rfl,Nat.zero_add,hr]
  exact A4RowsCheckSpec.rows_counts_public I C

end UAVProof.A4RowsCheck
