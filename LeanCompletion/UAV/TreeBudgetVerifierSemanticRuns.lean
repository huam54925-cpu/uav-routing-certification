import LeanCompletion.UAV.TreeBudgetVerifierFields
import LeanCompletion.UAV.TreeBudgetRowsCheckTotal
import LeanCompletion.UAV.TreeBudgetColumnCheckSpec
import LeanCompletion.UAV.TreeBudgetScaledWireBounds

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSparseVerifier TreeBudgetSparseCodec TreeBudgetCertificate TreeBudgetVectorChecker

set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev feesOf (I : Instance) := scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator
abbrev budgetOf (I : Instance) := scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator
abbrev posOf (I : Instance) := (feesOf I).map TreeBudgetSignedTableTM2.pos
abbrev negOf (I : Instance) := (feesOf I).map TreeBudgetSignedTableTM2.neg

def fieldBound (N : ℕ) := 4*(N+1)^2
def recordsBound (N : ℕ) := (N+1)*(A4RowsCheck.rowTimeBound (fieldBound N) N+72*(N+1)^2)
def columnsBound (N : ℕ) := 16384*(2*N+1)^4
def prepBound (N : ℕ) := 5*(2*fieldBound N)+13*(3*fieldBound N+3)+19

theorem fieldBound_ge (N : ℕ) : 4*(N+1)≤fieldBound N := by
  unfold fieldBound
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)

theorem preparation_bounds (x y : Bits) (s : A4FeeScaling.K → Bits)
    (I : Instance) (C : Certificate (Fin I.data.n)) (hi : parseInstance x=some I)
    (hc : decodeCertificate I.data.n y=some C) (hs : SavedFields s I C)
    (N : ℕ) (hN : x.length+y.length≤N) :
    ∀ i, (valueAt s (feesOf I).toList (budgetOf I) i).length≤fieldBound N := by
  obtain ⟨P,H,R,M⟩ := instance_wire_bounds x I hi
  obtain ⟨E,K⟩ := certificate_wire_bounds _ y C hc
  have hlin := fieldBound_ge N
  have hg : 4*(x.length+1)^2≤fieldBound N :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hsplit := A4ScaledWireBounds.split_fees_wire_length x I hi
  have hbudget := A4ScaledWireBounds.split_budget_width x I hi
  intro i
  fin_cases i <;> simp only [valueAt,hs.parents,hs.demands,hs.root,hs.routes,hs.body,hs.marks,
    List.length_replicate,feesOf,budgetOf] <;> omega

def rows_run (x y : Bits) (s : A4FeeScaling.K → Bits)
    (I : Instance) (C : Certificate (Fin I.data.n)) (hi : parseInstance x=some I)
    (hc : decodeCertificate I.data.n y=some C) (hs : SavedFields s I C)
    (N : ℕ) (hN : x.length+y.length≤N) :
    let d := rowInputs s (feesOf I).toList (budgetOf I)
    A4RowsCheck.Run (A4RowsCheck.start d)
      (A4RowsCheck.outcome d (A4RowsCheckSpec.rowPredicate I) (toRaw C) []) (recordsBound N) := by
  intro d
  have bounds := preparation_bounds x y s I C hi hc hs N hN
  have hp := bounds 0
  have hh := bounds 1
  have hr := bounds 2
  have ha := bounds 6
  have hb := bounds 7
  have ht := bounds 8
  have hu := bounds 9
  simp only [valueAt,hs.parents,hs.demands,hs.root] at hp hh hr
  obtain ⟨hbody,hk⟩ := certificate_wire_bounds _ y C hc
  have hm := (instance_wire_bounds x I hi).2.2.2
  have hsign : ∀ v : Fin I.data.n, ((posOf I)[v]:ℤ)-((negOf I)[v]:ℤ)=(feesOf I)[v] := by
    intro v
    have h (a : ℤ) : (TreeBudgetSignedTableTM2.pos a:ℤ)-(TreeBudgetSignedTableTM2.neg a:ℤ)=a := by
      cases a <;> simp [TreeBudgetSignedTableTM2.pos,TreeBudgetSignedTableTM2.neg] <;> omega
    simpa using h ((feesOf I)[v])
  have run := A4RowsCheck.records_from_start_unconditional I (posOf I) (negOf I)
    d (toRaw C) [] [] (fieldBound N) N hsign hp hh
    (by simpa [valueAt,posOf,Vector.toList_map,TreeBudgetSignedTableTM2.positive] using ha)
    (by simpa [valueAt,negOf,Vector.toList_map,TreeBudgetSignedTableTM2.negative] using hb) hr
    (by simpa only [valueAt] using ht) (by simpa only [valueAt] using hu)
    (by simp [d,rowInputs,hs.parents,hs.demands,hs.root,posOf,negOf,budgetOf,Vector.toList_map,
      TreeBudgetSignedTableTM2.positive,TreeBudgetSignedTableTM2.negative])
    hs.body (by rw [toRaw_length]; exact hs.marks)
    (by change (s bodySource).length≤N; rw [hs.body]; omega)
    (by change (s mSource).length≤N; rw [hs.routes]; omega)
    (toRaw_sized C)
  apply weaken run
  unfold recordsBound
  rw [toRaw_length]
  exact Nat.mul_le_mul_right _ (by omega)

def columns_run (x y : Bits) (s : A4FeeScaling.K → Bits)
    (I : Instance) (C : Certificate (Fin I.data.n)) (hi : parseInstance x=some I)
    (hc : decodeCertificate I.data.n y=some C) (hs : SavedFields s I C)
    (N : ℕ) (hN : x.length+y.length≤N) :
    let d := columnInputs s
    A4ColumnCheck.Run (A4ColumnCheck.start d)
      (A4ColumnCheck.output d I.data.parents.root.val 0 (toRaw C) I.data.H.toList)
      (columnsBound N) := by
  intro d
  have a := A4ColumnCheck.check_run d I.data.parents.root.val (toRaw C) I.data.H.toList
    hs.body hs.root hs.demands (by
      intro e he
      rw [Vector.length_toList]
      exact toRaw_sized C e he)
  obtain ⟨_,hh,hr,_⟩ := instance_wire_bounds x I hi
  have hc' := (certificate_wire_bounds _ y C hc).1
  apply weaken a
  unfold columnsBound
  apply Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 4)
  change (s bodySource).length+(s hSource).length+(s rSource).length+1≤_
  rw [hs.body,hs.demands,hs.root]
  omega

end UAVProof.A4Verifier
