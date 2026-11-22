import LeanCompletion.UAV.TreeBudgetVerifierSetup

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000

theorem prep_update (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : Fin 13) :
    Function.update (if j.val=8 ∨ j.val=9 then
      Function.update (prepBank s A AT j.val) (prepPort j).src []
    else prepBank s A AT j.val) (prepPort j).dst (valueAt s A AT j) =
    prepBank s A AT (j.val+1) := by
  funext k
  rcases k with k|((k|k)|((k|k)|u))
  · fin_cases j <;> rfl
  · rcases k with ((i|u)|(c|i))|a
    · fin_cases i <;> fin_cases j <;> rfl
    · cases u; fin_cases j <;> rfl
    · fin_cases j <;> rfl
    · fin_cases j <;> fin_cases i <;> rfl
    · cases a <;> fin_cases j <;> rfl
  · rcases k with c|a
    · fin_cases j <;> rfl
    · cases a <;> fin_cases j <;> rfl
  · fin_cases k <;> fin_cases j <;> rfl
  · fin_cases k <;> fin_cases j <;> rfl
  · cases u; fin_cases j <;> rfl

def prep_round (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : Fin 13) :
    TreeBudgetRegisterTM2.Run setup
      (TreeBudgetRegisterTM2.cfg (prepPC j.val) (prepBank s A AT j.val))
      (TreeBudgetRegisterTM2.cfg (prepPC (j.val+1)) (prepBank s A AT (j.val+1)))
      (3*(valueAt s A AT j).length+3) := by
  let p := prepPort j
  let b := prepBank s A AT j.val
  let v := valueAt s A AT j
  have src := prep_source s A AT j
  have dst := prep_dest s A AT j
  have hsc : b p.scratch=[] := by
    change prepBank s A AT j.val (prepPort j).scratch=[]
    rw [prep_port_scratch]; rfl
  have upd := prep_update s A AT j
  by_cases h : j.val=8 ∨ j.val=9
  · have hi : setup (prepPC j.val)=.read p (prepPC (j.val+1)) := by
      rcases h with h|h
      · have hj : j=8 := Fin.ext h
        subst j; rfl
      · have hj : j=9 := Fin.ext h
        subst j; rfl
    simp only [if_pos h] at src upd
    have run := TreeBudgetRegisterTM2.read_run setup _ _ p hi b v [] (by simpa only [List.append_nil] using src) hsc dst
    rw [upd] at run
    exact run
  · have hi : setup (prepPC j.val)=.copy p false (prepPC (j.val+1)) := by
      fin_cases j <;> first | rfl | (exfalso; exact h (by decide))
    simp only [if_neg h] at src upd
    have run := TreeBudgetRegisterTM2.copy_run setup _ _ p false hi b hsc
    change b p.src=v at src
    change b p.dst=[] at dst
    simp only [Bool.false_eq_true,ite_false,src,dst,List.append_nil] at run
    change Function.update b p.dst v=_ at upd
    rw [upd] at run
    exact weaken run (by change 2*v.length+3≤3*v.length+3; omega)

/-- Each bridge copy and each budget payload read is charged in the enclosing run. -/
def prep_suffix (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ)
    (j left B : ℕ) (hj : j+left=13) (hb : ∀ i, (valueAt s A AT i).length≤B) :
    TreeBudgetRegisterTM2.Run setup
      (TreeBudgetRegisterTM2.cfg (prepPC j) (prepBank s A AT j))
      (TreeBudgetRegisterTM2.stopped (prepBank s A AT 13)) (left*(3*B+3)+1) := by
  induction left generalizing j with
  | zero =>
    have h : j=13 := by omega
    subst j
    simpa only [Nat.zero_mul,Nat.zero_add] using
      TreeBudgetRegisterTM2.halt_run setup .done rfl (prepBank s A AT 13)
  | succ left ih =>
    let i : Fin 13 := ⟨j,by omega⟩
    have a := prep_round s A AT i
    have b := ih (j+1) (by omega)
    have run := TreeBudgetRegisterTM2.seq setup a b
    have hv := hb i
    apply weaken run
    change 3*(valueAt s A AT i).length+3+(left*(3*B+3)+1) ≤ (left+1)*(3*B+3)+1
    rw [Nat.add_mul]
    omega

end UAVProof.A4Verifier
