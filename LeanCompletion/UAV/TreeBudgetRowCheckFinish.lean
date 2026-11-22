import LeanCompletion.UAV.TreeBudgetRowCheckRuns

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def mass_left_run (s : K → Bits) (hs : s (reg 24)=[])
    (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    Execution (cfg .massLeft s) (cfg (if value (s (reg 22))≤1 then .oneLeft else bad) s) := by
  let m := s (reg 22)
  have first := copy_run instructions .massLeft .oneRight (operandPort 22 31 (by decide)) false rfl s hs
  have second := push_run instructions .oneRight .massLEone (reg 32) true rfl (set s 31 m)
  have third := compare_block .massLEone .oneLeft bad rfl (set (set s 31 m) 32 [true])
    (by simp [set,reg,h₃]) (by simp [set,reg,h₄])
  simp only [Bool.false_eq_true,ite_false,operandPort,h₁,List.append_nil] at first
  change Run instructions (cfg .massLeft s) (cfg .oneRight (set s 31 m)) (2*m.length+3) at first
  simp only [set,Function.update_of_ne (show reg 32≠reg 31 by decide),h₂] at second
  change Run instructions (cfg .oneRight (set s 31 m)) (cfg .massLEone (set (set s 31 m) 32 [true])) 1 at second
  simp only [set,Function.update_self,Function.update_of_ne (show reg 31≠reg 32 by decide)] at third
  have hcp := clear_pair s m [true] h₁ h₂
  simp only [set] at hcp
  rw [hcp] at third
  exact ⟨_,seq instructions (seq instructions first second) third⟩

def mass_right_run (s : K → Bits) (hs : s (reg 24)=[])
    (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    Execution (cfg .oneLeft s) (cfg (if 1≤value (s (reg 22)) then .budgetLeft else bad) s) := by
  let m := s (reg 22)
  have first := push_run instructions .oneLeft .massRight (reg 31) true rfl s
  have second := copy_run instructions .massRight .oneLEmass (operandPort 22 32 (by decide)) false rfl
    (set s 31 [true]) (by simp [operandPort,set,reg,hs])
  have third := compare_block .oneLEmass .budgetLeft bad rfl (set (set s 31 [true]) 32 m)
    (by simp [set,reg,h₃]) (by simp [set,reg,h₄])
  simp only [h₁] at first
  change Run instructions (cfg .oneLeft s) (cfg .massRight (set s 31 [true])) 1 at first
  simp only [operandPort,source,set,reg,Function.update_of_ne (by decide : reg 22≠reg 31),
    Function.update_of_ne (by decide : reg 32≠reg 31),Bool.false_eq_true,ite_false,h₂,
    List.append_nil] at second
  change Run instructions (cfg .massRight (set s 31 [true]))
    (cfg .oneLEmass (set (set s 31 [true]) 32 m)) (2*m.length+3) at second
  simp only [set,Function.update_self,Function.update_of_ne (show reg 31≠reg 32 by decide)] at third
  have hcp := clear_pair s [true] m h₁ h₂
  simp only [set] at hcp
  rw [hcp] at third
  exact ⟨_,seq instructions (seq instructions first second) third⟩

def final_test_run (base : K → Bits) (positive negative mass : Bits) :
    Execution (cfg .massLeft (ready base [] [] [] [] [] positive negative mass))
      (cfg (.cleanup (decide (value mass=1 ∧ value positive≤value negative)) 0)
        (ready base [] [] [] [] [] positive negative mass)) := by
  let s := ready base [] [] [] [] [] positive negative mass
  have left := mass_left_run s rfl rfl rfl rfl rfl
  have right := mass_right_run s rfl rfl rfl rfl rfl
  have budget := compare_saved .budgetLeft .budgetRight .budgetCompare good bad
    20 21 rfl rfl rfl s rfl rfl rfl rfl rfl
  have leftProp := left.property
  have rightProp := right.property
  have budgetProp := budget.property
  change Run instructions (cfg .massLeft s) (cfg (if value mass≤1 then .oneLeft else bad) s) left.val at leftProp
  change Run instructions (cfg .oneLeft s) (cfg (if 1≤value mass then .budgetLeft else bad) s) right.val at rightProp
  change Run instructions (cfg .budgetLeft s) (cfg (if value positive≤value negative then good else bad) s) budget.val at budgetProp
  by_cases hlo : value mass≤1
  · simp only [if_pos hlo] at leftProp
    by_cases hhi : 1≤value mass
    · simp only [if_pos hhi] at rightProp
      have he : value mass=1 := by omega
      have run := seq instructions (seq instructions leftProp rightProp) budgetProp
      by_cases hb : value positive≤value negative
      · exact ⟨_, by simpa [good,bad,he,hb,s] using run⟩
      · exact ⟨_, by simpa [good,bad,he,hb,s] using run⟩
    · have he : value mass≠1 := by omega
      exact ⟨_, by simpa [bad,hhi,he,s] using seq instructions leftProp rightProp⟩
  · have he : value mass≠1 := by omega
    exact ⟨left.val, by simpa [bad,hlo,he,s] using leftProp⟩

def retained (base : K → Bits) : K → Bits
  | .inl _ => []
  | .inr k => if k.val<10 then base (.inr k) else []

def workSize (s : K → Bits) : ℕ := ∑ k : Fin 35, if 10≤k.val then (s (reg k)).length else 0

theorem le_workSize (s : K → Bits) (k : Fin 35) (hk : 10≤k.val) :
    (s (reg k)).length≤workSize s := by
  have h := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j : Fin 35 => if 10≤j.val then (s (reg j)).length else 0)
    (by intro j _; exact Nat.zero_le _) (Finset.mem_univ k)
  simpa only [if_pos hk,workSize] using h

theorem wipe_state (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    wipe (state base P H u ap an par cap coord plus minus positive negative mass) 0=retained base := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

def cleanup_state_run (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits)
    (b : Bool) : Execution
      (cfg (.cleanup b 0) (state base P H u ap an par cap coord plus minus positive negative mass))
      ⟨none,(none,b),retained base⟩ := by
  let s := state base P H u ap an par cap coord plus minus positive negative mass
  have run := cleanup_run b 25 0 rfl s (workSize s) rfl (le_workSize s)
  rw [show wipe s 0=retained base from wipe_state base P H u ap an par cap coord plus minus positive negative mass] at run
  exact ⟨_,run⟩

def final_run (base : K → Bits) (positive negative mass : Bits) :
    Execution (cfg .loop (ready base [] [] [] [] [] positive negative mass))
      ⟨none,(none,decide (value mass=1 ∧ value positive≤value negative)),retained base⟩ := by
  have first := test_run instructions .loop .massLeft .readP (reg 10) rfl
    (ready base [] [] [] [] [] positive negative mass)
  change Run instructions _ (cfg .massLeft (ready base [] [] [] [] [] positive negative mass)) 1 at first
  have tests := final_test_run base positive negative mass
  have clean := cleanup_state_run base [] [] [] [] [] [] [] [] [] [] positive negative mass
    (decide (value mass=1 ∧ value positive≤value negative))
  exact ⟨_,seq instructions (seq instructions first tests.property) clean.property⟩

end UAVProof.A4RowCheck
