import LeanCompletion.UAV.TreeBudgetRowCheckTM2
import LeanCompletion.UAV.TreeBudgetSemanticRegisterRuns

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def cleanPC (b : Bool) (i : ℕ) : PC :=
  if h : i<25 then .cleanup b ⟨i,h⟩ else .finish b

def wipe (s : K → Bits) (i : ℕ) : K → Bits
  | .inl k => s (.inl k)
  | .inr k => if 10+i≤k.val then [] else s (.inr k)

theorem wipe_end (s : K → Bits) : wipe s 25=s := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => simp [wipe,show ¬10+25≤k.val by omega]

theorem wipe_step (s : K → Bits) (i : ℕ) (hi : i<25) :
    wipe (Function.update s (reg ⟨10+i,by omega⟩) []) (i+1)=wipe s i := by
  funext k
  cases k with
  | inl k => simp [wipe,reg]
  | inr k =>
    by_cases he : k.val=10+i
    · have hk : k=⟨10+i,by omega⟩ := Fin.ext he
      rw [hk]
      simp [wipe,reg]
    · have hk : (Sum.inr k : K)≠reg ⟨10+i,by omega⟩ := by simp [reg,Fin.ext_iff,he]
      simp only [wipe,Function.update_of_ne hk]
      have heq : (10+(i+1)≤k.val) ↔ (10+i≤k.val) := by omega
      simp only [heq]

/-- Cleanup has the same layout on acceptance and rejection. Its cost is
linear in the physical contents of the fixed workspace bank. -/
def cleanup_run (b : Bool) (remaining i : ℕ) (h : i+remaining=25)
    (s : K → Bits) (R : ℕ)
    (hs : s (.inl (.inr false))=[])
    (hw : ∀ k : Fin 35, 10≤k.val → (s (reg k)).length≤R) :
    Run instructions (cfg (cleanPC b i) s)
      ⟨none,(none,b),wipe s i⟩ (remaining*(R+2)+1) := by
  induction remaining generalizing i s with
  | zero =>
    have hi : i=25 := by omega
    subst i
    simp only [cleanPC,show ¬25<25 by omega,dif_neg,wipe_end,Nat.zero_mul,Nat.zero_add]
    cases b with
    | false => exact fail_run instructions (.finish false) rfl s
    | true => exact halt_run instructions (.finish true) rfl s
  | succ remaining ih =>
    have hi : i<25 := by omega
    let k : Fin 35 := ⟨10+i,by omega⟩
    let p : Ports K := ⟨reg k,.inl (.inr false),reg 9,
      by simp [reg],by simp only [reg,ne_eq,Sum.inr.injEq,Fin.ext_iff,k]; omega,by simp [reg]⟩
    let next := cleanPC b (i+1)
    have hinst : instructions (.cleanup b ⟨i,hi⟩)=.clear p next := by
      simp [instructions,p,k,next,cleanPC]
    have one := clear_run instructions (.cleanup b ⟨i,hi⟩) next p hinst s hs
    let s' := Function.update s (reg k) []
    have hs' : s' (.inl (.inr false))=[] := by simp [s',reg,hs]
    have hw' : ∀ j : Fin 35, 10≤j.val → (s' (reg j)).length≤R := by
      intro j hj
      by_cases he : j=k
      · subst j; simp [s']
      · simp [s',reg,he,hw j hj]
    have tail := ih (i+1) (by omega) s' hs' hw'
    have run := seq instructions one tail
    have he : wipe s' (i+1)=wipe s i := wipe_step s i hi
    rw [he] at run
    apply weaken (by simpa [cleanPC,hi,s',next,p,k] using run)
    have hk := hw k (by simp [k])
    dsimp [p,k] at hk ⊢
    rw [Nat.add_mul]
    omega

theorem wipe_store (P H row plus minus root tp tn ctx suffix : Bits) :
    wipe (store P H row plus minus root tp tn ctx suffix) 0=
      store P H row plus minus root tp tn ctx suffix := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

end UAVProof.A4RowCheck
