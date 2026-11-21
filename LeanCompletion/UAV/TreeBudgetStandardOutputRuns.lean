import LeanCompletion.UAV.TreeBudgetStandardOutputTM2
import LeanCompletion.UAV.TreeBudgetTransitionSpace

namespace UAVProof.TreeBudgetStandardOutputTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetTransitionSpace
variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]
variable (ks : List K) (M : Λ → Statement K Λ)

def Run (a b : Configuration (K ⊕ Unit) (Label Λ ks.length)) (t : ℕ) :=
  EvalsToInTime (TM2.step (program ks M)) a (some b) t

theorem clear_cons (i : Fin (ks.length+1)) (hi : i.val<ks.length)
    (s : K → Bits) (out tail : Bits) (b : Bool) (hs : s ks[i.val]=b::tail) :
    TM2.step (program ks M) (cfg ks i s out)=
      some (cfg ks i (Function.update s ks[i.val] tail) out) := by
  simp [program,cfg,TM2.step,TM2.stepAux,hi,store,hs,jump,store_update]

theorem clear_nil (i : Fin (ks.length+1)) (hi : i.val<ks.length)
    (s : K → Bits) (out : Bits) (hs : s ks[i.val]=[]) :
    TM2.step (program ks M) (cfg ks i s out)=
      some (cfg ks ⟨i.val+1,by omega⟩ s out) := by
  simp [program,cfg,TM2.step,TM2.stepAux,hi,store,hs,jump,store_update]
  rw [← hs,Function.update_eq_self]

def clear_stack_run (i : Fin (ks.length+1)) (hi : i.val<ks.length)
    (s : K → Bits) (out : Bits) (u : Bits) (hs : s ks[i.val]=u) :
    Run ks M (cfg ks i s out)
      (cfg ks ⟨i.val+1,by omega⟩ (Function.update s ks[i.val] []) out) (u.length+1) := by
  induction u generalizing s with
  | nil =>
    have hsame : Function.update s ks[i.val] []=s := by rw [← hs,Function.update_eq_self]
    rw [hsame]
    exact once (clear_nil ks M i hi s out hs)
  | cons b u ih =>
    have one := clear_cons ks M i hi s out u b hs
    have tail := ih (Function.update s ks[i.val] u) (by simp)
    simpa only [Function.update_idem,List.length_cons,Nat.add_assoc] using prepend one tail

def clear_all_run (pref rest : List K) (he : ks=pref++rest)
    (s : K → Bits) (out : Bits) (B : ℕ) (hb : Bounded s B) :
    Run ks M (cfg ks ⟨pref.length,by simp [he]⟩ s out)
      ⟨none,(none,true),store (cleaned rest s) out⟩ (rest.length*(B+1)+1) := by
  induction rest generalizing pref s with
  | nil =>
    have hp : pref.length=ks.length := by simp_all
    simp only [cleaned_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
    apply once
    simp [program,cfg,TM2.step,TM2.stepAux,hp]
  | cons k rest ih =>
    let i : Fin (ks.length+1) := ⟨pref.length,by simp [he]⟩
    have hi : i.val<ks.length := by simp [i,he]
    have hk : ks[i.val]=k := by simp [he,i]
    have first := clear_stack_run ks M i hi s out (s k) (by rw [hk])
    have hnext : ks=(pref++[k])++rest := by simpa only [List.append_assoc,List.singleton_append] using he
    have hb' := update_bound s B hb k [] (by simp)
    have tail := ih (pref++[k]) hnext (Function.update s k []) hb'
    rw [hk] at first
    have hn : (⟨i.val+1,by omega⟩ : Fin (ks.length+1))=
        ⟨(pref++[k]).length,by simp [hnext]⟩ := by ext; simp [i]
    rw [hn] at first
    have run := EvalsToInTime.trans (TM2.step (program ks M)) _ _ _ _ _ first tail
    rw [← cleaned_cons] at run
    apply weaken run
    simp only [List.length_cons]
    have h := hb k
    nlinarith

theorem covered_clean (cover : ∀ k, k∈ks) (s : K → Bits) : cleaned ks s=(fun _ => []) := by
  funext k; simp [cleaned,cover k]

/-- Both Boolean returns reach the exact standard configuration, including
empty work stacks and the initial finite state. -/
def return_run (input : K) (main : Λ) (cover : ∀ k, k∈ks)
    (v : State) (s : K → Bits) (B : ℕ) (hb : Bounded s B) :
    Run ks M ⟨some .write,v,store s []⟩
      (haltList (machine ks input main M) [v.2]) (ks.length*(B+1)+2) := by
  have first : TM2.step (program ks M) ⟨some .write,v,store s []⟩=
      some (cfg ks 0 s [v.2]) := by
    simp [program,TM2.step,TM2.stepAux,jump,cfg,store]
    congr 1
    funext k; cases k <;> simp [store,Function.update_apply]
  have tail := clear_all_run ks M [] ks (by simp) s [v.2] B hb
  rw [covered_clean ks cover] at tail
  have last : (⟨none,(none,true),store (fun _ => []) [v.2]⟩ :
      Configuration (K ⊕ Unit) (Label Λ ks.length))=
      haltList (machine ks input main M) [v.2] := by
    unfold haltList machine
    congr 1
    funext k; cases k <;> simp [store]
  rw [last] at tail
  simpa only [Nat.add_assoc] using prepend first tail

end UAVProof.TreeBudgetStandardOutputTM2
