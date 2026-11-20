import LeanCompletion.UAV.TreeBudgetRootFlowTM2
import LeanCompletion.UAV.TreeBudgetRootFlowScanTotal

namespace UAVProof.TreeBudgetRootFlowTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetParentPrefix (Raw)

def seq {a b c : Cfg} {x y : ℕ} (h : Run a b x) (g : Run b c y) : Run a c (x+y) :=
  by simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step x y a b (some c) h g

theorem prefix_return (out : TreeBudgetParentPrefixTM2.Cfg) (hl : out.l=none) :
    (embed prefixW L.prefix (.control .prefixed) (fun _ => []) out).stk=store {p:=out.stk} := by
  funext k
  rcases k with k | k | k | k
  · rfl
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem prefix_continue (out : TreeBudgetParentPrefixTM2.Cfg) (hl : out.l=none) (hb : out.var.2=true) :
    machine.step (embed prefixW L.prefix (.control .prefixed) (fun _ => []) out)=
      some (cfg (entry .input) {p:=out.stk}) := by
  simp only [machine,FinTM2.step,TM2.step,embed,hl,Option.elim_none,program,TM2.stepAux,hb]
  rw [show bank prefixW (fun _ => []) out.stk=store {p:=out.stk} from prefix_return out hl]
  rfl

theorem list_input (p : TreeBudgetParentPrefixTM2.K → Bits) (s : Bits) (hp : p TreeBudgetParentPrefixTM2.suffix=s) :
    cfg (.list 0) (copied .input {p:=p})=
      embed listW L.list (.control .listed) (store {p:=p}) (TreeBudgetListGuardTM2.atLabel 0 s [] [] [] [] []) := by
  simp only [cfg,embed,TreeBudgetListGuardTM2.atLabel]
  congr 1
  funext k
  rcases k with k | k | k
  · rfl
  · fin_cases k
    · change p TreeBudgetParentPrefixTM2.suffix ++ []=s
      simpa only [List.append_nil] using hp
    all_goals rfl
  · rfl

theorem list_halted (s : Bits) : (TreeBudgetCountedNatsTM2.stopped s []).l=none := by
  unfold TreeBudgetCountedNatsTM2.stopped
  dsimp only
  split <;> rfl

theorem list_continue (p : TreeBudgetParentPrefixTM2.K → Bits) (s : Bits)
    (hb : (TreeBudgetCountedNatsTM2.stopped s []).var.2=true) :
    machine.step (embed listW L.list (.control .listed) (store {p:=p}) (TreeBudgetCountedNatsTM2.stopped s []))=
      some (cfg (entry .parents) {p:=p,t:=(TreeBudgetCountedNatsTM2.stopped s []).stk}) := by
  simp only [machine,FinTM2.step,TM2.step,embed,list_halted,Option.elim_none,program,TM2.stepAux,hb,list_bank]
  rfl

def prepare_run (a : Raw) (hs : List ℕ) (p : TreeBudgetParentPrefixTM2.K → Bits) (t : Fin 7 → Bits)
    (hp : p TreeBudgetParentPrefixTM2.parsedBody=TreeBudgetParentPrefix.body a)
    (hr : p TreeBudgetParentPrefixTM2.parsedRoot=a.root.bits)
    (hm : p (.inr (.inr 0))=a.routes.bits) (hh : t 2=hs.flatMap encodeNat) :
    Run (cfg (entry .parents) {p:=p,t:=t})
      (cfg (.scan TreeBudgetRootFlowScanTM2.machine.main) ⟨p,t,TreeBudgetRootFlowScanTM2.initial a.parents hs a.root a.routes⟩)
      (2*((TreeBudgetParentPrefix.body a).length+a.root.bits.length+a.routes.bits.length+
        (hs.flatMap encodeNat).length)+8) := by
  let d₀ : Data := {p:=p,t:=t}
  let d₁ := copied .parents d₀
  let d₂ := copied .root d₁
  let d₃ := copied .routes d₂
  have h₁ := copy_job .parents d₀ rfl
  have h₂ := copy_job .root d₁ rfl
  have h₃ := copy_job .routes d₂ rfl
  have h₄ := copy_job .demands d₃ rfl
  exact weaken (by simpa [d₃,d₂,d₁,d₀,copied,setDest,source,dest,hp,hr,hm,hh,
      TreeBudgetRootFlowScanTM2.initial,TreeBudgetParentPrefix.body] using seq (seq (seq h₁ h₂) h₃) h₄)
    (by simp only [TreeBudgetParentPrefix.body,List.length_flatMap]; omega)

theorem scan_call (a : Raw) (hs : List ℕ) (p : TreeBudgetParentPrefixTM2.K → Bits) (t : Fin 7 → Bits) (S : ℕ)
    (bp : (TreeBudgetParentPrefix.body a).length≤S) (bh : (hs.flatMap encodeNat).length≤S)
    (br : a.root.bits.length≤S) (bm : a.routes.bits.length≤S) (bn : a.parents.length≤S) :
    ∃ out, Nonempty (Run (cfg (.scan TreeBudgetRootFlowScanTM2.machine.main)
      ⟨p,t,TreeBudgetRootFlowScanTM2.initial a.parents hs a.root a.routes⟩) out (256*(S+1)^2+1)) ∧
      out.l=none ∧ out.var.2=TreeBudgetRootFlowSpec.listOK a hs ∧
      (∀ k, out.stk (.inl k)=p k) ∧ (∀ k, out.stk (.inr (.inl k))=t k) := by
  obtain ⟨c,⟨run⟩,hl,hv,hkeep⟩ := TreeBudgetRootFlowScanTM2.scan_polynomial a.parents hs a.root a.routes S bp bh br bm bn
  have call := call_run scanW L.scan (.control .scanned) (store {p:=p,t:=t})
    TreeBudgetRootFlowScanTM2.program program (fun _ => rfl) run
  have init : embed scanW L.scan (.control .scanned) (store {p:=p,t:=t})
      (TreeBudgetRootFlowScanTM2.start a.parents hs a.root a.routes)=
      cfg (.scan TreeBudgetRootFlowScanTM2.machine.main) ⟨p,t,TreeBudgetRootFlowScanTM2.initial a.parents hs a.root a.routes⟩ := by
    simp only [TreeBudgetRootFlowScanTM2.start,TreeBudgetRootFlowScanTM2.cfg,embed,scan_bank]
    rfl
  rw [init] at call
  let out : Cfg := {embed scanW L.scan (.control .scanned) (store {p:=p,t:=t}) c with l:=none}
  have last : machine.step (embed scanW L.scan (.control .scanned) (store {p:=p,t:=t}) c)=some out := by
    simp [machine,FinTM2.step,TM2.step,embed,hl,program,TM2.stepAux,out]
  exact ⟨out,⟨seq call (once last)⟩,rfl,hv,fun _ => rfl,fun _ => rfl⟩

end UAVProof.TreeBudgetRootFlowTM2
