import LeanCompletion.UAV.TreeBudgetSignedWordTM2
import LeanCompletion.UAV.TreeBudgetWeightedWidth
import LeanCompletion.UAV.TreeBudgetStackRoutine
import LeanCompletion.UAV.TreeBudgetTM2CallOn

/-! A finite-control assembler for physical word operations. Each instruction
expands to the existing stack, frame, multiplication or signed-output routine;
the accompanying runs count dispatch and return transitions as well. -/
namespace UAVProof.TreeBudgetRegisterTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
open Turing.TM2.Stmt

inductive Instr (K Λ : Type)
  | copy (p : Ports K) (framed : Bool) (next : Λ)
  | clear (p : Ports K) (next : Λ)
  | read (p : Ports K) (next : Λ)
  | mul (w : Wiring (Fin 6) K) (next : Λ)
  | emit (p : Ports K) (sign : K) (next : Λ)
  | bit (src dst : K) (next : Λ)
  | test (src : K) (empty more : Λ)
  | push (dst : K) (b : Bool) (next : Λ)
  | halt

inductive Label (Λ : Type)
  | pc (l : Λ)
  | stack (l : Λ) (ph : TreeBudgetStackRoutine.Phase)
  | read (l : Λ) (ph : TreeBudgetFrameRoutineTM2.Phase)
  | mul (l : Λ) (ph : Fin 6)
  | emit (l : Λ) (ph : TreeBudgetSignedWordTM2.Phase)
  | done (l : Λ)
  | bad
  deriving DecidableEq, Fintype

variable {K Λ : Type} [DecidableEq K]

def reject : Statement K (Label Λ) := load (fun _ => (none,false)) halt

def program (I : Λ → Instr K Λ) : Label Λ → Statement K (Label Λ)
  | .pc l => match I l with
    | .copy _ _ _ => TreeBudgetStackRoutine.jump (.stack l .reverse)
    | .clear _ _ => TreeBudgetStackRoutine.jump (.stack l .clear)
    | .read _ _ => TreeBudgetStackRoutine.jump (.read l .marker)
    | .mul _ _ => load (fun _ => (none,false)) (goto fun _ => .mul l 0)
    | .emit _ sg _ => pop sg (fun _ b => (none,b.getD false)) (goto fun _ => .emit l .reverse)
    | .bit s d next => pop s (fun _ b => (b,true))
        (branch (fun v => v.1.isNone) reject
          (push d (fun v => v.1.getD false) (TreeBudgetStackRoutine.jump (.pc next))))
    | .test s a b => peek s (fun _ v => (v,true))
        (branch (fun v => v.1.isNone) (TreeBudgetStackRoutine.jump (.pc a))
          (TreeBudgetStackRoutine.jump (.pc b)))
    | .push d b next => push d (fun _ => b) (TreeBudgetStackRoutine.jump (.pc next))
    | .halt => load (fun _ => (none,true)) halt
  | .stack l ph => match I l with
    | .copy p framed next => TreeBudgetStackRoutine.code p (Label.stack l) (.pc next) framed ph
    | .clear p next => TreeBudgetStackRoutine.code p (Label.stack l) (.pc next) false ph
    | _ => reject
  | .read l ph => match I l with
    | .read p next => code p (Label.read l) (.pc next) .bad false ph
    | _ => reject
  | .mul l ph => match I l with
    | .mul w next => compile w (Label.mul l) (.done next) (TreeBudgetWeightedTM2.program ph)
    | _ => reject
  | .emit l ph => match I l with
    | .emit p _ next => TreeBudgetSignedWordTM2.code p (Label.emit l) (.pc next) ph
    | _ => reject
  | .done l => TreeBudgetStackRoutine.jump (.pc l)
  | .bad => reject

abbrev Cfg (K Λ : Type) := Configuration K (Label Λ)
def cfg (l : Λ) (s : K → Bits) : Cfg K Λ := ⟨some (.pc l),(none,true),s⟩
def stopped (s : K → Bits) : Cfg K Λ := ⟨none,(none,true),s⟩
abbrev Run (I : Λ → Instr K Λ) (a b : Cfg K Λ) (t : ℕ) :=
  StateTransition.EvalsToInTime (TM2.step (program I)) a (some b) t

def seq (I : Λ → Instr K Λ) {a b c : Cfg K Λ} {u v : ℕ}
    (h : Run I a b u) (g : Run I b c v) : Run I a c (u+v) := by
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans
    (TM2.step (program I)) u v a b (some c) h g

end UAVProof.TreeBudgetRegisterTM2
