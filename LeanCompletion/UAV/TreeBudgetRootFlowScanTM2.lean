import LeanCompletion.UAV.TreeBudgetNatRoutine
import LeanCompletion.UAV.TreeBudgetCompareRoutine
import LeanCompletion.UAV.TreeBudgetStackRoutine

/-! A physical, synchronized parent/H scan. Original tables and m,r are kept.
The two EOF tests enforce equal lengths; only nonroot direct children add. -/
namespace UAVProof.TreeBudgetRootFlowScanTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open Turing.TM2.Stmt

inductive Job
  | parents | demands | rootP | index | rootI | operand | clearAcc | clearH | increment
  | finalA | finalM | reverseM | reverseA
  deriving DecidableEq, Fintype
inductive Check | parent | index | le | ge
  deriving DecidableEq, Fintype
inductive Control | loop | add | returned | reject
  deriving DecidableEq, Fintype
inductive L
  | adder : Fin 3 → L
  | job : Job → TreeBudgetStackRoutine.Phase → L
  | frame : Bool → Phase → L
  | compare : Check → L
  | compared : Check → L
  | control : Control → L
  deriving DecidableEq, Fintype

abbrev K := Fin 4 ⊕ Fin 10
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev acc : K := .inl 3
abbrev temp : K := .inr 9
def entry (j : Job) : L := .job j (match j with
  | .clearAcc | .clearH => .clear | .increment => .carry | _ => .reverse)
def next : Job → L
  | .parents => entry .demands | .demands => .control .loop
  | .rootP => .compare .parent | .index => entry .rootI | .rootI => .compare .index
  | .operand => entry .clearAcc | .clearAcc => .control .add
  | .clearH => entry .increment | .increment => .control .loop
  | .finalA => entry .finalM | .finalM => .compare .le
  | .reverseM => entry .reverseA | .reverseA => .compare .ge
def ports (j : Job) : Ports K where
  src := match j with
    | .parents => .inr 0 | .demands => .inr 1 | .rootP | .rootI => .inr 2
    | .index | .increment => .inr 6 | .clearH => .inl 1
    | .finalM | .reverseM => .inr 3 | _ => acc
  scratch := temp
  dst := match j with
    | .parents => .inr 4 | .demands => .inr 5
    | .rootP | .rootI | .finalM | .reverseA => .inr 8
    | .index | .finalA | .reverseM => .inr 7
    | .operand => .inl 0 | _ => .inr 0
  scratch_ne_src := by cases j <;> decide
  dst_ne_src := by cases j <;> decide
  dst_ne_scratch := by cases j <;> decide
def framePorts (h : Bool) : Ports K :=
  ⟨.inr (if h then 5 else 4),temp,if h then .inl 1 else .inr 7,
    by cases h <;> decide,by cases h <;> decide,by cases h <;> decide⟩
def frameNext (h : Bool) : L := if h then entry .rootP else .frame true .marker
def comparePorts : Ports K := ⟨.inr 7,.inr 8,.inr 6,by decide,by decide,by decide⟩
def equal : Check → Bool | .parent | .index => true | _ => false
def jump (l : L) : Stmt := TreeBudgetStackRoutine.jump l
def program : L → Stmt
  | .adder l => compile L.adder (.control .returned) (TreeBudgetAddWordsTM2.program l)
  | .job j p => TreeBudgetStackRoutine.code (ports j) (L.job j) (next j) false p
  | .frame h p => code (framePorts h) (L.frame h) (frameNext h) (.control .reject) true p
  | .compare c => TreeBudgetCompareRoutine.code comparePorts (.compare c) (.compared c) (equal c)
  | .compared .parent => branch Prod.snd (jump (entry .index)) (jump (entry .clearH))
  | .compared .index => branch Prod.snd (jump (entry .clearH)) (jump (entry .operand))
  | .compared .le => branch Prod.snd (jump (entry .reverseM)) halt
  | .compared .ge => halt
  | .control .loop => peek (.inr 4) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone)
        (peek (.inr 5) (fun _ b => (b,true)) (branch (fun s => s.1.isNone)
          (jump (entry .finalA)) (load (fun _ => (none,false)) halt)))
        (peek (.inr 5) (fun _ b => (b,true)) (branch (fun s => s.1.isNone)
          (load (fun _ => (none,false)) halt) (jump (.frame false .marker)))))
  | .control .add => load (fun _ => (none,false)) (goto (fun _ => .adder 0))
  | .control .returned => jump (entry .increment)
  | .control .reject => load (fun _ => (none,false)) halt

def machine : FinTM2 where
  K := K
  k₀ := .inr 0
  k₁ := acc
  Γ _ := Bool
  Λ := L
  main := entry .parents
  σ := State
  initialState := (none,true)
  m := program

structure Data where
  a : Bits := []
  b : Bits := []
  c : Bits := []
  u : Bits := []
  p : Bits := []
  h : Bits := []
  r : Bits := []
  m : Bits := []
  pw : Bits := []
  hw : Bits := []
  idx : Bits := []
  x : Bits := []
  y : Bits := []
  tmp : Bits := []
def saved (d : Data) (k : Fin 10) : Bits := match k.val with
  | 0 => d.p | 1 => d.h | 2 => d.r | 3 => d.m | 4 => d.pw | 5 => d.hw
  | 6 => d.idx | 7 => d.x | 8 => d.y | _ => d.tmp
def store (d : Data) : K → Bits := banks (TreeBudgetAddWordsTM2.tapes d.a d.b d.c d.u) (saved d)
def cfg (l : L) (d : Data) (b : Bool := true) : Cfg := ⟨some l,(none,b),store d⟩
def stop (d : Data) (b : Bool) : Cfg := ⟨none,(none,b),store d⟩
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n
def initial (p h : List ℕ) (r m : ℕ) : Data :=
  {p:=p.flatMap encodeNat,h:=h.flatMap encodeNat,r:=r.bits,m:=m.bits}
def start (p h : List ℕ) (r m : ℕ) := cfg (entry .parents) (initial p h r m)
def Kept (d : Data) (out : Cfg) : Prop :=
  out.stk (.inr 0)=d.p ∧ out.stk (.inr 1)=d.h ∧ out.stk (.inr 2)=d.r ∧ out.stk (.inr 3)=d.m

def source (j : Job) (d : Data) : Bits := match j with
  | .parents => d.p | .demands => d.h | .rootP | .rootI => d.r
  | .index | .increment => d.idx | .clearH => d.b | .finalM | .reverseM => d.m | _ => d.u
def dest (j : Job) (d : Data) : Bits := match j with
  | .parents => d.pw | .demands => d.hw | .rootP | .rootI | .finalM | .reverseA => d.y
  | .index | .finalA | .reverseM => d.x | .operand => d.a | _ => d.p
def replace (j : Job) (d : Data) (s t z : Bits) : Data := match j with
  | .parents => {d with p:=s,tmp:=t,pw:=z} | .demands => {d with h:=s,tmp:=t,hw:=z}
  | .rootP | .rootI => {d with r:=s,tmp:=t,y:=z}
  | .index => {d with idx:=s,tmp:=t,x:=z} | .increment => {d with idx:=s,tmp:=t,p:=z}
  | .operand => {d with u:=s,tmp:=t,a:=z} | .clearAcc => {d with u:=s,tmp:=t,p:=z}
  | .clearH => {d with b:=s,tmp:=t,p:=z}
  | .finalA => {d with u:=s,tmp:=t,x:=z} | .finalM => {d with m:=s,tmp:=t,y:=z}
  | .reverseM => {d with m:=s,tmp:=t,x:=z} | .reverseA => {d with u:=s,tmp:=t,y:=z}
theorem replace_original (j : Job) (d : Data) : replace j d (source j d) d.tmp (dest j d)=d := by cases j <;> rfl
theorem tapes_replace (j : Job) (d : Data) (s t z : Bits) :
    tapes (ports j) (store d) s t z=store (replace j d s t z) := by
  cases j <;> funext k <;> cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl
theorem conf_replace (j : Job) (d : Data) (l : L) (s t z : Bits) :
    TreeBudgetStackRoutine.conf (ports j) (store d) l s t z=cfg l (replace j d s t z) := by
  simp only [TreeBudgetStackRoutine.conf,cfg,tapes_replace]
def copied (j : Job) (d : Data) := replace j d (source j d) [] (source j d ++ dest j d)
def copy_job (j : Job) (d : Data) (ht : d.tmp=[]) :
    Run (cfg (.job j .reverse) d) (cfg (next j) (copied j d)) (2*(source j d).length+2) := by
  have h := TreeBudgetStackRoutine.copy_run (ports j) (store d) (L.job j) (next j) false
    program (fun _ => rfl) (source j d) (dest j d)
  rw [conf_replace,conf_replace,← ht,replace_original] at h
  simpa only [copied,ht] using h
def clear_job (j : Job) (d : Data) :
    Run (cfg (.job j .clear) d) (cfg (next j) (replace j d [] d.tmp (dest j d))) ((source j d).length+1) := by
  have h := TreeBudgetStackRoutine.clear_run (ports j) (store d) (L.job j) (next j) false
    program (fun _ => rfl) (source j d) d.tmp (dest j d)
  rw [conf_replace,conf_replace,replace_original] at h
  exact h
def increment_job (d : Data) (ht : d.tmp=[]) :
    Run (cfg (entry .increment) d) (cfg (.control .loop) {d with idx:=TreeBudgetStackRoutine.increment d.idx})
      (2*d.idx.length+2) := by
  have h := TreeBudgetStackRoutine.increment_run (ports .increment) (store d) (L.job .increment)
    (next .increment) false program (fun _ => rfl) d.idx [] d.p
  rw [conf_replace,conf_replace] at h
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at h
  rw [← ht] at h
  exact h

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by change Finite Bool; infer_instance
set_option maxRecDepth 10000 in
theorem finite_control : Fintype.card K=14 ∧ Fintype.card L=101 ∧ Fintype.card State=6 := by decide

end UAVProof.TreeBudgetRootFlowScanTM2
