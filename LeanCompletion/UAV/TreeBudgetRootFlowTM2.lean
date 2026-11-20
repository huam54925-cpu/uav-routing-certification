import LeanCompletion.UAV.TreeBudgetParentPrefixTotal
import LeanCompletion.UAV.TreeBudgetRootFlowScanTM2
import LeanCompletion.UAV.TreeBudgetTM2CallOn

/-! Raw input caller: parent-prefix validation, guarded H parsing, synchronized
root-flow scan. Only statically wired subprograms and physical stack copies. -/
namespace UAVProof.TreeBudgetRootFlowTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open Turing.TM2.Stmt

set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024

abbrev K := TreeBudgetParentPrefixTM2.K ⊕ (Fin 7 ⊕ TreeBudgetRootFlowScanTM2.K)
instance decidableStack : DecidableEq K := inferInstanceAs (DecidableEq (TreeBudgetParentPrefixTM2.K ⊕ (Fin 7 ⊕ TreeBudgetRootFlowScanTM2.K)))
inductive Job | input | parents | root | routes | demands
  deriving DecidableEq, Fintype
inductive Control | prefixed | listed | scanned
  deriving DecidableEq, Fintype
inductive L
  | prefix : TreeBudgetParentPrefixTM2.L → L
  | list : Fin 18 → L
  | scan : TreeBudgetRootFlowScanTM2.L → L
  | job : Job → TreeBudgetStackRoutine.Phase → L
  | control : Control → L
  deriving DecidableEq, Fintype
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L

def prefixW : Wiring TreeBudgetParentPrefixTM2.K K :=
  ⟨Sum.inl,(fun k => match k with | .inl i => some i | _ => none),by intro k; rfl,
    by intro r k h; cases r <;> simpa using h⟩
def listW : Wiring (Fin 7) K :=
  ⟨(fun k => .inr (.inl k)),(fun k => match k with | .inr (.inl i) => some i | _ => none),
    by intro k; rfl,by intro r k h; rcases r with r | r | r <;> simpa using h⟩
def scanW : Wiring TreeBudgetRootFlowScanTM2.K K :=
  ⟨(fun k => .inr (.inr k)),(fun k => match k with | .inr (.inr i) => some i | _ => none),
    by intro k; rfl,by intro r k h; rcases r with r | r | r <;> simpa using h⟩

abbrev context : K := .inl TreeBudgetParentPrefixTM2.context
abbrev suffix : K := .inr (.inl 0)
abbrev demands : K := .inr (.inl 2)
abbrev temp : K := .inr (.inr TreeBudgetRootFlowScanTM2.temp)
def entry (j : Job) : L := .job j .reverse
def next : Job → L
  | .input => .list 0 | .parents => entry .root | .root => entry .routes
  | .routes => entry .demands | .demands => .scan TreeBudgetRootFlowScanTM2.machine.main
def ports (j : Job) : Ports K where
  src := match j with
    | .input => .inl TreeBudgetParentPrefixTM2.suffix | .parents => .inl TreeBudgetParentPrefixTM2.parsedBody
    | .root => .inl TreeBudgetParentPrefixTM2.parsedRoot | .routes => .inl (.inr (.inr 0))
    | .demands => demands
  scratch := temp
  dst := match j with
    | .input => suffix | .parents => .inr (.inr (.inr 0))
    | .root => .inr (.inr (.inr 2)) | .routes => .inr (.inr (.inr 3))
    | .demands => .inr (.inr (.inr 1))
  scratch_ne_src := by cases j <;> decide
  dst_ne_src := by cases j <;> decide
  dst_ne_scratch := by cases j <;> decide
def program : L → Stmt
  | .prefix l => compile prefixW L.prefix (.control .prefixed) (TreeBudgetParentPrefixTM2.program l)
  | .list l => compile listW L.list (.control .listed) (TreeBudgetListGuardTM2.program l)
  | .scan l => compile scanW L.scan (.control .scanned) (TreeBudgetRootFlowScanTM2.program l)
  | .job j q => TreeBudgetStackRoutine.code (ports j) (L.job j) (next j) false q
  | .control .prefixed => branch Prod.snd (TreeBudgetStackRoutine.jump (entry .input)) halt
  | .control .listed => branch Prod.snd (TreeBudgetStackRoutine.jump (entry .parents)) halt
  | .control .scanned => halt
def machine : FinTM2 where
  K := K
  k₀ := .inl TreeBudgetParentPrefixTM2.machine.k₀
  k₁ := .inr (.inr TreeBudgetRootFlowScanTM2.acc)
  Γ _ := Bool
  Λ := L
  main := .prefix TreeBudgetParentPrefixTM2.machine.main
  σ := State
  initialState := (none,true)
  m := program

structure Data where
  p : TreeBudgetParentPrefixTM2.K → Bits
  t : Fin 7 → Bits := fun _ => []
  c : TreeBudgetRootFlowScanTM2.Data := {}
def store (d : Data) : K → Bits := TreeBudgetTM2Call.banks d.p (TreeBudgetTM2Call.banks d.t (TreeBudgetRootFlowScanTM2.store d.c))
def cfg (l : L) (d : Data) (b : Bool := true) : Cfg := ⟨some l,(none,b),store d⟩
def start (s ctx : Bits) : Cfg := embed prefixW L.prefix (.control .prefixed) (fun _ => []) (TreeBudgetParentPrefixTM2.start s ctx)
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n

def source (j : Job) (d : Data) : Bits := match j with
  | .input => d.p TreeBudgetParentPrefixTM2.suffix | .parents => d.p TreeBudgetParentPrefixTM2.parsedBody
  | .root => d.p TreeBudgetParentPrefixTM2.parsedRoot | .routes => d.p (.inr (.inr 0)) | .demands => d.t 2
def dest (j : Job) (d : Data) : Bits := match j with
  | .input => d.t 0 | .parents => d.c.p | .root => d.c.r | .routes => d.c.m | .demands => d.c.h
def setDest (j : Job) (d : Data) (v : Bits) : Data := match j with
  | .input => {d with t:=Function.update d.t 0 v}
  | .parents => {d with c:={d.c with p:=v}}
  | .root => {d with c:={d.c with r:=v}}
  | .routes => {d with c:={d.c with m:=v}}
  | .demands => {d with c:={d.c with h:=v}}
def copied (j : Job) (d : Data) := setDest j d (source j d ++ dest j d)

theorem restored {I : Type} [DecidableEq I] (p : Ports I) (s : I → Bits) (v : Bits) (ht : s p.scratch=[]) :
    tapes p s (s p.src) [] v=Function.update s p.dst v := by
  funext k
  by_cases hd : k=p.dst
  · subst k; simp
  · by_cases hs : k=p.src
    · subst k; simp [tapes,Function.update_apply,Ne.symm p.dst_ne_src]
    · by_cases hx : k=p.scratch <;> simp_all [tapes,Function.update_apply]

theorem copy_layout (j : Job) (d : Data) (v : Bits) (ht : d.c.tmp=[]) :
    tapes (ports j) (store d) (source j d) [] v=store (setDest j d v) := by
  have hs : source j d=store d (ports j).src := by cases j <;> rfl
  have hx : store d (ports j).scratch=[] := ht
  rw [hs,restored _ _ _ hx]
  cases j <;> funext k <;> rcases k with k | k | k | k
  all_goals first
    | rfl
    | (fin_cases k <;> rfl)

theorem original_dest (j : Job) (d : Data) : setDest j d (dest j d)=d := by
  cases j <;> simp [setDest,dest]

def copy_job (j : Job) (d : Data) (ht : d.c.tmp=[]) :
    Run (cfg (entry j) d) (cfg (next j) (copied j d)) (2*(source j d).length+2) := by
  have run := TreeBudgetStackRoutine.copy_run (ports j) (store d) (L.job j) (next j) false
    program (fun _ => rfl) (source j d) (dest j d)
  simp only [TreeBudgetStackRoutine.conf,copy_layout j d _ ht,original_dest] at run
  exact run

theorem prefix_bank (d : Data) (p : TreeBudgetParentPrefixTM2.K → Bits) : bank prefixW (store d) p=store {d with p:=p} := by
  funext k; cases k <;> rfl
theorem list_bank (d : Data) (t : Fin 7 → Bits) : bank listW (store d) t=store {d with t:=t} := by
  funext k; rcases k with k | k | k <;> rfl
theorem scan_bank (d : Data) (c : TreeBudgetRootFlowScanTM2.Data) : bank scanW (store d) (TreeBudgetRootFlowScanTM2.store c)=store {d with c:=c} := by
  funext k; rcases k with k | k | k <;> rfl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by change Finite Bool; infer_instance
theorem finite_control : Fintype.card K=49 ∧ Fintype.card L=410 ∧ Fintype.card State=6 := by decide

end UAVProof.TreeBudgetRootFlowTM2
