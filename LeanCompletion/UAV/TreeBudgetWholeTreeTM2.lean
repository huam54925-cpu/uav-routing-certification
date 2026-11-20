import LeanCompletion.UAV.TreeBudgetStackRoutine
import LeanCompletion.UAV.TreeBudgetWalkRootContract

/-! One finite-control, Boolean-stack machine enumerates all vertices of a
parsed parent table. Caller-owned copies survive every endpoint call. -/
namespace UAVProof.TreeBudgetWholeTreeTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray
open Turing StateTransition Turing.TM2.Stmt

inductive Job
  | count | queue | rootTable | rootIndex | rootCode | rootClear
  | table | index | ticks | root | clear | increment
  deriving DecidableEq, Fintype
inductive Control | rootCall | rootReturn | test | call | returned
  deriving DecidableEq, Fintype

abbrev K := TreeBudgetWalkRootTM2.K ⊕ Fin 7
abbrev L := (Bool × TreeBudgetWalkRootTM2.L) ⊕ ((Job × TreeBudgetStackRoutine.Phase) ⊕ Control)
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev cursor : K := .inl TreeBudgetWalkRootTM2.cursor
abbrev rootWork : K := .inl TreeBudgetWalkRootTM2.rootCode
abbrev tickWork : K := .inl (.inl TreeBudgetParentWalkTM2.count)
abbrev tableSave : K := .inr 0
abbrev rootSave : K := .inr 1
abbrev tokens : K := .inr 2
abbrev queue : K := .inr 3
abbrev index : K := .inr 4
abbrev temp : K := .inr 5
abbrev context : K := .inr 6

def lab (j : Job) (p : TreeBudgetStackRoutine.Phase) : L := .inr (.inl (j,p))
def ctl (c : Control) : L := .inr (.inr c)
def entry (j : Job) : L := lab j (match j with
  | .count => .count | .rootClear | .clear => .clear | .increment => .carry | _ => .reverse)
def ports (j : Job) : Ports K where
  src := match j with
    | .count | .rootTable | .table => tableSave
    | .queue | .ticks => tokens
    | .rootIndex | .rootCode | .root => rootSave
    | .rootClear | .clear => cursor
    | .index | .increment => index
  scratch := temp
  dst := match j with
    | .count => tokens | .queue => queue
    | .rootTable | .rootIndex | .table | .index => cursor
    | .rootCode | .root => rootWork | .ticks => tickWork
    | .rootClear | .clear | .increment => rootSave
  scratch_ne_src := by cases j <;> decide
  dst_ne_src := by cases j <;> decide
  dst_ne_scratch := by cases j <;> decide
def next : Job → L
  | .count => entry .queue | .queue => entry .rootTable
  | .rootTable => entry .rootIndex | .rootIndex => entry .rootCode
  | .rootCode => ctl .rootCall | .rootClear => ctl .test
  | .table => entry .index | .index => entry .ticks | .ticks => entry .root
  | .root => ctl .call | .clear => entry .increment | .increment => ctl .test
def framed (j : Job) : Bool := j == .index
def jump (l : L) : Stmt := TreeBudgetStackRoutine.jump l

def returnLabel (root : Bool) := ctl (if root then .rootReturn else .returned)
def callLabel (root : Bool) (l : TreeBudgetWalkRootTM2.L) : L := .inl (root,l)
def callEntry (root : Bool) := callLabel root TreeBudgetWalkRootTM2.machine.main

def program : L → Stmt
  | .inl (root,l) => compile (callLabel root) (returnLabel root) (TreeBudgetWalkRootTM2.program l)
  | .inr (.inl (j,p)) => TreeBudgetStackRoutine.code (ports j) (lab j) (next j) (framed j) p
  | .inr (.inr c) => match c with
    | .rootCall => push tickWork (fun _ => true) (jump (callEntry true))
    | .rootReturn => branch Prod.snd (jump (entry .rootClear)) halt
    | .test => TreeBudgetStackRoutine.scan queue
        (load (fun _ => (none,true)) halt) (jump (entry .table))
    | .call => jump (callEntry false)
    | .returned => branch Prod.snd (jump (entry .clear)) halt

def machine : FinTM2 where
  K := K
  k₀ := tableSave
  k₁ := cursor
  Γ _ := Bool
  Λ := L
  main := entry .count
  σ := State
  initialState := (none,true)
  m := program

/-- A proof-facing view of the physical stacks. The machine never stores a
natural number or a list in its finite state. -/
structure Data where
  q : Bits := []
  r : Bits := []
  t : Bits := []
  body : Bits := []
  root : Bits := []
  tokens : Bits := []
  todo : Bits := []
  idx : Bits := []
  tmp : Bits := []
  ctx : Bits := []

def saved (d : Data) (i : Fin 7) : Bits := match i.val with
  | 0 => d.body | 1 => d.root | 2 => d.tokens | 3 => d.todo
  | 4 => d.idx | 5 => d.tmp | _ => d.ctx
def store (d : Data) : K → Bits :=
  banks (TreeBudgetWalkRootTM2.start d.t d.q d.r []).stk (saved d)
def cfg (l : L) (d : Data) : Cfg := ⟨some l,(none,true),store d⟩
def stop (d : Data) (b : Bool) : Cfg := ⟨none,(none,b),store d⟩
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n

def initial {n : ℕ} (P : ParentArray n) (ctx : Bits) : Data :=
  {body := TreeBudgetParentWalkTM2.body P,root := encodeNat P.root.val,ctx := ctx}
def start {n : ℕ} (P : ParentArray n) (ctx : Bits) : Cfg := cfg (entry .count) (initial P ctx)
def ready {n : ℕ} (P : ParentArray n) (ctx : Bits) (i left : ℕ) : Data :=
  {initial P ctx with tokens := List.replicate n true,todo := List.replicate left true,idx := i.bits}

/-- Caller-owned data to retain at both successful and rejecting exits. -/
def Preserved {n : ℕ} (P : ParentArray n) (ctx : Bits) (c : Cfg) : Prop :=
  c.stk tableSave = TreeBudgetParentWalkTM2.body P ∧
  c.stk rootSave = encodeNat P.root.val ∧ c.stk context = ctx

def source (j : Job) (d : Data) : Bits := match j with
  | .count | .rootTable | .table => d.body
  | .queue | .ticks => d.tokens
  | .rootIndex | .rootCode | .root => d.root
  | .rootClear | .clear => d.q
  | .index | .increment => d.idx
def dest (j : Job) (d : Data) : Bits := match j with
  | .count => d.tokens | .queue => d.todo
  | .rootTable | .rootIndex | .table | .index => d.q
  | .rootCode | .root => d.r | .ticks => d.t
  | .rootClear | .clear | .increment => d.root
def replace (j : Job) (d : Data) (s t a : Bits) : Data := match j with
  | .count => {d with body := s,tmp := t,tokens := a}
  | .queue => {d with tokens := s,tmp := t,todo := a}
  | .rootTable | .table => {d with body := s,tmp := t,q := a}
  | .rootIndex => {d with root := s,tmp := t,q := a}
  | .rootCode | .root => {d with root := s,tmp := t,r := a}
  | .rootClear | .clear => {d with q := s,tmp := t,root := a}
  | .index => {d with idx := s,tmp := t,q := a}
  | .ticks => {d with tokens := s,tmp := t,t := a}
  | .increment => {d with idx := s,tmp := t,root := a}

theorem replace_original (j : Job) (d : Data) : replace j d (source j d) d.tmp (dest j d) = d := by
  cases j <;> rfl

theorem tapes_replace (j : Job) (d : Data) (s t a : Bits) :
    tapes (ports j) (store d) s t a = store (replace j d s t a) := by
  cases j <;> funext k <;> rcases k with (((i | b) | u) | v) | z
  all_goals first
    | fin_cases i <;> rfl
    | cases b <;> rfl
    | cases u <;> rfl
    | cases v <;> rfl
    | fin_cases z <;> rfl

theorem conf_replace (j : Job) (d : Data) (l : L) (s t a : Bits) :
    TreeBudgetStackRoutine.conf (ports j) (store d) l s t a = cfg l (replace j d s t a) := by
  simp only [TreeBudgetStackRoutine.conf,cfg,tapes_replace]

def copied (j : Job) (d : Data) :=
  replace j d (source j d) [] ((if framed j then word (source j d) else source j d) ++ dest j d)

def copy_job (j : Job) (d : Data) (ht : d.tmp = []) :
    Run (cfg (lab j .reverse) d) (cfg (next j) (copied j d)) (2*(source j d).length+2) := by
  have h := TreeBudgetStackRoutine.copy_run (ports j) (store d) (lab j) (next j) (framed j)
    program (fun _ => rfl) (source j d) (dest j d)
  rw [conf_replace,conf_replace,← ht,replace_original] at h
  simpa only [copied,ht] using h

def count_job (d : Data) (xs : List ℕ) (hs : d.body = xs.flatMap encodeNat) (ht : d.tmp = []) :
    Run (cfg (entry .count) d)
      (cfg (entry .queue) {d with tokens := List.replicate xs.length true ++ d.tokens})
      (2*d.body.length+2) := by
  have h := TreeBudgetStackRoutine.count_run (ports .count) (store d) (lab .count) (next .count) false
    program (fun _ => rfl) xs d.tokens
  rw [conf_replace,conf_replace,← hs,← ht] at h
  exact h

def clear_job (j : Job) (d : Data) :
    Run (cfg (lab j .clear) d)
      (cfg (next j) (replace j d [] d.tmp (dest j d))) ((source j d).length+1) := by
  have h := TreeBudgetStackRoutine.clear_run (ports j) (store d) (lab j) (next j) (framed j)
    program (fun _ => rfl) (source j d) d.tmp (dest j d)
  rw [conf_replace,conf_replace,replace_original] at h
  exact h

def increment_job (d : Data) (ht : d.tmp = []) :
    Run (cfg (entry .increment) d)
      (cfg (ctl .test) {d with idx := TreeBudgetStackRoutine.increment d.idx}) (2*d.idx.length+2) := by
  have h := TreeBudgetStackRoutine.increment_run (ports .increment) (store d) (lab .increment)
    (next .increment) false program (fun _ => rfl) d.idx [] d.root
  rw [conf_replace,conf_replace] at h
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at h
  rw [← ht] at h
  exact h

end UAVProof.TreeBudgetWholeTreeTM2
