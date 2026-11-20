import LeanCompletion.UAV.TreeBudgetParentPrefixParse
import LeanCompletion.UAV.TreeBudgetCompareRoutine
import LeanCompletion.UAV.TreeBudgetTM2CallRight

/-! Read an actual instance prefix, check every index and its declared dimension,
then call the whole-tree machine. The right bank retains the parsed prefix. -/
namespace UAVProof.TreeBudgetParentPrefixTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open Turing.TM2.Stmt

set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024

inductive Job
  | table | rootFrame | rootDigit | rootBound | body | parentBound | counterDigit | counterBound
  | increment | clear
  deriving DecidableEq, Fintype
inductive Check | root | parent | dimension
  deriving DecidableEq, Fintype
inductive Control | parsed | loop | halt | reject
  deriving DecidableEq, Fintype
inductive L
  | tree : TreeBudgetWholeTreeTM2.L → L
  | parser : TreeBudgetParentPrefixParse.L → L
  | job : Job → TreeBudgetStackRoutine.Phase → L
  | frame : Phase → L
  | beginCompare : Check → L
  | compare : Check → L
  | compared : Check → L
  | control : Control → L
  deriving DecidableEq, Fintype

abbrev K := TreeBudgetWholeTreeTM2.K ⊕ TreeBudgetParentPrefixParse.K
instance decidableStack : DecidableEq K := inferInstanceAs
  (DecidableEq (((((Fin 7 ⊕ Bool) ⊕ Unit) ⊕ Unit) ⊕ Fin 7) ⊕ ((Fin 7 ⊕ Unit) ⊕ Fin 2)))
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev Data := TreeBudgetWholeTreeTM2.Data
abbrev Saved := TreeBudgetParentPrefixParse.K → Bits
abbrev cursor : K := .inl TreeBudgetWholeTreeTM2.cursor
abbrev left : K := .inl TreeBudgetWholeTreeTM2.rootWork
abbrev right : K := .inl TreeBudgetWholeTreeTM2.tickWork
abbrev temp : K := .inl TreeBudgetWholeTreeTM2.temp
abbrev counter : K := .inl TreeBudgetWholeTreeTM2.index
abbrev table : K := .inl TreeBudgetWholeTreeTM2.tableSave
abbrev root : K := .inl TreeBudgetWholeTreeTM2.rootSave
abbrev parsedBody : K := .inr (.inl (.inl 2))
abbrev parsedRoot : K := .inr (.inl (.inr ()))
abbrev dimension : K := .inr (.inr 1)
abbrev context : K := .inr (.inl (.inl 5))
abbrev suffix : K := .inr (.inl (.inl 0))

def entry (j : Job) : L := .job j (match j with
  | .increment => .carry | .clear => .clear | _ => .reverse)
def treeEntry := L.tree TreeBudgetWholeTreeTM2.machine.main
def next : Job → L
  | .table => entry .rootFrame | .rootFrame => entry .rootDigit | .rootDigit => entry .rootBound
  | .rootBound => .beginCompare .root | .body => .control .loop
  | .parentBound => .beginCompare .parent | .counterDigit => entry .counterBound
  | .counterBound => .beginCompare .dimension | .increment => .control .loop | .clear => treeEntry
def equal (c : Check) : Bool := c == .dimension
def after : Check → L
  | .root => entry .body | .parent => entry .increment | .dimension => entry .clear
def framed (j : Job) : Bool := j == .rootFrame
def ports (j : Job) : Ports K where
  src := match j with
    | .table | .body => parsedBody | .rootFrame | .rootDigit => parsedRoot
    | .rootBound | .parentBound | .counterBound => dimension
    | .counterDigit | .increment | .clear => counter
  scratch := temp
  dst := match j with
    | .table => table | .rootFrame | .increment | .clear => root
    | .rootDigit | .counterDigit => left | .rootBound | .parentBound | .counterBound => right
    | .body => cursor
  scratch_ne_src := by cases j <;> decide
  dst_ne_src := by cases j <;> decide
  dst_ne_scratch := by cases j <;> decide
def framePorts : Ports K := ⟨cursor,temp,left,by decide,by decide,by decide⟩
def comparePorts : Ports K := ⟨left,right,counter,by decide,by decide,by decide⟩
def jump (l : L) : Stmt := TreeBudgetStackRoutine.jump l

def program : L → Stmt
  | .tree l => compile L.tree (.control .halt) (TreeBudgetWholeTreeTM2.program l)
  | .parser l => compileRight L.parser (.control .parsed) (TreeBudgetParentPrefixParse.program l)
  | .job j p => TreeBudgetStackRoutine.code (ports j) (L.job j) (next j) (framed j) p
  | .frame p => code framePorts L.frame (entry .parentBound) (.control .reject) true p
  | .beginCompare c => load (fun _ => (none,equal c)) (goto (fun _ => .compare c))
  | .compare c => TreeBudgetCompareRoutine.code comparePorts (.compare c) (.compared c) (equal c)
  | .compared c => branch Prod.snd (jump (after c)) halt
  | .control .parsed => branch Prod.snd (jump (entry .table)) halt
  | .control .loop => peek cursor (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump (entry .counterDigit)) (jump (.frame .marker)))
  | .control .halt => halt
  | .control .reject => load (fun _ => (none,false)) halt

def machine : FinTM2 where
  K := K
  k₀ := suffix
  k₁ := left
  Γ _ := Bool
  Λ := L
  main := .parser TreeBudgetParentPrefixParse.machine.main
  σ := State
  initialState := (none,true)
  m := program

def store (d : Data) (saved : Saved) : K → Bits := banks (TreeBudgetWholeTreeTM2.store d) saved
def cfg (l : L) (d : Data) (saved : Saved) (b : Bool := true) : Cfg :=
  ⟨some l,(none,b),store d saved⟩
def stop (d : Data) (saved : Saved) (b : Bool) : Cfg := ⟨none,(none,b),store d saved⟩
def start (s ctx : Bits) : Cfg := embedRight L.parser (.control .parsed)
  (TreeBudgetWholeTreeTM2.store {}) (TreeBudgetParentPrefixParse.start s ctx)
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n
def kept (saved : Saved) (out : Cfg) : Prop := ∀ k, out.stk (.inr k) = saved k

def source (j : Job) (d : Data) (saved : Saved) : Bits := match j with
  | .table | .body => saved (.inl (.inl 2))
  | .rootFrame | .rootDigit => saved (.inl (.inr ()))
  | .rootBound | .parentBound | .counterBound => saved (.inr 1)
  | .counterDigit | .increment | .clear => d.idx
def dest (j : Job) (d : Data) : Bits := match j with
  | .table => d.body | .rootFrame | .increment | .clear => d.root
  | .rootDigit | .counterDigit => d.r | .rootBound | .parentBound | .counterBound => d.t
  | .body => d.q
def setDest (j : Job) (d : Data) (v : Bits) : Data := match j with
  | .table => {d with body:=v} | .rootFrame | .increment | .clear => {d with root:=v}
  | .rootDigit | .counterDigit => {d with r:=v}
  | .rootBound | .parentBound | .counterBound => {d with t:=v}
  | .body => {d with q:=v}
def copied (j : Job) (d : Data) (saved : Saved) : Data := setDest j d
  ((if framed j then word (source j d saved) else source j d saved) ++ dest j d)

theorem copy_layout (j : Job) (d : Data) (saved : Saved) (out : Bits) (ht : d.tmp=[]) :
    tapes (ports j) (store d saved) (source j d saved) [] out = store (setDest j d out) saved := by
  rcases d with ⟨q,r,t,body,root,tokens,todo,idx,tmp,ctx⟩
  dsimp only at ht
  subst tmp
  cases j <;> funext k <;> rcases k with ((((i | b) | u) | v) | z) | w
  all_goals first
    | fin_cases i <;> rfl
    | cases b <;> rfl
    | cases u <;> rfl
    | cases v <;> rfl
    | fin_cases z <;> rfl
    | (rcases w with (i | u) | z
       · fin_cases i <;> rfl
       · cases u; rfl
       · fin_cases z <;> rfl)

theorem original_dest (j : Job) (d : Data) : setDest j d (dest j d) = d := by cases j <;> rfl

def copy_job (j : Job) (d : Data) (saved : Saved) (ht : d.tmp=[]) :
    Run (cfg (.job j .reverse) d saved) (cfg (next j) (copied j d saved) saved)
      (2*(source j d saved).length+2) := by
  have h := TreeBudgetStackRoutine.copy_run (ports j) (store d saved) (L.job j) (next j)
    (framed j) program (fun _ => rfl) (source j d saved) (dest j d)
  simp only [TreeBudgetStackRoutine.conf,copy_layout j d saved _ ht,original_dest] at h
  exact h

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by change Finite Bool; infer_instance

theorem finite_control : Fintype.card K=28 ∧ Fintype.card L=258 ∧ Fintype.card State=6 := by decide

theorem init_eq (s : Bits) : initList machine s = start s [] := by
  simp only [initList,machine,start,embedRight,TreeBudgetParentPrefixParse.start,
    TreeBudgetParentPrefixParse.atLabel]
  congr 1
  funext k
  rcases k with ((((i | b) | u) | v) | z) | w
  · fin_cases i <;> rfl
  · cases b <;> rfl
  · cases u <;> rfl
  · cases v <;> rfl
  · fin_cases z <;> rfl
  · rcases w with (i | u) | z
    · fin_cases i <;> rfl
    · cases u; rfl
    · fin_cases z <;> rfl

end UAVProof.TreeBudgetParentPrefixTM2
