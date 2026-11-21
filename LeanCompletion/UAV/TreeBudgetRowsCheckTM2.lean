import LeanCompletion.UAV.TreeBudgetRowCheckTM2
import LeanCompletion.UAV.TreeBudgetEntryLayout

/-! Traverse a parsed record table in its saved order. The record markers
drive the loop; multiplicities are added in binary and never expanded. -/
namespace UAVProof.A4RowsCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
open Turing.TM2.Stmt
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

inductive Aux
  | body | markers | todo | routes | total | sum | scratch | spare
  | cmp0 | cmp1 | cmp2 | cmp3
  deriving DecidableEq, Fintype

abbrev K := (TreeBudgetEntryTM2.K ⊕ A4RowCheck.K) ⊕ Aux
abbrev es (k : TreeBudgetEntryTM2.K) : K := .inl (.inl k)
abbrev rs (k : A4RowCheck.K) : K := .inl (.inr k)
abbrev ax (k : Aux) : K := .inr k

def ew : Wiring TreeBudgetEntryTM2.K K :=
  ⟨es,(fun k => match k with | .inl (.inl k) => some k | _ => none),
    by intro k; rfl,
    by intro r k h; rcases r with (i|j)|a <;> simpa [es] using h⟩

def rw : Wiring A4RowCheck.K K :=
  ⟨rs,(fun k => match k with | .inl (.inr k) => some k | _ => none),
    by intro k; rfl,
    by intro r k h; rcases r with (i|j)|a <;> simpa [rs] using h⟩

def addPut (k : Fin 4) : K := match k.val with
  | 0 => ax .total | 1 => es (.inr ()) | 2 => ax .spare | _ => ax .sum
def addGet : K → Option (Fin 4)
  | .inl (.inl (.inr ())) => some 1
  | .inr .total => some 0 | .inr .sum => some 3 | .inr .spare => some 2
  | _ => none
def aw : Wiring (Fin 4) K where
  put := addPut
  get := addGet
  get_put := by decide
  get_eq := by
    intro r k h
    rcases r with ((i|u)|j)|a
    · fin_cases i <;> simp [addGet] at h
    · cases u; fin_cases k <;> simpa [addGet,addPut,es] using h
    · simp [addGet] at h
    · cases a <;> fin_cases k <;> simpa [addGet,addPut,ax] using h

def cmpPut (k : Fin 4) : K := ax <| match k.val with
  | 0 => .cmp0 | 1 => .cmp1 | 2 => .cmp2 | _ => .cmp3
def cmpGet : K → Option (Fin 4)
  | .inr .cmp0 => some 0 | .inr .cmp1 => some 1
  | .inr .cmp2 => some 2 | .inr .cmp3 => some 3 | _ => none
def cw : Wiring (Fin 4) K where
  put := cmpPut
  get := cmpGet
  get_put := by decide
  get_eq := by
    intro r k h
    cases r with
    | inl r => simp [cmpGet] at h
    | inr a => cases a <;> fin_cases k <;> simpa [cmpGet,cmpPut,ax] using h

inductive Job
  | copyBody | copyMarkers | copyRow | clearEntryRow
  | copySum | clearSum | clearRow
  | totalLeft | routesRight | routesLeft | totalRight
  deriving DecidableEq, Fintype

inductive L
  | entryCall (l : TreeBudgetEntryTM2.L)
  | rowCall (l : TreeBudgetSemanticRegisterTM2.Label A4RowCheck.PC)
  | addCall (l : Fin 3)
  | compareCall (reverse : Bool) (l : Unit)
  | job (j : Job) (p : TreeBudgetStackRoutine.Phase)
  | tick | entryDone | rowStart | rowDone | addStart | addDone
  | compareDone (reverse : Bool) | bad | good
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L

def ports : Job → Ports K
  | .copyBody => ⟨ax .body,ax .scratch,es (.inl 0),by decide,by decide,by decide⟩
  | .copyMarkers => ⟨ax .markers,ax .scratch,ax .todo,by decide,by decide,by decide⟩
  | .copyRow => ⟨es (.inl 2),ax .scratch,rs (A4RowCheck.reg 2),by decide,by decide,by decide⟩
  | .clearEntryRow => ⟨es (.inl 2),ax .scratch,ax .spare,by decide,by decide,by decide⟩
  | .copySum => ⟨ax .sum,ax .scratch,ax .total,by decide,by decide,by decide⟩
  | .clearSum => ⟨ax .sum,ax .scratch,ax .spare,by decide,by decide,by decide⟩
  | .clearRow => ⟨rs (A4RowCheck.reg 2),ax .scratch,ax .spare,by decide,by decide,by decide⟩
  | .totalLeft => ⟨ax .total,ax .scratch,ax .cmp0,by decide,by decide,by decide⟩
  | .routesRight => ⟨ax .routes,ax .scratch,ax .cmp1,by decide,by decide,by decide⟩
  | .routesLeft => ⟨ax .routes,ax .scratch,ax .cmp0,by decide,by decide,by decide⟩
  | .totalRight => ⟨ax .total,ax .scratch,ax .cmp1,by decide,by decide,by decide⟩

def next : Job → L
  | .copyBody => .job .copyMarkers .reverse
  | .copyMarkers => .tick
  | .copyRow => .job .clearEntryRow .clear
  | .clearEntryRow => .rowStart
  | .copySum => .job .clearSum .clear
  | .clearSum => .job .clearRow .clear
  | .clearRow => .tick
  | .totalLeft => .job .routesRight .reverse
  | .routesRight => .compareCall false ()
  | .routesLeft => .job .totalRight .reverse
  | .totalRight => .compareCall true ()

def jump (l : L) : Stmt := TreeBudgetStackRoutine.jump l
def reject : Stmt := load (fun _ => (none,false)) halt

def program : L → Stmt
  | .entryCall l => compile ew L.entryCall .entryDone (TreeBudgetEntryTM2.program l)
  | .rowCall l => compile rw L.rowCall .rowDone
      (TreeBudgetSemanticRegisterTM2.program A4RowCheck.instructions l)
  | .addCall l => compile aw L.addCall .addDone (TreeBudgetAddWordsTM2.program l)
  | .compareCall rev l => compile cw (L.compareCall rev) (.compareDone rev)
      (TreeBudgetLeWordsTM2.program l)
  | .job j p => TreeBudgetStackRoutine.code (ports j) (L.job j) (next j) false p
  | .tick => pop (ax .todo) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump (.job .totalLeft .reverse))
        (jump (.entryCall TreeBudgetEntryTM2.machine.main)))
  | .entryDone => branch Prod.snd (jump (.job .copyRow .reverse)) reject
  | .rowStart => jump (.rowCall A4RowCheck.machine.main)
  | .rowDone => branch Prod.snd (jump .addStart) reject
  | .addStart => load (fun _ => (none,false)) (goto fun _ => .addCall 0)
  | .addDone => jump (.job .copySum .reverse)
  | .compareDone rev => pop (ax .cmp3) (fun _ b => (b,true))
      (branch (fun s => s.1.getD false)
        (jump (if rev then .good else .job .routesLeft .reverse)) reject)
  | .bad => reject
  | .good => load (fun _ => (none,true)) halt

def machine : FinTM2 where
  K := K
  k₀ := ax .body
  k₁ := ax .total
  Γ _ := Bool
  Λ := L
  main := .job .copyBody .reverse
  σ := State
  initialState := (none,true)
  m := program

/-- A row's ten saved registers form immutable caller context, except that
register 2 is loaded with the next row and emptied after its successful call. -/
structure Data where
  rowSaved : A4RowCheck.K → Bits
  body : Bits := []
  markers : Bits := []
  routes : Bits := []
  todo : Bits := []
  cursor : Bits := []
  entryRow : Bits := []
  mult : Bits := []
  total : Bits := []
  sum : Bits := []
  scratch : Bits := []
  spare : Bits := []
  cmp0 : Bits := []
  cmp1 : Bits := []
  cmp2 : Bits := []
  cmp3 : Bits := []

def store (d : Data) : K → Bits
  | .inl (.inl (.inl i)) => match i.val with | 0 => d.cursor | 2 => d.entryRow | _ => []
  | .inl (.inl (.inr ())) => d.mult
  | .inl (.inr k) => d.rowSaved k
  | .inr a => match a with
      | .body => d.body | .markers => d.markers | .routes => d.routes
      | .todo => d.todo | .total => d.total | .sum => d.sum
      | .scratch => d.scratch | .spare => d.spare
      | .cmp0 => d.cmp0 | .cmp1 => d.cmp1 | .cmp2 => d.cmp2 | .cmp3 => d.cmp3

def cfg (l : L) (d : Data) : Cfg := ⟨some l,(none,true),store d⟩
def stop (b : Bool) (d : Data) : Cfg := ⟨none,(none,b),store d⟩
abbrev Run (a b : Cfg) (t : ℕ) := StateTransition.EvalsToInTime machine.step a (some b) t

def seq {a b c : Cfg} {x y : ℕ} (h : Run a b x) (g : Run b c y) : Run a c (x+y) :=
  by simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step x y a b (some c) h g

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.A4RowsCheck
