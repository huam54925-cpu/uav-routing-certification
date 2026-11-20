import LeanCompletion.UAV.TreeBudgetFeeTailSpec

/-! Composed instance-stage FinTM2. The suffix is consumed in place.
The result is returned in the configuration flag; successful output stacks retain
canonical field bodies in forward order and the caller context is preserved.
The final standard-verifier `haltList` cleanup is a separate stage. -/
namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
open Turing.TM2.Stmt

set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000

inductive FeeField | nums | dens | bnum | bden
  deriving DecidableEq, Fintype
inductive Aux | tmp | expected | ticks | rev | result (f : FeeField)
  deriving DecidableEq, Fintype
abbrev K := TreeBudgetRootFlowTM2.K ⊕ Aux
inductive L
  | prefix (l : TreeBudgetRootFlowTM2.L)
  | afterPrefix
  | dimension (g : Bool) (p : TreeBudgetStackRoutine.Phase)
  | header (g : Bool)
  | count (g : Bool) (p : TreeBudgetStackRoutine.Phase)
  | more (g : Bool)
  | sign (f : FeeField)
  | marker (f : FeeField) (endOK : Bool)
  | digit (f : FeeField)
  | flush (f : FeeField)
  | eof | bad
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev src : K := .inl TreeBudgetRootFlowTM2.suffix
abbrev dimension : K := .inl (.inl TreeBudgetParentPrefixTM2.dimension)
abbrev parents : K := .inl (.inl TreeBudgetParentPrefixTM2.parsedBody)
abbrev context : K := .inl TreeBudgetRootFlowTM2.context

def prefixW : Wiring TreeBudgetRootFlowTM2.K K :=
  ⟨Sum.inl, (fun k => match k with | .inl i => some i | _ => none), by intro k; rfl,
    by intro r k h; cases r <;> simpa using h⟩
def dimPorts : Ports K := ⟨dimension,.inr .tmp,.inr .expected, by decide, by decide, by decide⟩
def countPorts : Ports K := ⟨parents,.inr .tmp,.inr .ticks, by decide, by decide, by decide⟩
def go (l : L) : Stmt := goto (fun _ => l)
def doneField : FeeField → L
  | .nums => .more false | .dens => .more true
  | .bnum => .flush .bnum | .bden => .flush .bden
def nextGroup : FeeField → L
  | .nums => .dimension true .reverse | .dens => .sign .bnum
  | .bnum => .marker .bden false | .bden => .eof

/-- Pop one wire bit, save it on the reversed-output stack, then dispatch. -/
def readBit (onZero onOne : L) : Stmt :=
  pop src (fun _ b => (b,true))
    (branch (fun s => s.1.isNone) (go .bad)
      (push (.inr .rev) (fun s => s.1.getD false)
        (branch (fun s => s.1.getD false) (go onOne) (go onZero))))

def program : L → Stmt
  | .prefix l => compile prefixW L.prefix .afterPrefix (TreeBudgetRootFlowTM2.program l)
  | .afterPrefix => branch Prod.snd (TreeBudgetStackRoutine.jump (.dimension false .reverse)) (go .bad)
  | .dimension g ph =>
      TreeBudgetStackRoutine.code dimPorts (L.dimension g) (.header g) true ph
  | .header g => pop (.inr .expected) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (go (.count g .count))
        (pop src (fun s b => (none,s.1 == b))
          (branch Prod.snd (go (.header g)) (go .bad))))
  | .count g ph => TreeBudgetStackRoutine.code countPorts (L.count g) (.more g) false ph
  | .more g => pop (.inr .ticks) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (go (.flush (if g then .dens else .nums)))
        (go (if g then .marker .dens false else .sign .nums)))
  | .sign f => readBit (.marker f true) (.marker f false)
  | .marker f ok => readBit (if ok then doneField f else .bad) (.digit f)
  | .digit f => readBit (.marker f false) (.marker f true)
  | .flush f => pop (.inr .rev) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (go (nextGroup f))
        (push (.inr (.result f)) (fun s => s.1.getD false) (go (.flush f))))
  | .eof => peek src (fun _ b => (none,b.isNone)) halt
  | .bad => load (fun _ => (none,false)) halt

def machine : FinTM2 where
  K := K
  k₀ := .inl TreeBudgetRootFlowTM2.machine.k₀
  k₁ := .inr (.result .bden)
  Γ _ := Bool
  Λ := L
  main := .prefix TreeBudgetRootFlowTM2.machine.main
  σ := State
  initialState := TreeBudgetRootFlowTM2.machine.initialState
  m := program

def start (x ctx : Bits) : Cfg :=
  embed prefixW L.prefix .afterPrefix (fun _ => []) (TreeBudgetRootFlowTM2.start x ctx)

/-- A separate harness can start at the saved-fields interface. -/
def prepared (n : ℕ) (ps : List ℕ) (t ctx : Bits) : Cfg :=
  ⟨some (.dimension false .reverse),(none,true),fun k =>
    if k = dimension then n.bits else if k = parents then ps.flatMap encodeNat
    else if k = src then t else if k = context then ctx else []⟩

def observe : ℕ → Cfg → Option Cfg
  | 0, _ => none
  | fuel+1, c => match machine.step c with
    | none => some c
    | some d => observe fuel d

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem finite_control : Fintype.card K=57 ∧ Fintype.card L=461 ∧ Fintype.card State=6 := by decide

end UAVProof.A4FeeTailMachine
