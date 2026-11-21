import LeanCompletion.UAV.TreeBudgetCertificateRecordsSpec
import LeanCompletion.UAV.TreeBudgetEntryLayout
import LeanCompletion.UAV.TreeBudgetTM2CallOn
import LeanCompletion.UAV.TreeBudgetStackRoutine

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition Turing.TM2.Stmt

set_option synthInstance.maxSize 2048
set_option maxRecDepth 10000

inductive Aux | dim | tokens | scratch | amount | dimCopy
  deriving DecidableEq, Fintype
abbrev K := (Fin 7 ⊕ TreeBudgetEntryTM2.K) ⊕ Aux
inductive Job | saveBody | copyTokens | clearMult | incSize | copyDim
  deriving DecidableEq, Fintype
inductive L
  | guardCall (l : Fin 18)
  | entryCall (l : TreeBudgetEntryTM2.L)
  | job (j : Job) (p : TreeBudgetStackRoutine.Phase)
  | tick | returned | row | equalSize | eof | bad
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev gs (i : Fin 7) : K := .inl (.inl i)
abbrev es (i : TreeBudgetEntryTM2.K) : K := .inl (.inr i)
abbrev cursor : K := es (.inl 0)
abbrev rowBody : K := es (.inl 2)
abbrev mult : K := es (.inr ())
abbrev savedBody : K := gs 0
abbrev savedCount : K := gs 4
abbrev ctxStack : K := gs 5

def gw : Wiring (Fin 7) K :=
  ⟨gs,(fun k => match k with | .inl (.inl i) => some i | _ => none),
    by intro k; rfl, by intro r k h; rcases r with (i | e) | a <;> simpa [gs] using h⟩
def ew : Wiring TreeBudgetEntryTM2.K K :=
  ⟨es,(fun k => match k with | .inl (.inr i) => some i | _ => none),
    by intro k; rfl, by intro r k h; rcases r with (i | e) | a <;> simpa [es] using h⟩

def ports : Job → Ports K
  | .saveBody => ⟨savedBody,.inr .scratch,cursor,by decide,by decide,by decide⟩
  | .copyTokens => ⟨savedCount,.inr .scratch,.inr .tokens,by decide,by decide,by decide⟩
  | .clearMult => ⟨mult,.inr .scratch,.inr .dimCopy,by decide,by decide,by decide⟩
  | .incSize => ⟨.inr .amount,.inr .scratch,.inr .dimCopy,by decide,by decide,by decide⟩
  | .copyDim => ⟨.inr .dim,.inr .scratch,.inr .dimCopy,by decide,by decide,by decide⟩

def next : Job → L
  | .saveBody => .job .copyTokens .reverse
  | .copyTokens => .tick
  | .clearMult | .incSize => .row
  | .copyDim => .equalSize

def jump (l : L) : Stmt := TreeBudgetStackRoutine.jump l
def reject : Stmt := load (fun _ => (none,false)) halt

def program : L → Stmt
  | .guardCall l =>
    if l = 9 then jump (.job .saveBody .reverse)
    else if l = 10 then reject
    else compile gw L.guardCall .bad (TreeBudgetListGuardTM2.program l)
  | .entryCall l => compile ew L.entryCall .returned (TreeBudgetEntryTM2.program l)
  | .job j p => TreeBudgetStackRoutine.code (ports j) (L.job j) (next j) false p
  | .tick => pop (.inr .tokens) (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump .eof)
        (jump (.entryCall (TreeBudgetEntryTM2.labels .marker))))
  | .returned => branch Prod.snd (jump (.job .clearMult .clear)) reject
  | .row => pop rowBody (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump (.job .copyDim .reverse))
        (branch (fun s => s.1.getD false)
          (pop rowBody (fun _ b => (b,true))
            (branch (fun s => s.1.isNone) reject (jump .row)))
          (jump (.job .incSize .carry))))
  | .equalSize => pop (.inr .amount) (fun _ b => (b,true))
      (pop (.inr .dimCopy) (fun s b => (s.1,s.1 == b))
        (branch Prod.snd (branch (fun s => s.1.isNone) (jump .tick) (jump .equalSize)) reject))
  | .eof => peek cursor (fun _ b => (none,b.isNone)) halt
  | .bad => reject

def machine : FinTM2 where
  K := K
  k₀ := savedBody
  k₁ := savedBody
  Γ _ := Bool
  Λ := L
  main := .guardCall 0
  σ := State
  initialState := (none,true)
  m := program

def start (n : ℕ) (y ctx : Bits) : Cfg :=
  ⟨some machine.main,(none,true), fun k =>
    if k = savedBody then y else if k = ctxStack then ctx
    else if k = .inr .dim then n.bits else []⟩

/-- Proposed cost of the certificate stage alone. -/
def recordBound (w d : ℕ) : ℕ :=
  8*(w+1)^2 + 24*w*(w+1)^2 + 64*(w+1)*(w+d+1)

/-- Goal for the general run proof. Defining this proposition supplies the interface. -/
def RecordsPolynomialSpec : Prop :=
  ∀ (n : ℕ) (y ctx : Bits), ∃ out : Cfg,
    Nonempty (EvalsToInTime machine.step (start n y ctx) (some out)
      (recordBound y.length n.bits.length)) ∧
    out.l = none ∧ out.var.2 = (decodeCertificate n y).isSome ∧
    out.stk ctxStack = ctx ∧ out.stk (.inr .dim) = n.bits ∧
    ∀ xs : RawCertificate, packet n y = some xs →
      out.stk savedCount = List.replicate xs.length true ∧
      out.stk savedBody = xs.flatMap encodeEntry ∧ out.stk cursor = []

end UAVProof.A4CertRecords
