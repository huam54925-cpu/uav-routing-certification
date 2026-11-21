import LeanCompletion.UAV.TreeBudgetFeeScalingTotal
import LeanCompletion.UAV.TreeBudgetSignedTableRuns
import LeanCompletion.UAV.TreeBudgetRowsCheckTM2
import LeanCompletion.UAV.TreeBudgetColumnCheckTM2

/-! The semantic verifier pipeline: the raw paired entrance, exact fee
scaling, signed-table preparation, all rows and total count, then columns. -/
namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
open Turing.TM2.Stmt
set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev K := A4FeeScaling.K ⊕ ((A4RowsCheck.K ⊕ A4ColumnCheck.K) ⊕ ((Fin 7 ⊕ Fin 7) ⊕ Unit))
abbrev sk (k : A4FeeScaling.K) : K := .inl k
abbrev rk (k : A4RowsCheck.K) : K := .inr (.inl (.inl k))
abbrev ck (k : A4ColumnCheck.K) : K := .inr (.inl (.inr k))
abbrev fk (k : Fin 7) : K := .inr (.inr (.inl (.inl k)))
abbrev bk (k : Fin 7) : K := .inr (.inr (.inl (.inr k)))
abbrev scratch : K := .inr (.inr (.inr ()))
abbrev rowReg (k : Fin 35) : K := rk (A4RowsCheck.rs (A4RowCheck.reg k))
abbrev inst (k : A4FeeTailMachine.K) : K := sk (A4FeeScaling.old (A4PairedParser.ik k))
abbrev cert (k : A4CertRecords.K) : K := sk (A4FeeScaling.old (A4PairedParser.ck k))

def sw : Wiring A4FeeScaling.K K :=
  ⟨sk,(fun k => match k with | .inl k => some k | _ => none),
    by intro k; rfl,by intro r k h; cases r <;> simpa [sk] using h⟩
def rw : Wiring A4RowsCheck.K K :=
  ⟨rk,(fun k => match k with | .inr (.inl (.inl k)) => some k | _ => none),
    by intro k; rfl,by intro r k h; rcases r with r|((r|c)|a) <;> simpa [rk] using h⟩
def cw : Wiring A4ColumnCheck.K K :=
  ⟨ck,(fun k => match k with | .inr (.inl (.inr k)) => some k | _ => none),
    by intro k; rfl,by intro r k h; rcases r with r|((r|c)|a) <;> simpa [ck] using h⟩
def fw : Wiring (Fin 7) K :=
  ⟨fk,(fun k => match k with | .inr (.inr (.inl (.inl k))) => some k | _ => none),
    by intro k; rfl,
    by intro r k h; rcases r with r|((r|c)|((f|b)|u)) <;> simpa [fk] using h⟩
def bw : Wiring (Fin 7) K :=
  ⟨bk,(fun k => match k with | .inr (.inr (.inl (.inr k))) => some k | _ => none),
    by intro k; rfl,
    by intro r k h; rcases r with r|((r|c)|((f|b)|u)) <;> simpa [bk] using h⟩
def iw : Wiring K K := ⟨id,some,by intro k; rfl,by intro k i h; simpa using h⟩

inductive PC
  | fees | budget | parents | demands | root | routes | body | markers
  | positive | negative | budgetPositive | budgetNegative
  | columnBody | columnRoot | columnTargets | done
  deriving DecidableEq, Fintype

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,scratch,$d,by decide,by decide,by decide⟩ : Ports K))

def setup : PC → TreeBudgetRegisterTM2.Instr K PC
  | .fees => .copy port(sk (A4FeeScaling.wr .fees),fk 0) false .budget
  | .budget => .copy port(sk (A4FeeScaling.wr .budget),bk 0) false .done
  | .parents => .copy port(inst A4FeeTailMachine.parents,rowReg 0) false .demands
  | .demands => .copy port(inst (.inl TreeBudgetRootFlowTM2.demands),rowReg 1) false .root
  | .root => .copy port(inst (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot)),rowReg 5) false .routes
  | .routes => .copy port(inst (.inl (.inl (.inr (.inr 0)))),rk (A4RowsCheck.ax .routes)) false .body
  | .body => .copy port(cert A4CertRecords.savedBody,rk (A4RowsCheck.ax .body)) false .markers
  | .markers => .copy port(cert A4CertRecords.savedCount,rk (A4RowsCheck.ax .markers)) false .positive
  | .positive => .copy port(fk 4,rowReg 3) false .negative
  | .negative => .copy port(fk 5,rowReg 4) false .budgetPositive
  | .budgetPositive => .read port(bk 4,rowReg 6) .budgetNegative
  | .budgetNegative => .read port(bk 5,rowReg 7) .columnBody
  | .columnBody => .copy port(cert A4CertRecords.savedBody,ck (A4ColumnCheck.wr .body)) false .columnRoot
  | .columnRoot => .copy port(inst (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot)),ck (A4ColumnCheck.wr .root)) false .columnTargets
  | .columnTargets => .copy port(inst (.inl TreeBudgetRootFlowTM2.demands),ck (A4ColumnCheck.wr .targets)) false .done
  | .done => .halt

inductive L
  | scaled (l : A4FeeScaling.Entry.L)
  | scaledReturn
  | load (l : TreeBudgetRegisterTM2.Label PC)
  | splitFees (l : TreeBudgetSignedTableTM2.L)
  | splitBudget (l : TreeBudgetSignedTableTM2.L)
  | prepare (l : TreeBudgetRegisterTM2.Label PC)
  | rows (l : A4RowsCheck.L)
  | rowsReturn
  | columns (l : TreeBudgetSemanticRegisterTM2.Label A4ColumnCheck.PC)
  | done
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
def reject : Statement K L := load (fun _ => (none,false)) halt

def program : L → Statement K L
  | .scaled l => compile sw L.scaled .scaledReturn (A4FeeScaling.Entry.program l)
  | .scaledReturn => branch Prod.snd (TreeBudgetStackRoutine.jump (.load (.pc .fees))) reject
  | .load l => compile iw L.load (.splitFees .sign) (TreeBudgetRegisterTM2.program setup l)
  | .splitFees l => compile fw L.splitFees (.splitBudget .sign) (TreeBudgetSignedTableTM2.program l)
  | .splitBudget l => compile bw L.splitBudget (.prepare (.pc .parents)) (TreeBudgetSignedTableTM2.program l)
  | .prepare l => compile iw L.prepare (.rows A4RowsCheck.machine.main) (TreeBudgetRegisterTM2.program setup l)
  | .rows l => compile rw L.rows .rowsReturn (A4RowsCheck.program l)
  | .rowsReturn => branch Prod.snd (TreeBudgetStackRoutine.jump (.columns A4ColumnCheck.machine.main)) reject
  | .columns l => compile cw L.columns .done (TreeBudgetSemanticRegisterTM2.program A4ColumnCheck.code l)
  | .done => halt

def machine : FinTM2 where
  K := K
  k₀ := sk A4FeeScaling.Entry.machine.k₀
  k₁ := rk (A4RowsCheck.ax .total)
  Γ _ := Bool
  Λ := L
  main := .scaled A4FeeScaling.Entry.machine.main
  σ := State
  initialState := (none,true)
  m := program

def store (saved : A4FeeScaling.K → Bits) (rows : A4RowsCheck.K → Bits)
    (columns : A4ColumnCheck.K → Bits) (fees budget : Fin 7 → Bits) : K → Bits
  | .inl k => saved k
  | .inr (.inl (.inl k)) => rows k
  | .inr (.inl (.inr k)) => columns k
  | .inr (.inr (.inl (.inl k))) => fees k
  | .inr (.inr (.inl (.inr k))) => budget k
  | .inr (.inr (.inr _)) => []

abbrev Run (a b : Cfg) (t : ℕ) := StateTransition.EvalsToInTime machine.step a (some b) t
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) := by
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step u v a b (some c) h g

end UAVProof.A4Verifier
