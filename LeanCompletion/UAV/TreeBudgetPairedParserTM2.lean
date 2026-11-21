import LeanCompletion.UAV.TreeBudgetPairedParserSpec
import LeanCompletion.UAV.TreeBudgetInstanceTotal
import LeanCompletion.UAV.TreeBudgetCertificateRecordsTotal
import LeanCompletion.UAV.TreeBudgetFrameRunsTM2

/-! One fixed finite machine splits the input pair, calls the complete
instance parser, physically copies its dimension, then calls the records
parser. The two subprograms use disjoint stack banks. -/
namespace UAVProof.A4PairedParser
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition Turing.TM2.Stmt

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000

abbrev K := A4FeeTailMachine.K ⊕ A4CertRecords.K ⊕ Unit
inductive L
  | frame (p : Phase)
  | instanceCall (l : A4FeeTailMachine.L)
  | afterInstance
  | dimension (p : TreeBudgetStackRoutine.Phase)
  | recordsCall (l : A4CertRecords.L)
  | afterRecords | bad
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev ik (k : A4FeeTailMachine.K) : K := .inl k
abbrev ck (k : A4CertRecords.K) : K := .inr (.inl k)
abbrev scratch : K := .inr (.inr ())

def iw : Wiring A4FeeTailMachine.K K :=
  ⟨ik,(fun k => match k with | .inl i => some i | _ => none),
    by intro k; rfl, by intro r k h; rcases r with i | c | u <;> simpa using h⟩
def cw : Wiring A4CertRecords.K K :=
  ⟨ck,(fun k => match k with | .inr (.inl c) => some c | _ => none),
    by intro k; rfl, by intro r k h; rcases r with i | c | u <;> simpa using h⟩

def framePorts : Ports K :=
  ⟨ck A4CertRecords.savedBody,scratch,ik A4FeeTailMachine.machine.k₀,
    by decide,by decide,by decide⟩
def dimPorts : Ports K :=
  ⟨ik A4FeeTailMachine.dimension,scratch,ck (.inr .dim),by decide,by decide,by decide⟩

def program : L → Stmt
  | .frame p => code framePorts L.frame (.instanceCall A4FeeTailMachine.machine.main) .bad false p
  | .instanceCall l => compile iw L.instanceCall .afterInstance (A4FeeTailMachine.program l)
  | .afterInstance => branch Prod.snd (TreeBudgetStackRoutine.jump (.dimension .reverse))
      (load (fun _ => (none,false)) halt)
  | .dimension p => TreeBudgetStackRoutine.code dimPorts L.dimension
      (.recordsCall A4CertRecords.machine.main) false p
  | .recordsCall l => compile cw L.recordsCall .afterRecords (A4CertRecords.program l)
  | .afterRecords => halt
  | .bad => load (fun _ => (none,false)) halt

def machine : FinTM2 where
  K := K
  k₀ := ck A4CertRecords.savedBody
  k₁ := ck A4CertRecords.savedBody
  Γ _ := Bool
  Λ := L
  main := .frame .marker
  σ := State
  initialState := (none,true)
  m := program

def store (i : A4FeeTailMachine.K → Bits) (c : A4CertRecords.K → Bits) (t : Bits := []) : K → Bits
  | .inl k => i k | .inr (.inl k) => c k | .inr (.inr _) => t

def certBase (y : Bits) := (A4CertRecords.start 0 y []).stk
def base (y : Bits) : K → Bits := store (fun _ => []) (certBase y)
def afterInstance (out : A4FeeTailMachine.Cfg) (y : Bits) : Cfg :=
  ⟨some .afterInstance,out.var,store out.stk (certBase y)⟩
def stopped (b : State) (stk : K → Bits) : Cfg := ⟨none,b,stk⟩
def instanceView (out : Cfg) : A4FeeTailMachine.Cfg :=
  ⟨none,out.var,fun k => out.stk (ik k)⟩

abbrev Run (a b : Cfg) (t : ℕ) := EvalsToInTime machine.step a (some b) t
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) :=
  by simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step u v a b (some c) h g

def Saved (x y : Bits) (out : Cfg) : Prop :=
  A4FeeTailMachine.SavedInstance x (instanceView out) ∧
  out.stk (ik A4FeeTailMachine.context)=[] ∧
  ∀ I, TreeBudgetSparseVerifier.parseInstance x=some I →
    out.stk (ik A4FeeTailMachine.dimension)=I.data.n.bits ∧
    out.stk (ck (.inr .dim))=I.data.n.bits ∧
    ∀ xs, A4CertRecords.packet I.data.n y=some xs →
      out.stk (ck A4CertRecords.savedCount)=List.replicate xs.length true ∧
      out.stk (ck A4CertRecords.savedBody)=xs.flatMap TreeBudgetSparseCodec.encodeEntry ∧
      out.stk (ck A4CertRecords.cursor)=[]

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool; infer_instance
theorem finite_control : Fintype.card K=78 ∧ Fintype.card L=552 ∧ Fintype.card State=6 := by decide

end UAVProof.A4PairedParser
