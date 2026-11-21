import LeanCompletion.UAV.TreeBudgetRegisterRuns
import LeanCompletion.UAV.TreeBudgetParentLookupTM2

namespace UAVProof.A4NaturalLookup
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
abbrev Child := TreeBudgetParentLookupTM2.K
abbrev K := Child ⊕ Fin 4
abbrev table : K := .inr 0
abbrev index : K := .inr 1
abbrev scratch : K := .inr 2
abbrev output : K := .inr 3
abbrev src : K := .inl (.inl 0)
abbrev front : K := .inl (.inl 2)
abbrev digits : K := .inl (.inr true)
def cw : Wiring Child K :=
  ⟨Sum.inl,(fun k => match k with | .inl k => some k | _ => none),
    by intro k; rfl, by intro k i h; cases k <;> simpa using h⟩
def iw : Wiring K K := ⟨id,some,by intro k; rfl,by intro k i h; simpa using h⟩
local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,scratch,$d,by decide,by decide,by decide⟩ : Ports K))
def prep : Fin 3 → TreeBudgetRegisterTM2.Instr K (Fin 3)
  | 0 => .copy port(table,src) false 1
  | 1 => .copy port(index,src) true 2
  | _ => .halt
def clean : Fin 5 → TreeBudgetRegisterTM2.Instr K (Fin 5)
  | 0 => .copy port(digits,output) false 1
  | 1 => .clear port(src,output) 2
  | 2 => .clear port(front,output) 3
  | 3 => .clear port(digits,output) 4
  | _ => .halt
inductive L
  | prepare (l : TreeBudgetRegisterTM2.Label (Fin 3))
  | lookup (l : TreeBudgetParentLookupTM2.L)
  | cleanup (l : TreeBudgetRegisterTM2.Label (Fin 5))
  | done
  deriving DecidableEq, Fintype
abbrev Cfg := Configuration K L
def program : L → Statement K L
  | .prepare l => compile iw L.prepare (.lookup TreeBudgetParentLookupTM2.machine.main)
      (TreeBudgetRegisterTM2.program prep l)
  | .lookup l => compile cw L.lookup (.cleanup (.pc 0)) (TreeBudgetParentLookupTM2.program l)
  | .cleanup l => compile iw L.cleanup .done (TreeBudgetRegisterTM2.program clean l)
  | .done => .halt
def machine : FinTM2 where
  K := K
  k₀ := table
  k₁ := output
  Γ _ := Bool
  Λ := L
  main := .prepare (.pc 0)
  σ := State
  initialState := (none,true)
  m := program
def store (t i s f d o : Bits) : K → Bits
  | .inr k => match k.val with | 0 => t | 1 => i | 3 => o | _ => []
  | .inl (.inl k) => match k.val with | 0 => s | 2 => f | _ => []
  | .inl (.inr b) => if b then d else []
def start (t i : Bits) : Cfg := ⟨some machine.main,(none,true),store t i [] [] [] []⟩
def stopped (t i o : Bits) : Cfg := ⟨none,(none,true),store t i [] [] [] o⟩
abbrev Run (a b : Cfg) (n : ℕ) := StateTransition.EvalsToInTime machine.step a (some b) n
end UAVProof.A4NaturalLookup
