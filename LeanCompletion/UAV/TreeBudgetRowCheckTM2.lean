import LeanCompletion.UAV.TreeBudgetSemanticRegisterTM2
import LeanCompletion.UAV.TreeBudgetNaturalLookupTM2

/-! The complete finite instruction table for one parsed row. Original tables,
root, budget, caller context and record suffix are persistent registers. Every
failure rejoins the same bounded workspace cleanup as success. -/
namespace UAVProof.A4RowCheck
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
open TreeBudgetSemanticRegisterTM2

abbrev K := A4NaturalLookup.Child ⊕ Fin 35
abbrev reg (i : Fin 35) : K := .inr i
/- Registers 0..9 are persistent: P,H,row,A+,A-,root,T+,T-,ctx,suffix.
10..14 are scan cursors; 15..19 are their current decoded fields.
20,21 are signed cost accumulators, 22 root flow, 23 lookup output;
24 copy scratch, 25 lookup scratch, 26..30 weighted bank, 31..34 compare. -/

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,reg 24,$d,by decide,by decide,by decide⟩ : Ports K))

def mulPut (which : Fin 3) (k : Fin 6) : K := reg <| match k.val with
  | 0 => 26 | 1 => 27 | 2 => ⟨20+which.val,by omega⟩
  | 3 => 28 | 4 => 29 | _ => 30
def mulGet (which : Fin 3) : K → Option (Fin 6)
  | .inl _ => none
  | .inr k => if k.val=20+which.val then some 2 else match k.val with
      | 26 => some 0 | 27 => some 1 | 28 => some 3 | 29 => some 4
      | 30 => some 5 | _ => none
def mw (which : Fin 3) : Wiring (Fin 6) K where
  put := mulPut which
  get := mulGet which
  get_put := by fin_cases which <;> decide
  get_eq := by
    intro r k h
    cases r with
    | inl r => simp [mulGet] at h
    | inr r => fin_cases which <;> fin_cases r <;> fin_cases k <;> simp_all [mulGet,mulPut,reg]

def cmpPut (k : Fin 4) : K := reg ⟨31+k.val,by omega⟩
def cmpGet : K → Option (Fin 4)
  | .inl _ => none
  | .inr k => match k.val with
      | 31 => some 0 | 32 => some 1 | 33 => some 2 | 34 => some 3 | _ => none
def cw : Wiring (Fin 4) K where
  put := cmpPut
  get := cmpGet
  get_put := by decide
  get_eq := by
    intro r k h
    cases r with
    | inl r => simp [cmpGet] at h
    | inr r => fin_cases r <;> fin_cases k <;> simp_all [cmpGet,cmpPut,reg]

def lookupPut (which : Fin 3) (atRoot : Bool) : A4NaturalLookup.K → K
  | .inl k => .inl k
  | .inr k => reg <| match k.val with
      | 0 => ⟨2+which.val,by omega⟩
      | 1 => if atRoot then 5 else 15
      | 2 => 25 | _ => 23
def lookupGet (which : Fin 3) (atRoot : Bool) : K → Option A4NaturalLookup.K
  | .inl k => some (.inl k)
  | .inr k => if k.val=2+which.val then some (.inr 0)
      else if k.val=(if atRoot then 5 else 15) then some (.inr 1)
      else match k.val with | 25 => some (.inr 2) | 23 => some (.inr 3) | _ => none
def lw (which : Fin 3) (atRoot : Bool) : Wiring A4NaturalLookup.K K where
  put := lookupPut which atRoot
  get := lookupGet which atRoot
  get_put := by
    intro k
    cases k with
    | inl k => rfl
    | inr k => fin_cases which <;> cases atRoot <;> fin_cases k <;> rfl
  get_eq := by
    intro r k h
    cases r with
    | inl r =>
      simp only [lookupGet,Option.some.injEq] at h
      subst k
      rfl
    | inr r =>
      cases k with
      | inl k => fin_cases which <;> cases atRoot <;> fin_cases r <;> simp_all [lookupGet]
      | inr k => fin_cases which <;> cases atRoot <;> fin_cases r <;> fin_cases k <;>
          simp_all [lookupGet,lookupPut,reg]

inductive PC
  | rootLookup | rootTest | rootClear
  | prepP | prepH | prepRow | prepPos | prepNeg | prepBudgetPos | prepBudgetNeg
  | loop | readP | readH | readRow | readPos | readNeg
  | capU | capH | capCompare
  | selfPosU | selfPosH | selfPosRun | selfNegU | selfNegH | selfNegRun
  | parentLeft | rootRight | parentLEroot | rootLeft | parentRight | rootLEparent
  | rootAddU | rootAddOne | rootAddRun
  | parentNonzero | parentLookup | parentTest | parentClear
  | parentPosLookup | parentPosU | parentPosH | parentPosClear | parentPosRun
  | parentNegLookup | parentNegU | parentNegH | parentNegClear | parentNegRun
  | roundClear (i : Fin 5)
  | massLeft | oneRight | massLEone | oneLeft | massRight | oneLEmass
  | budgetLeft | budgetRight | budgetCompare
  | cleanup (good : Bool) (i : Fin 25)
  | finish (good : Bool)
  deriving DecidableEq, Fintype

def bad : PC := .cleanup false 0
def good : PC := .cleanup true 0

def instructions : PC → Instr K PC
  | .rootLookup => .lookup (lw 0 true) .rootTest
  | .rootTest => .test (reg 23) .rootClear bad
  | .rootClear => .clear port(reg 23,reg 26) .prepP
  | .prepP => .copy port(reg 0,reg 10) false .prepH
  | .prepH => .copy port(reg 1,reg 11) false .prepRow
  | .prepRow => .copy port(reg 2,reg 12) false .prepPos
  | .prepPos => .copy port(reg 3,reg 13) false .prepNeg
  | .prepNeg => .copy port(reg 4,reg 14) false .prepBudgetPos
  | .prepBudgetPos => .copy port(reg 7,reg 20) false .prepBudgetNeg
  | .prepBudgetNeg => .copy port(reg 6,reg 21) false .loop
  | .loop => .test (reg 10) .massLeft .readP
  | .readP => .read port(reg 10,reg 15) .readH
  | .readH => .read port(reg 11,reg 16) .readRow
  | .readRow => .read port(reg 12,reg 17) .readPos
  | .readPos => .read port(reg 13,reg 18) .readNeg
  | .readNeg => .read port(reg 14,reg 19) .capU
  | .capU => .copy port(reg 17,reg 31) false .capH
  | .capH => .copy port(reg 16,reg 32) false .capCompare
  | .capCompare => .le cw .selfPosU bad
  | .selfPosU => .copy port(reg 17,reg 26) false .selfPosH
  | .selfPosH => .copy port(reg 18,reg 27) false .selfPosRun
  | .selfPosRun => .weighted (mw 0) .selfNegU
  | .selfNegU => .copy port(reg 17,reg 26) false .selfNegH
  | .selfNegH => .copy port(reg 19,reg 27) false .selfNegRun
  | .selfNegRun => .weighted (mw 1) .parentLeft
  | .parentLeft => .copy port(reg 15,reg 31) false .rootRight
  | .rootRight => .copy port(reg 5,reg 32) false .parentLEroot
  | .parentLEroot => .le cw .rootLeft .parentNonzero
  | .rootLeft => .copy port(reg 5,reg 31) false .parentRight
  | .parentRight => .copy port(reg 15,reg 32) false .rootLEparent
  | .rootLEparent => .le cw .rootAddU .parentNonzero
  | .rootAddU => .copy port(reg 17,reg 26) false .rootAddOne
  | .rootAddOne => .push (reg 27) true .rootAddRun
  | .rootAddRun => .weighted (mw 2) (.roundClear 0)
  | .parentNonzero => .test (reg 17) (.roundClear 0) .parentLookup
  | .parentLookup => .lookup (lw 0 false) .parentTest
  | .parentTest => .test (reg 23) bad .parentClear
  | .parentClear => .clear port(reg 23,reg 26) .parentPosLookup
  | .parentPosLookup => .lookup (lw 1 false) .parentPosU
  | .parentPosU => .copy port(reg 17,reg 26) false .parentPosH
  | .parentPosH => .copy port(reg 23,reg 27) false .parentPosClear
  | .parentPosClear => .clear port(reg 23,reg 31) .parentPosRun
  | .parentPosRun => .weighted (mw 0) .parentNegLookup
  | .parentNegLookup => .lookup (lw 2 false) .parentNegU
  | .parentNegU => .copy port(reg 17,reg 26) false .parentNegH
  | .parentNegH => .copy port(reg 23,reg 27) false .parentNegClear
  | .parentNegClear => .clear port(reg 23,reg 31) .parentNegRun
  | .parentNegRun => .weighted (mw 1) (.roundClear 0)
  | .roundClear i => .clear
      ⟨reg ⟨15+i.val,by omega⟩,reg 24,reg 26,
        by simp only [reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega,
        by simp only [reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega,by decide⟩
      (if h : i.val+1<5 then .roundClear ⟨i.val+1,h⟩ else .loop)
  | .massLeft => .copy port(reg 22,reg 31) false .oneRight
  | .oneRight => .push (reg 32) true .massLEone
  | .massLEone => .le cw .oneLeft bad
  | .oneLeft => .push (reg 31) true .massRight
  | .massRight => .copy port(reg 22,reg 32) false .oneLEmass
  | .oneLEmass => .le cw .budgetLeft bad
  | .budgetLeft => .copy port(reg 20,reg 31) false .budgetRight
  | .budgetRight => .copy port(reg 21,reg 32) false .budgetCompare
  | .budgetCompare => .le cw good bad
  | .cleanup b i => .clear
      ⟨reg ⟨10+i.val,by omega⟩,.inl (.inr false),reg 9,
        by simp [reg],by simp only [reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega,by simp [reg]⟩
      (if h : i.val+1<25 then .cleanup b ⟨i.val+1,h⟩ else .finish b)
  | .finish b => if b then .halt else .fail

def machine : FinTM2 where
  K := K
  k₀ := reg 2
  k₁ := reg 22
  Γ _ := Bool
  Λ := Label PC
  main := .pc .rootLookup
  σ := State
  initialState := (none,true)
  m := program instructions

def store (P H row plus minus root tplus tminus ctx suffix : Bits) : K → Bits
  | .inl _ => []
  | .inr k => match k.val with
      | 0 => P | 1 => H | 2 => row | 3 => plus | 4 => minus | 5 => root
      | 6 => tplus | 7 => tminus | 8 => ctx | 9 => suffix | _ => []

def start (P H row plus minus root tplus tminus ctx suffix : Bits) : Configuration K (Label PC) :=
  cfg .rootLookup (store P H row plus minus root tplus tminus ctx suffix)

def stopped (b : Bool) (P H row plus minus root tplus tminus ctx suffix : Bits) :
    Configuration K (Label PC) :=
  ⟨none,(none,b),store P H row plus minus root tplus tminus ctx suffix⟩

end UAVProof.A4RowCheck
