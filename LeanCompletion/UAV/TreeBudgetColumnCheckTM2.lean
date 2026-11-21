import LeanCompletion.UAV.TreeBudgetSemanticRegisterRuns
import LeanCompletion.UAV.TreeBudgetColumnAccumulator

/-! Fixed-stack rereading of all compressed records for each nonroot column. -/
namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000

inductive R
  | body | tokens | root | targets | ctx
  | index | htail | target | cursor | row | count | coord | acc
  | a | b | c | d | scratch
  deriving DecidableEq, Fintype
abbrev Child := A4NaturalLookup.Child
abbrev K := Child ⊕ R
abbrev wr (r : R) : K := .inr r
abbrev lr (r : Child) : K := .inl r

inductive PC
  | prepare | column | readTarget
  | rootA | rootB | rootLe | rootBackA | rootBackB | rootBackLe
  | records | entry | lookup | update | clearRow
  | sumA | sumB | sumLe | sumBackA | sumBackB | sumBackLe
  | clearSum | clearTarget | increment | finish | done | bad
  deriving DecidableEq, Fintype

def lw : Wiring A4NaturalLookup.K K :=
  ⟨(fun k => match k with
    | .inl c => lr c
    | .inr i => match i.val with
      | 0 => wr .row | 1 => wr .index | 2 => wr .scratch | _ => wr .coord),
   (fun k => match k with
    | .inl c => some (.inl c)
    | .inr .row => some (.inr 0) | .inr .index => some (.inr 1)
    | .inr .scratch => some (.inr 2) | .inr .coord => some (.inr 3)
    | _ => none),
   by intro k; cases k with | inl c => rfl | inr i => fin_cases i <;> rfl,
   by intro k i h; cases k with
      | inl c => simp only [Option.some.injEq] at h; subst i; rfl
      | inr r => cases r <;> simp_all <;> subst i <;> rfl⟩

def mw : Wiring (Fin 6) K :=
  ⟨(fun i => wr (![R.count,R.coord,R.acc,R.a,R.b,R.ctx] i)),
    (fun k => match k with
      | .inr .count => some 0 | .inr .coord => some 1 | .inr .acc => some 2
      | .inr .a => some 3 | .inr .b => some 4 | .inr .ctx => some 5 | _ => none),
    by intro i; fin_cases i <;> rfl,
    by intro k i h; cases k with
       | inl c => simp_all
       | inr r => cases r <;> simp_all <;> subst i <;> rfl⟩

def cw : Wiring (Fin 4) K :=
  ⟨(fun i => wr (![R.a,R.b,R.c,R.d] i)),
    (fun k => match k with
      | .inr .a => some 0 | .inr .b => some 1 | .inr .c => some 2 | .inr .d => some 3
      | _ => none),
    by intro i; fin_cases i <;> rfl,
    by intro k i h; cases k with
       | inl c => simp_all
       | inr r => cases r <;> simp_all <;> subst i <;> rfl⟩

def ew : Wiring TreeBudgetEntryTM2.K K :=
  ⟨(fun k => match k with
    | .inl i => match i.val with
      | 0 => wr .cursor | 1 => lr (.inl 0) | 2 => wr .row | 3 => lr (.inl 1)
      | 4 => lr (.inl 2) | 5 => wr .ctx | _ => lr (.inl 3)
    | .inr _ => wr .count),
   (fun k => match k with
    | .inl (.inl i) => match i.val with
      | 0 => some (.inl 1) | 1 => some (.inl 3) | 2 => some (.inl 4)
      | 3 => some (.inl 6) | _ => none
    | .inr .cursor => some (.inl 0) | .inr .row => some (.inl 2)
    | .inr .ctx => some (.inl 5) | .inr .count => some (.inr ()) | _ => none),
   by intro k; cases k with
      | inl i => fin_cases i <;> rfl
      | inr u => cases u; rfl,
   by intro k i h; rcases k with (j|b)|r
      · fin_cases j <;> simp_all <;> subst i <;> rfl
      · cases b <;> simp_all
      · cases r <;> simp_all <;> subst i <;> rfl⟩

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨wr $s,wr .scratch,wr $d,by decide,by decide,by decide⟩ : Ports K))

def code : PC → TreeBudgetSemanticRegisterTM2.Instr K PC
  | .prepare => .copy port(.targets,.htail) false .column
  | .column => .test (wr .htail) .done .readTarget
  | .readTarget => .read port(.htail,.target) .rootA
  | .rootA => .copy port(.index,.a) false .rootB
  | .rootB => .copy port(.root,.b) false .rootLe
  | .rootLe => .le cw .rootBackA .records
  | .rootBackA => .copy port(.root,.a) false .rootBackB
  | .rootBackB => .copy port(.index,.b) false .rootBackLe
  | .rootBackLe => .le cw .clearTarget .records
  | .records => .copy port(.body,.cursor) false .entry
  | .entry => .test (wr .cursor) .sumA .lookup
  | .lookup => .entry ew .update
  | .update => .lookup lw .clearRow
  | .clearRow => .weighted mw .sumB
  | .sumB => .clear port(.row,.ctx) .entry
  | .sumA => .copy port(.acc,.a) false .sumLe
  | .sumLe => .copy port(.target,.b) false .sumBackA
  | .sumBackA => .le cw .sumBackB .bad
  | .sumBackB => .copy port(.target,.a) false .sumBackLe
  | .sumBackLe => .copy port(.acc,.b) false .clearSum
  | .clearSum => .le cw .clearTarget .bad
  | .clearTarget => .clear port(.target,.ctx) .increment
  | .increment => .clear port(.acc,.ctx) .finish
  | .finish => .inc port(.index,.ctx) .column
  | .done => .halt
  | .bad => .fail

structure Data where
  child : Child → Bits := fun _ => []
  reg : R → Bits := fun _ => []

def store (d : Data) : K → Bits
  | .inl c => d.child c | .inr r => d.reg r

def put (d : Data) (k : K) (v : Bits) : Data := match k with
  | .inl c => {d with child := Function.update d.child c v}
  | .inr r => {d with reg := Function.update d.reg r v}

theorem store_put (d : Data) (k : K) (v : Bits) : store (put d k v)=Function.update (store d) k v := by
  funext j
  cases k <;> cases j <;> simp [store,put,Function.update_apply]

theorem data_ext (a b : Data) (hc : a.child=b.child) (hr : a.reg=b.reg) : a=b := by
  cases a; cases b; cases hc; cases hr; rfl

abbrev Cfg := TreeBudgetSemanticRegisterTM2.Cfg K PC
def cfg (l : PC) (d : Data) : Cfg := TreeBudgetSemanticRegisterTM2.cfg l (store d)
abbrev Run := TreeBudgetSemanticRegisterTM2.Run code
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) := TreeBudgetSemanticRegisterTM2.seq code h g

structure Input where
  body : Bits
  tokens : Bits
  root : Bits
  targets : Bits
  ctx : Bits

def state (s : Input) (i h t cursor a : Bits) : Data :=
  {reg := fun r => match r with
    | .body => s.body | .tokens => s.tokens | .root => s.root
    | .targets => s.targets | .ctx => s.ctx
    | .index => i | .htail => h | .target => t | .cursor => cursor | .acc => a
    | _ => []}

def machine : FinTM2 where
  K := K
  k₀ := wr .body
  k₁ := wr .acc
  Γ _ := Bool
  Λ := TreeBudgetSemanticRegisterTM2.Label PC
  main := .pc .prepare
  σ := State
  initialState := (none,true)
  m := TreeBudgetSemanticRegisterTM2.program code

def start (s : Input) : Cfg := cfg .prepare (state s [] [] [] [] [])

end UAVProof.A4ColumnCheck
