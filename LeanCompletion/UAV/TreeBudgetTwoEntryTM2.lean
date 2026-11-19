import LeanCompletion.UAV.TreeBudgetEntryTM2

/-! Execute a second record parser at the first record's cursor. Save the first
count and row in caller stacks before reusing the callee's workspace. -/
namespace UAVProof.TreeBudgetTwoEntryTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open Turing.TM2.Stmt

abbrev K := TreeBudgetEntryTM2.K ⊕ Fin 3
abbrev L := TreeBudgetEntryTM2.L ⊕ Fin 3
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev rowStack : K := .inl (.inl 2)
abbrev countStack : K := .inl (.inr ())
def jump (l : L) : Stmt := load (fun _ => (none,true)) (goto (fun _ => l))

def transfer (src dst : K) (more : L) (next : Stmt) : Stmt :=
  pop src (fun _ b => (b,true)) (branch (fun s => s.1.isNone) next
    (push dst (fun s => s.1.getD false) (jump more)))

def program : L → Stmt
  | .inl l => compile Sum.inl (.inr 0) (TreeBudgetEntryTM2.program l)
  | .inr l =>
    if l = 0 then branch Prod.snd
      (peek (.inr 2) (fun _ b => (b,true))
        (branch (fun s => s.1.isNone) (jump (.inr 1)) (load (fun _ => (none,true)) halt))) halt
    else if l = 1 then transfer rowStack (.inr 0) (.inr 1) (jump (.inr 2))
    else transfer countStack (.inr 1) (.inr 2)
      (push (.inr 2) (fun _ => true) (jump (.inl (TreeBudgetEntryTM2.labels .marker))))

def machine : FinTM2 where
  K := K
  k₀ := .inl (.inl 0)
  k₁ := .inl (.inl 2)
  Γ _ := Bool
  Λ := L
  main := .inl (TreeBudgetEntryTM2.labels .marker)
  σ := State
  initialState := (none,true)
  m := program

def saved (row count flag : Bits) (i : Fin 3) := match i.val with
  | 0 => row | 1 => count | _ => flag
def start (s ctx : Bits) : Cfg :=
  embed Sum.inl (.inr 0) (saved [] [] []) (TreeBudgetEntryTM2.start s ctx)

/-- Return both physical outputs and the remaining cursor. Saved words are
in reverse order because the transfer consumes the first callee's sources. -/
def readBoth (c : Cfg) : Option (TreeBudgetSparseCodec.RawEntry × TreeBudgetSparseCodec.RawEntry × Bits) := do
  if !c.var.2 then none else
    let row₁ := (c.stk (.inr 0)).reverse
    let row₂ := c.stk rowStack
    let ns ← TreeBudgetNatListLoop.fields row₁.length row₁
    let ms ← TreeBudgetNatListLoop.fields row₂.length row₂
    return ((value (c.stk (.inr 1)).reverse, ns), (value (c.stk countStack), ms),
      c.stk (.inl (.inl 0)))

def run : ℕ → Cfg → Option Cfg
  | 0, _ => none
  | n+1, c => match machine.step c with
    | none => some c
    | some d => run n d

def sample (s ctx : Bits) (fuel : ℕ) :
    Option (Option (TreeBudgetSparseCodec.RawEntry × TreeBudgetSparseCodec.RawEntry × Bits) × Bits) := (run fuel (start s ctx)).map fun c =>
  (readBoth c, c.stk (.inl (.inl 5)))

theorem consecutive_suffix (a b : TreeBudgetSparseCodec.RawEntry) (tail ctx : Bits) :
    TreeBudgetEntryTM2.readEntry (TreeBudgetEntryTM2.stopped
      (TreeBudgetSparseCodec.encodeEntry a ++ (TreeBudgetSparseCodec.encodeEntry b ++ tail)) ctx) =
        some (a, TreeBudgetSparseCodec.encodeEntry b ++ tail) ∧
    TreeBudgetEntryTM2.readEntry (TreeBudgetEntryTM2.stopped (TreeBudgetSparseCodec.encodeEntry b ++ tail) ctx) =
        some (b,tail) :=
  ⟨TreeBudgetEntryTM2.entry_suffix .., TreeBudgetEntryTM2.entry_suffix ..⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem unequal_rows :
    sample (TreeBudgetSparseCodec.encodeEntry (2,[0,3]) ++
      TreeBudgetSparseCodec.encodeEntry (5,[1]) ++ [true,false]) [false,true] 300 =
      some (some ((2,[0,3]),(5,[1]),[true,false]),[false,true]) := by rfl

theorem empty_then_nonempty :
    sample (TreeBudgetSparseCodec.encodeEntry (0,[]) ++
      TreeBudgetSparseCodec.encodeEntry (1,[0,0])) [true] 180 =
      some (some ((0,[]),(1,[0,0]),[]),[true]) := by rfl

theorem truncated_second :
    sample (TreeBudgetSparseCodec.encodeEntry (1,[0]) ++ encodeNat 2 ++ [true]) [false] 100 =
      some (none,[false]) := by rfl

theorem oversize_first :
    sample (encodeNat 1 ++ encodeNat 8 ++ [true,false]) [false] 100 =
      some (none,[false]) := by rfl

end UAVProof.TreeBudgetTwoEntryTM2
