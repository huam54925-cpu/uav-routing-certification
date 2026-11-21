import LeanCompletion.UAV.TreeBudgetIntTM2

/-! Split a canonical signed table into two natural tables, preserving its
original wire order. All loops inspect and move one physical stack bit. -/
namespace UAVProof.TreeBudgetSignedTableTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open Turing.TM2.Stmt

abbrev K := Fin 7
inductive L | sign | marker | payload | restore | positive | negative | done
  deriving DecidableEq, Fintype
abbrev Cfg := Configuration K L

def jump (l : L) : Statement K L := load (fun _ => (none,true)) (goto fun _ => l)
def moved (k : K) (q : Statement K L) := push k (fun s => s.1.getD false) q
def program : L → Statement K L
  | .sign => pop 0 (fun _ b => (b,b.getD false))
      (branch (fun s => s.1.isNone) (jump .restore)
        (moved 1 (branch Prod.snd
          (push 2 (fun _ => false) (load (fun s => (none,s.2)) (goto fun _ => .marker)))
          (push 3 (fun _ => false) (load (fun s => (none,s.2)) (goto fun _ => .marker))))))
  | .marker => pop 0 (fun s b => (b,s.2))
      (moved 1 (branch Prod.snd (moved 3 (branch (fun s => s.1.getD false)
        (load (fun s => (none,s.2)) (goto fun _ => .payload)) (jump .sign)))
        (moved 2 (branch (fun s => s.1.getD false)
          (load (fun s => (none,s.2)) (goto fun _ => .payload)) (jump .sign)))))
  | .payload => pop 0 (fun s b => (b,s.2))
      (moved 1 (branch Prod.snd
        (moved 3 (load (fun s => (none,s.2)) (goto fun _ => .marker)))
        (moved 2 (load (fun s => (none,s.2)) (goto fun _ => .marker)))))
  | .restore => pop 1 (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump .positive) (moved 0 (jump .restore)))
  | .positive => pop 2 (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump .negative) (moved 4 (jump .positive)))
  | .negative => pop 3 (fun _ b => (b,true))
      (branch (fun s => s.1.isNone) (jump .done) (moved 5 (jump .negative)))
  | .done => halt

def machine : FinTM2 where
  K := K
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := L
  main := .sign
  σ := State
  initialState := (none,true)
  m := program

def store (s h p n po no ctx : Bits) : K → Bits := fun k => match k.val with
  | 0 => s | 1 => h | 2 => p | 3 => n | 4 => po | 5 => no | _ => ctx
def cfg (l : L) (b : Bool) (s h p n po no ctx : Bits) : Cfg :=
  ⟨some l,(none,b),store s h p n po no ctx⟩
def stopped (s p n ctx : Bits) : Cfg := ⟨none,(none,true),store s [] [] [] p n ctx⟩
def start (s ctx : Bits) := cfg .sign true s [] [] [] [] [] ctx

def pos (a : ℤ) : ℕ := a.toNat
def neg (a : ℤ) : ℕ := (-a).toNat
def positive (xs : List ℤ) := (xs.map pos).flatMap encodeNat
def negative (xs : List ℤ) := (xs.map neg).flatMap encodeNat
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step u v a b (some c) h g

theorem split_fields (a : ℤ) :
    (if decide (a<0) then encodeNat 0 else word a.natAbs.bits)=encodeNat (pos a) ∧
    (if decide (a<0) then word a.natAbs.bits else encodeNat 0)=encodeNat (neg a) := by
  cases a <;> simp [pos,neg,encodeNat]

theorem split_lengths (xs : List ℤ) :
    (positive xs).length+(negative xs).length=(xs.flatMap encodeInt).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a <;> simp_all [positive,negative,pos,neg,encodeNat,encodeInt,word,List.length_append] <;> omega

theorem init_eq (s : Bits) : initList machine s=start s [] := by
  simp only [initList,machine,start,cfg]
  congr 1
  funext k; fin_cases k <;> rfl

end UAVProof.TreeBudgetSignedTableTM2
