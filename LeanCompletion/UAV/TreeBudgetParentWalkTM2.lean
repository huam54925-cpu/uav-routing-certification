import LeanCompletion.UAV.TreeBudgetTableChecks

/-! Repeat the physical indexed parent lookup. After each lookup the caller
rebuilds the table and prepends the fetched parent as the next index. Stack
moves are charged; the loop owns a separate stack of iteration tokens. -/
namespace UAVProof.TreeBudgetParentWalkTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open Turing.TM2.Stmt
abbrev K := TreeBudgetParentLookupTM2.K ⊕ Unit
abbrev L := TreeBudgetParentLookupTM2.L ⊕ Fin 8
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L
abbrev src : K := .inl (.inl 0)
abbrev front : K := .inl (.inl 2)
abbrev digits : K := .inl (.inr true)
abbrev tmp : K := .inl (.inr false)
abbrev count : K := .inr ()
def jump (l : L) : Stmt := load (fun _ => (none,true)) (goto fun _ => l)
def put (k : K) (q : Stmt) : Stmt := push k (fun s => s.1.getD false) q
def scan (k : K) (empty more : Stmt) : Stmt :=
  pop k (fun _ b => (b,true)) (branch (fun s => s.1.isNone) empty more)
def emit (q : Stmt) := put src (push src (fun _ => true) q)
def term (q : Stmt) := push src (fun _ => false) q

def program : L → Stmt
  | .inl l => compile Sum.inl (.inr 0) (TreeBudgetParentLookupTM2.program l)
  | .inr l => match l.val with
    | 0 => branch Prod.snd (jump (.inr 1)) halt
    | 1 => scan digits (term (jump (.inr 2))) (put tmp (jump (.inr 1)))
    | 2 => scan tmp (jump (.inr 3)) (put digits (emit (jump (.inr 2))))
    | 3 => scan front (jump (.inr 4)) (put tmp (jump (.inr 3)))
    | 4 => scan tmp (jump (.inr 5)) (put src (jump (.inr 4)))
    | 5 => scan digits (term (jump (.inr 6))) (put tmp (jump (.inr 5)))
    | 6 => scan tmp (jump (.inr 7)) (emit (jump (.inr 6)))
    | _ => scan count (load (fun _ => (none,true)) halt) (jump (.inl (.inl 0)))

def machine : FinTM2 where
  K := K
  k₀ := src
  k₁ := src
  Γ _ := Bool
  Λ := L
  main := .inr 7
  σ := State
  initialState := (none,true)
  m := program

def store (s f d t ticks ctx : Bits) : K → Bits
  | .inr _ => ticks
  | .inl (.inr b) => if b then d else t
  | .inl (.inl i) => match i.val with
    | 0 => s | 2 => f | 5 => ctx | _ => []
def cfg (l : Fin 8) (s f d t ticks ctx : Bits) : Cfg :=
  ⟨some (.inr l),(none,true),store s f d t ticks ctx⟩
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n

local macro "one_step" : tactic => `(tactic|
  (simp [machine,FinTM2.step,TM2.step,TM2.stepAux,cfg,program,scan,put,jump,emit,term,store]
   all_goals congr 2
   all_goals funext k; cases k with
     | inr u => cases u; rfl
     | inl k => cases k with
       | inr b => cases b <;> rfl
       | inl i => fin_cases i <;> rfl))

def reverse_digits (d s f t ticks ctx : Bits) (stage : Bool) :
    Run (cfg (if stage then 5 else 1) s f d t ticks ctx)
      (cfg (if stage then 6 else 2) (false :: s) f [] (d.reverse ++ t) ticks ctx) (d.length+1) := by
  induction d generalizing t with
  | nil => cases stage <;> apply once <;> one_step
  | cons b d ih =>
    have step : machine.step (cfg (if stage then 5 else 1) s f (b::d) t ticks ctx) =
        some (cfg (if stage then 5 else 1) s f d (b::t) ticks ctx) := by cases stage <;> one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend step (ih (b::t))

def payload (d : Bits) := d.flatMap fun b => [true,b]

def emit_digits (t s f d ticks ctx : Bits) (keep : Bool) :
    Run (cfg (if keep then 2 else 6) s f d t ticks ctx)
      (cfg (if keep then 3 else 7) (payload t.reverse ++ s) f
        (if keep then t.reverse ++ d else d) [] ticks ctx) (t.length+1) := by
  induction t generalizing s d with
  | nil => cases keep <;> apply once <;> one_step
  | cons b t ih =>
    cases keep with
    | false =>
      have step : machine.step (cfg 6 s f d (b::t) ticks ctx) =
          some (cfg 6 (true::b::s) f d t ticks ctx) := by one_step
      simpa [payload,List.reverse_cons,List.append_assoc] using prepend step (ih (true::b::s) d)
    | true =>
      have step : machine.step (cfg 2 s f d (b::t) ticks ctx) =
          some (cfg 2 (true::b::s) f (b::d) t ticks ctx) := by one_step
      simpa [payload,List.reverse_cons,List.append_assoc] using prepend step (ih (true::b::s) (b::d))

def reverse_front (f s d t ticks ctx : Bits) :
    Run (cfg 3 s f d t ticks ctx) (cfg 4 s [] d (f.reverse ++ t) ticks ctx) (f.length+1) := by
  induction f generalizing t with
  | nil => apply once; one_step
  | cons b f ih =>
    have step : machine.step (cfg 3 s (b::f) d t ticks ctx) =
        some (cfg 3 s f d (b::t) ticks ctx) := by one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend step (ih (b::t))

def restore_front (t s d ticks ctx : Bits) :
    Run (cfg 4 s [] d t ticks ctx) (cfg 5 (t.reverse ++ s) [] d [] ticks ctx) (t.length+1) := by
  induction t generalizing s with
  | nil => apply once; one_step
  | cons b t ih =>
    have step : machine.step (cfg 4 s [] d (b::t) ticks ctx) =
        some (cfg 4 (b::s) [] d t ticks ctx) := by one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend step (ih (b::s))

/-- Rebuild the entire parent table and prepend a fresh copy of the fetched
address. The query and table are ready for the very same lookup program. -/
def requery (f d t ticks ctx : Bits) :
    Run (cfg 1 t f d [] ticks ctx)
      (cfg 7 (word d ++ (f ++ (word d ++ t))) [] [] [] ticks ctx)
      (4*d.length+2*f.length+6) := by
  have r₁ := reverse_digits d t f [] ticks ctx false
  have e₁ := emit_digits d.reverse (false::t) f [] ticks ctx true
  have r₂ := reverse_front f (word d ++ t) d [] ticks ctx
  have e₂ := restore_front f.reverse (word d ++ t) d ticks ctx
  have r₃ := reverse_digits d (f ++ (word d ++ t)) [] [] ticks ctx true
  have e₃ := emit_digits d.reverse (false::(f ++ (word d ++ t))) [] [] ticks ctx false
  have enc (s : Bits) : payload d ++ false :: s = word d ++ s := by simp [payload,word,List.append_assoc]
  simp only [Bool.false_eq_true,ite_false,ite_true,List.append_nil,List.reverse_reverse,
    List.length_reverse,enc] at r₁ e₁ r₂ e₂ r₃ e₃
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ r₁ e₁
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq r₂
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq e₂
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq r₃
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq e₃) (by omega)

end UAVProof.TreeBudgetParentWalkTM2
