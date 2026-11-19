import LeanCompletion.UAV.TreeBudgetFrameRunsTM2
import LeanCompletion.UAV.TreeBudgetCanonicalDigits

/-! Counted-loop continuation. Its inputs are the suffix and the one-token-per-
element stack returned by the count guard. -/
namespace UAVProof.TreeBudgetNatListLoop
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits Turing StateTransition
open Turing.TM2.Stmt

abbrev K := Fin 7
abbrev L := Fin 18
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L

def ports : Ports K := ⟨0, 1, 2, by decide, by decide, by decide⟩
def labels : Phase → L
  | .marker => 11 | .payload => 12 | .reverse => 13 | .clear => 14

def base (tokens acc ctx : Bits) (k : K) := if k = 4 then tokens else
  if k = 5 then ctx else if k = 6 then acc else []
def conf (l : L) (r digits tokens acc ctx : Bits) : Cfg :=
  cfg ports (base tokens acc ctx) l none true r [] digits

def jump (l : L) : Stmt := load (fun _ => (none,true)) (goto (fun _ => l))
def takeBit (k : K) (no yes : Stmt) : Stmt := pop k (fun _ b => (b,true))
  (branch (fun s => s.1.isNone) no yes)

def loopCode (l : L) : Stmt :=
  match l.val with
  | 9 => takeBit 4 (jump 16) (jump 11)
  | 11 => code ports labels 15 10 true .marker
  | 12 => code ports labels 15 10 true .payload
  | 13 => code ports labels 15 10 true .reverse
  | 14 => code ports labels 15 10 true .clear
  | 15 => takeBit 2 (push 6 (fun _ => false) (jump 9))
      (push 6 (fun _ => true) (push 6 (fun s => s.1.getD false) (jump 15)))
  | 16 => takeBit 6 (jump 17) (push 2 (fun s => s.1.getD false) (jump 16))
  | _ => halt

/-- The caller owns labels outside this routine. -/
structure Linked (M : L → Stmt) : Prop where
  tick : M 9 = loopCode 9
  frame : ∀ p, M (labels p) = code ports labels 15 10 true p
  emit : M 15 = loopCode 15
  finish : M 16 = loopCode 16

variable {M : L → Stmt} (link : Linked M)
include link

theorem tick_nil (r acc ctx : Bits) :
    TM2.step M (conf 9 r [] [] acc ctx) = some (conf 16 r [] [] acc ctx) := by
  simp [TM2.step, conf, cfg, link.tick, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]

theorem tick_cons (r tokens acc ctx : Bits) :
    TM2.step M (conf 9 r [] (true :: tokens) acc ctx) = some (conf 11 r [] tokens acc ctx) := by
  simp [TM2.step, conf, cfg, link.tick, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]
  funext k; fin_cases k <;> rfl

theorem emit_nil (r tokens acc ctx : Bits) :
    TM2.step M (conf 15 r [] tokens acc ctx) = some (conf 9 r [] tokens (false :: acc) ctx) := by
  simp [TM2.step, conf, cfg, link.emit, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]
  funext k; fin_cases k <;> rfl

theorem emit_cons (r ds tokens acc ctx : Bits) (b : Bool) :
    TM2.step M (conf 15 r (b :: ds) tokens acc ctx) = some (conf 15 r ds tokens (b :: true :: acc) ctx) := by
  simp [TM2.step, conf, cfg, link.emit, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]
  funext k; fin_cases k <;> rfl

theorem finish_nil (r ds ctx : Bits) :
    TM2.step M (conf 16 r ds [] [] ctx) = some (conf 17 r ds [] [] ctx) := by
  simp [TM2.step, conf, cfg, link.finish, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]

theorem finish_cons (r ds acc ctx : Bits) (b : Bool) :
    TM2.step M (conf 16 r ds [] (b :: acc) ctx) = some (conf 16 r (b :: ds) [] acc ctx) := by
  simp [TM2.step, conf, cfg, link.finish, loopCode, takeBit, jump, TM2.stepAux, tapes, base, ports]
  funext k; fin_cases k <;> rfl

def emit_run (ds r tokens acc ctx : Bits) :
    EvalsToInTime (TM2.step M) (conf 15 r ds tokens acc ctx)
      (some (conf 9 r [] tokens ((word ds).reverse ++ acc) ctx)) (ds.length+1) := by
  induction ds generalizing acc with
  | nil => exact once (emit_nil link r tokens acc ctx)
  | cons b ds ih =>
    simpa [word, List.reverse_append, List.append_assoc] using
      prepend (emit_cons link r ds tokens acc ctx b) (ih (b :: true :: acc))

def finish_run (acc r ds ctx : Bits) :
    EvalsToInTime (TM2.step M) (conf 16 r ds [] acc ctx)
      (some (conf 17 r (acc.reverse ++ ds) [] [] ctx)) (acc.length+1) := by
  induction acc generalizing ds with
  | nil => exact once (finish_nil link r ds ctx)
  | cons b acc ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      prepend (finish_cons link r ds acc ctx b) (ih (b :: ds))

def suffix (s : Bits) := ((parseWord s).map Prod.snd).getD []
def fieldEnd (r tokens acc ctx : Bits) : Cfg :=
  match parseNat r with
  | none => conf 10 (suffix r) [] tokens acc ctx
  | some (n,t) => conf 15 t n.bits tokens acc ctx

def field_run (r tokens acc ctx : Bits) : EvalsToInTime (TM2.step M) (conf 11 r [] tokens acc ctx)
    (some (fieldEnd r tokens acc ctx)) (2*r.length+2) := by
  cases hw : parseWord r with
  | none =>
    have run := truncated_run ports (base tokens acc ctx) labels 15 10 true M link.frame
      r hw none true [] []
    simpa [conf, fieldEnd, parseNat_truncated r hw, suffix, hw, labels] using run
  | some pair =>
    obtain ⟨ds,t⟩ := pair
    have he := parseWord_consumed r ds t hw
    subst r
    have run := framed_run ports (base tokens acc ctx) labels 15 10 true M link.frame
      ds t none true [] []
    have hb : 3*ds.length+2 ≤ 2*(word ds ++ t).length+2 := by simp [word_length]; omega
    cases hc : lastDigit ds true with
    | false => simpa [conf, fieldEnd, parseNat_framed, hc, labels, suffix, parseWord_append] using weaken run hb
    | true => simpa [conf, fieldEnd, parseNat_framed, hc, labels, canonical_of_last ds hc] using weaken run hb

end UAVProof.TreeBudgetNatListLoop
