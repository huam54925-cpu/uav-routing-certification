import LeanCompletion.UAV.TreeBudgetCertificateRecordsTM2

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

structure Data where
  body : Bits := []
  count : Bits := []
  ctx : Bits := []
  dim : Bits := []
  todo : Bits := []
  input : Bits := []
  row : Bits := []
  mult : Bits := []
  amount : Bits := []
  dimCopy : Bits := []
  scratch : Bits := []

def store (d : Data) : K → Bits
  | .inl (.inl i) => match i.val with
    | 0 => d.body | 4 => d.count | 5 => d.ctx | _ => []
  | .inl (.inr (.inl i)) => match i.val with
    | 0 => d.input | 2 => d.row | _ => []
  | .inl (.inr (.inr _)) => d.mult
  | .inr .dim => d.dim
  | .inr .tokens => d.todo
  | .inr .scratch => d.scratch
  | .inr .amount => d.amount
  | .inr .dimCopy => d.dimCopy

def cfg (l : L) (d : Data) : Cfg := ⟨some l, (none,true), store d⟩
def stop (d : Data) (b : Bool) : Cfg := ⟨none, (none,b), store d⟩
abbrev Run (a b : Cfg) (t : ℕ) := EvalsToInTime machine.step a (some b) t

def seq {a b c : Cfg} {x y : ℕ} (h : Run a b x) (g : Run b c y) : Run a c (x+y) :=
  by simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step x y a b (some c) h g

def Kept (d : Data) (out : Cfg) : Prop :=
  out.stk savedBody = d.body ∧ out.stk savedCount = d.count ∧
  out.stk ctxStack = d.ctx ∧ out.stk (.inr .dim) = d.dim

def work (d : Data) (k : ℕ) (s : Bits) : Data :=
  {d with
    todo := List.replicate k true
    input := s
    row := []
    mult := []
    amount := []
    dimCopy := []
    scratch := []}

def source (j : Job) (d : Data) : Bits := match j with
  | .saveBody => d.body | .copyTokens => d.count | .clearMult => d.mult
  | .incSize => d.amount | .copyDim => d.dim
def dest (j : Job) (d : Data) : Bits := match j with
  | .saveBody => d.input | .copyTokens => d.todo | _ => d.dimCopy
def replace (j : Job) (d : Data) (s t z : Bits) : Data := match j with
  | .saveBody => {d with body := s, scratch := t, input := z}
  | .copyTokens => {d with count := s, scratch := t, todo := z}
  | .clearMult => {d with mult := s, scratch := t, dimCopy := z}
  | .incSize => {d with amount := s, scratch := t, dimCopy := z}
  | .copyDim => {d with dim := s, scratch := t, dimCopy := z}

theorem replace_original (j : Job) (d : Data) :
    replace j d (source j d) d.scratch (dest j d) = d := by cases j <;> rfl

theorem tapes_replace (j : Job) (d : Data) (s t z : Bits) :
    tapes (ports j) (store d) s t z = store (replace j d s t z) := by
  cases j <;> funext k <;> rcases k with (i | (i | u)) | a
  all_goals first | (fin_cases i <;> rfl) | (cases u; rfl) | (cases a <;> rfl)

theorem conf_replace (j : Job) (d : Data) (l : L) (s t z : Bits) :
    TreeBudgetStackRoutine.conf (ports j) (store d) l s t z =
      cfg l (replace j d s t z) := by
  simp only [TreeBudgetStackRoutine.conf, cfg, tapes_replace]

def copied (j : Job) (d : Data) := replace j d (source j d) [] (source j d ++ dest j d)

def copy_job (j : Job) (d : Data) (ht : d.scratch = []) :
    Run (cfg (.job j .reverse) d) (cfg (next j) (copied j d))
      (2*(source j d).length+2) := by
  have h := TreeBudgetStackRoutine.copy_run (ports j) (store d) (L.job j) (next j)
    false program (fun _ => rfl) (source j d) (dest j d)
  rw [conf_replace, conf_replace, ← ht, replace_original] at h
  simpa only [copied, ht] using h

def clear_mult (d : Data) :
    Run (cfg (.job .clearMult .clear) d) (cfg .row {d with mult := []}) (d.mult.length+1) := by
  have h := TreeBudgetStackRoutine.clear_run (ports .clearMult) (store d)
    (L.job .clearMult) (next .clearMult) false program (fun _ => rfl)
    d.mult d.scratch d.dimCopy
  rw [conf_replace, conf_replace] at h
  exact h

def increment_job (d : Data) (ht : d.scratch = []) :
    Run (cfg (.job .incSize .carry) d)
      (cfg .row {d with amount := TreeBudgetStackRoutine.increment d.amount})
      (2*d.amount.length+2) := by
  have h := TreeBudgetStackRoutine.increment_run (ports .incSize) (store d)
    (L.job .incSize) (next .incSize) false program (fun _ => rfl) d.amount [] d.dimCopy
  rw [conf_replace, conf_replace] at h
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at h
  rw [← ht] at h
  exact h

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem finite_control : Fintype.card K = 20 ∧ Fintype.card L = 78 ∧
    Fintype.card State = 6 := by decide

end UAVProof.A4CertRecords
