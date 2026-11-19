import LeanCompletion.UAV.TreeBudgetBinaryCodec
import Mathlib.Computability.TuringMachine.Computable

/-! A callable, data-preserving finite-alphabet TM2 frame parser. The caller
supplies labels and three distinct stacks. Other stacks are untouched. The
optional canonicality check tests the last payload digit (empty means zero).
All bounds count actual TM2 transitions, including scratch-stack cleanup. -/
namespace UAVProof.TreeBudgetFrameRoutineTM2
open TreeBudgetBinaryCodec Turing StateTransition Turing.TM2.Stmt

inductive Phase | marker | payload | reverse | clear
  deriving DecidableEq, Fintype

abbrev State := Option Bool × Bool
abbrev Statement (K Λ : Type) := TM2.Stmt (fun _ : K => Bool) Λ State
abbrev Configuration (K Λ : Type) := TM2.Cfg (fun _ : K => Bool) Λ State

structure Ports (K : Type) where
  src : K
  scratch : K
  dst : K
  scratch_ne_src : scratch ≠ src
  dst_ne_src : dst ≠ src
  dst_ne_scratch : dst ≠ scratch

variable {K Λ : Type} [DecidableEq K]

def tapes (p : Ports K) (base : K → Bits) (input acc output : Bits) : K → Bits :=
  fun k => if k = p.src then input else if k = p.scratch then acc
    else if k = p.dst then output else base k

@[simp] theorem tapes_src (p : Ports K) (base : K → Bits) (xs acc out : Bits) :
    tapes p base xs acc out p.src = xs := by simp [tapes]
@[simp] theorem tapes_scratch (p : Ports K) (base : K → Bits) (xs acc out : Bits) :
    tapes p base xs acc out p.scratch = acc := by simp [tapes, p.scratch_ne_src]
@[simp] theorem tapes_dst (p : Ports K) (base : K → Bits) (xs acc out : Bits) :
    tapes p base xs acc out p.dst = out := by simp [tapes, p.dst_ne_src, p.dst_ne_scratch]

@[simp] theorem update_src (p : Ports K) (base : K → Bits) (xs ys acc out : Bits) :
    Function.update (tapes p base xs acc out) p.src ys = tapes p base ys acc out := by
  funext k; by_cases h : k = p.src <;> simp [tapes, h, Function.update_apply]
@[simp] theorem update_scratch (p : Ports K) (base : K → Bits) (xs acc ys out : Bits) :
    Function.update (tapes p base xs acc out) p.scratch ys = tapes p base xs ys out := by
  funext k
  by_cases h : k = p.scratch
  · subst k; simp [tapes, p.scratch_ne_src]
  · by_cases h' : k = p.src <;>
      simp_all [tapes, Ne.symm p.scratch_ne_src]
@[simp] theorem update_dst (p : Ports K) (base : K → Bits) (xs acc out ys : Bits) :
    Function.update (tapes p base xs acc out) p.dst ys = tapes p base xs acc ys := by
  funext k
  by_cases h : k = p.dst
  · subst k; simp [tapes, p.dst_ne_src, p.dst_ne_scratch]
  · by_cases h' : k = p.src <;> by_cases h'' : k = p.scratch <;>
      simp_all [tapes, Ne.symm p.dst_ne_src, Ne.symm p.dst_ne_scratch, p.scratch_ne_src]

def cfg (p : Ports K) (base : K → Bits) (l : Λ) (tmp : Option Bool) (last : Bool)
    (xs acc out : Bits) : Configuration K Λ := ⟨some l, (tmp, last), tapes p base xs acc out⟩

def code (p : Ports K) (lab : Phase → Λ) (ok bad : Λ) (canonical : Bool) :
    Phase → Statement K Λ
  | .marker => pop p.src (fun s b => (b, s.2))
      (branch (fun s => s.1.isNone) (goto (fun _ => lab .clear))
        (branch (fun s => s.1 == some false)
          (branch (fun s => !canonical || s.2) (goto (fun _ => lab .reverse))
            (goto (fun _ => lab .clear))) (goto (fun _ => lab .payload))))
  | .payload => pop p.src (fun s b => (b, s.2))
      (branch (fun s => s.1.isNone) (goto (fun _ => lab .clear))
        (push p.scratch (fun s => s.1.getD false)
          (load (fun s => (s.1, s.1.getD false)) (goto (fun _ => lab .marker)))))
  | .reverse => pop p.scratch (fun s b => (b, s.2))
      (branch (fun s => s.1.isNone) (load (fun _ => (none, true)) (goto (fun _ => ok)))
        (push p.dst (fun s => s.1.getD false) (goto (fun _ => lab .reverse))))
  | .clear => pop p.scratch (fun s b => (b, s.2))
      (branch (fun s => s.1.isNone) (load (fun _ => (none, true)) (goto (fun _ => bad)))
        (goto (fun _ => lab .clear)))

def lastDigit : Bits → Bool → Bool
  | [], seed => seed
  | b :: bs, _ => lastDigit bs b

section Execution
variable (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (ok bad : Λ) (canonical : Bool)
variable (M : Λ → Statement K Λ)
variable (hM : ∀ phase, M (lab phase) = code p lab ok bad canonical phase)
include hM

theorem step_reverse_nil (tmp : Option Bool) (last : Bool) (xs out : Bits) :
    TM2.step M (cfg p base (lab .reverse) tmp last xs [] out) =
      some (cfg p base ok none true xs [] out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_reverse_cons (tmp : Option Bool) (last b : Bool) (xs acc out : Bits) :
    TM2.step M (cfg p base (lab .reverse) tmp last xs (b :: acc) out) =
      some (cfg p base (lab .reverse) (some b) last xs acc (b :: out)) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_clear_nil (tmp : Option Bool) (last : Bool) (xs out : Bits) :
    TM2.step M (cfg p base (lab .clear) tmp last xs [] out) =
      some (cfg p base bad none true xs [] out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_clear_cons (tmp : Option Bool) (last b : Bool) (xs acc out : Bits) :
    TM2.step M (cfg p base (lab .clear) tmp last xs (b :: acc) out) =
      some (cfg p base (lab .clear) (some b) last xs acc out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_marker_nil (tmp : Option Bool) (last : Bool) (acc out : Bits) :
    TM2.step M (cfg p base (lab .marker) tmp last [] acc out) =
      some (cfg p base (lab .clear) none last [] acc out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_marker_end (tmp : Option Bool) (last : Bool) (xs acc out : Bits) :
    TM2.step M (cfg p base (lab .marker) tmp last (false :: xs) acc out) =
      some (cfg p base (lab (if !canonical || last then .reverse else .clear))
        (some false) last xs acc out) := by
  cases canonical <;> cases last <;> simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_marker_more (tmp : Option Bool) (last : Bool) (xs acc out : Bits) :
    TM2.step M (cfg p base (lab .marker) tmp last (true :: xs) acc out) =
      some (cfg p base (lab .payload) (some true) last xs acc out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_payload_nil (tmp : Option Bool) (last : Bool) (acc out : Bits) :
    TM2.step M (cfg p base (lab .payload) tmp last [] acc out) =
      some (cfg p base (lab .clear) none last [] acc out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]
theorem step_payload_cons (tmp : Option Bool) (last b : Bool) (xs acc out : Bits) :
    TM2.step M (cfg p base (lab .payload) tmp last (b :: xs) acc out) =
      some (cfg p base (lab .marker) (some b) b xs (b :: acc) out) := by
  simp [cfg, TM2.step, hM, code, TM2.stepAux]

end Execution

def once {S : Type} {f : S → Option S} {a b : S} (h : f a = some b) :
    EvalsToInTime f a (some b) 1 := ⟨⟨1, by simpa using h⟩, le_rfl⟩
def prepend {S : Type} {f : S → Option S} {a b : S} {out : Option S} {t : ℕ}
    (h : f a = some b) (tail : EvalsToInTime f b out t) : EvalsToInTime f a out (t + 1) :=
  EvalsToInTime.trans f 1 t a b out (once h) tail
def weaken {S : Type} {f : S → Option S} {a : S} {out : Option S} {s t : ℕ}
    (run : EvalsToInTime f a out s) (h : s ≤ t) : EvalsToInTime f a out t :=
  ⟨run.toEvalsTo, run.steps_le_m.trans h⟩

end UAVProof.TreeBudgetFrameRoutineTM2
