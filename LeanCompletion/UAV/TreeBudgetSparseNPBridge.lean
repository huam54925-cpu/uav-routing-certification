import LeanCompletion.UAV.TreeBudgetSparseWireBounds
import Mathlib.Computability.TuringMachine.Computable

/-! Standard-machine boundary. This file proves a CONDITIONAL NP transfer.
It does not construct the polynomial-time TM2 verifier that is its hypothesis.
All stack alphabets are required finite, in addition to FinTM2's finite control. -/
namespace UAVProof.TreeBudgetSparseNPBridge
open TreeBudgetBinaryCodec TreeBudgetSparseVerifier TreeBudgetSparseWireBounds
open TreeBudgetMatrix TreeBudgetVector TreeBudgetCertificate

def pairWire (p : Bits × Bits) : Bits := word p.1 ++ p.2

theorem pairWire_length (x y : Bits) :
    (pairWire (x, y)).length = 2 * x.length + 1 + y.length := by
  simp [pairWire, word_length]

theorem pairWire_injective : Function.Injective pairWire := by
  intro p q h
  have hp := congrArg parseWord h
  simpa only [pairWire, parseWord_append, Option.some.injEq] using hp

/-- Finite-stack, finite-control, finite-alphabet deterministic TM2, with an
actual polynomial bound on TM2 transitions for every encoded pair, both true
and false outputs. No acceptance hypothesis is part of this requirement. -/
structure StandardVerifier (V : Bits → Bits → Bool) where
  machine : Turing.TM2ComputableInPolyTime pairWire (fun b : Bool => [b])
    (fun p : Bits × Bits => V p.1 p.2)
  finiteAlphabet : ∀ k, Finite (machine.tm.Γ k)

/-- The verifier characterization of NP, instantiated with a standard machine
model and explicit polynomial witness length. -/
def InNP (language : Set Bits) : Prop :=
  ∃ V : Bits → Bits → Bool, Nonempty (StandardVerifier V) ∧
    ∃ bound : Polynomial ℕ, ∀ x,
      x ∈ language ↔ ∃ y, y.length ≤ bound.eval x.length ∧ V x y = true

def language : Set Bits := {x | ∃ I : Instance, parseInstance x = some I ∧
  MatrixFeasible (tree I) (decode I.data.H) I.routes (fees I) (budget I)}

theorem accepted_in_language (x y : Bits) (h : verify x y = true) : x ∈ language := by
  obtain ⟨I, hp, C, _, hc⟩ := (verify_refines x y).mp h
  exact ⟨I, hp, valid_implies_matrix _ _ _ _ _ C ((checkCertificate_eq_true_iff ..).mp hc)⟩

/-- A convenient ordinary polynomial majorant of the sharper A3 bound. -/
noncomputable def witnessPolynomial : Polynomial ℕ := Polynomial.X * (Polynomial.X + 1)

theorem witnessPolynomial_eval (L : ℕ) : witnessPolynomial.eval L = L * (L + 1) := by
  simp [witnessPolynomial]

theorem language_iff_polynomial_witness (x : Bits) :
    x ∈ language ↔ ∃ y, y.length ≤ witnessPolynomial.eval x.length ∧ verify x y = true := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := (language_iff_short_witness x).mp h
    refine ⟨y, hy.trans ?_, hv⟩
    rw [witnessPolynomial_eval]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_self _ _) _)
  · rintro ⟨y, _, hv⟩
    exact accepted_in_language x y hv

/-- Explicit remaining hypothesis: a concrete machine, with a proved step
bound. Neither a Costed counter nor a numeric polynomial can discharge it. -/
theorem language_inNP_of_standard_verifier (machine : StandardVerifier verify) :
    InNP language :=
  ⟨verify, ⟨machine⟩, witnessPolynomial, language_iff_polynomial_witness⟩

theorem language_inNP_of_equivalent_executor (execute : Bits → Bits → Bool)
    (machine : StandardVerifier execute) (refines : ∀ x y, execute x y = verify x y) :
    InNP language := by
  refine ⟨execute, ⟨machine⟩, witnessPolynomial, ?_⟩
  intro x
  simpa only [refines] using language_iff_polynomial_witness x

end UAVProof.TreeBudgetSparseNPBridge
