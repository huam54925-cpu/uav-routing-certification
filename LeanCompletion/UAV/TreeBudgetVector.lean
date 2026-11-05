import LeanCompletion.UAV.TreeBudgetPatterns

/-! An actual array-backed representation of finite natural-valued rows.
`Vector` contains an `Array` and a size proof. Decoding is used only to state
semantic correspondence; comparisons traverse arrays and subtraction produces
a materialized array. No operation-count or bit-cost claim is made here. -/
namespace UAVProof.TreeBudgetVector
open TreeFlowExistence
variable {n : ℕ}

def decode (p : Vector ℕ n) : Fin n → ℕ := fun i => p[i]

def encode (p : Fin n → ℕ) : Vector ℕ n := Vector.ofFn p

@[simp] theorem decode_encode (p : Fin n → ℕ) : decode (encode p) = p := by
  funext i
  simp [decode, encode]

@[simp] theorem encode_decode (p : Vector ℕ n) : encode (decode p) = p := by
  apply Vector.ext
  intro i hi
  simp [encode, decode]

theorem decode_injective : Function.Injective (decode (n := n)) := by
  intro p q h
  simpa using congrArg encode h

/-- Materialize coordinatewise equality flags, then test them with `all`. -/
def eqB (p q : Vector ℕ n) : Bool :=
  (p.zipWith (fun a b => decide (a = b)) q).all id

/-- Guard comparison is a finite array traversal. -/
def leB (p q : Vector ℕ n) : Bool :=
  (p.zipWith (fun a b => decide (a ≤ b)) q).all id

def isZero (p : Vector ℕ n) : Bool := p.all (fun a => decide (a = 0))

theorem eqB_eq_true (p q : Vector ℕ n) : eqB p q = true ↔ decode p = decode q := by
  simp only [eqB, Vector.all_eq_true, Vector.getElem_zipWith, id_eq, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact h i.val i.isLt
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

theorem leB_eq_true (p q : Vector ℕ n) : leB p q = true ↔ decode p ≤ decode q := by
  simp only [leB, Vector.all_eq_true, Vector.getElem_zipWith, id_eq, decide_eq_true_eq]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

theorem isZero_eq_true (p : Vector ℕ n) : isZero p = true ↔ decode p = 0 := by
  simp only [isZero, Vector.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact h i.val i.isLt
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

/-- Coordinatewise truncated subtraction; no guard is required for its semantics. -/
def sub (p q : Vector ℕ n) : Vector ℕ n := p.zipWith Nat.sub q

@[simp] theorem decode_sub (p q : Vector ℕ n) : decode (sub p q) = decode p - decode q := by
  funext i
  simp [decode, sub]

/-- Normalize the stored root coordinate, leaving all other array cells intact. -/
def normalize (R : RootedTree (Fin n)) (p : Vector ℕ n) : Vector ℕ n :=
  p.set R.root.val 0 R.root.isLt

@[simp] theorem decode_normalize (R : RootedTree (Fin n)) (p : Vector ℕ n) :
    decode (normalize R p) = TreeBudgetPatterns.normalize R (decode p) := by
  funext i
  simp [decode, normalize, TreeBudgetPatterns.normalize, Vector.getElem_set, Fin.ext_iff,
    eq_comm]

end UAVProof.TreeBudgetVector

#print axioms UAVProof.TreeBudgetVector.decode_encode
#print axioms UAVProof.TreeBudgetVector.encode_decode
#print axioms UAVProof.TreeBudgetVector.decode_injective
#print axioms UAVProof.TreeBudgetVector.eqB_eq_true
#print axioms UAVProof.TreeBudgetVector.leB_eq_true
#print axioms UAVProof.TreeBudgetVector.isZero_eq_true
#print axioms UAVProof.TreeBudgetVector.decode_sub
#print axioms UAVProof.TreeBudgetVector.decode_normalize
