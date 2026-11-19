import LeanCompletion.UAV.TreeBudgetSparseCostedCheck
import LeanCompletion.UAV.TreeBudgetCostedInput

/-! Checked frontend with measured binary guards, including shape, tree,
denominator, route-count and certificate-dimension rejection. -/
namespace UAVProof.TreeBudgetSparseCostedFrontend
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCandidates
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedInput TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparseExecutionWidths TreeBudgetSparseCostedCheck TreeBudgetSparseCostedParsing

theorem thenD_work {α β : Type} (a : Costed (Option α)) (f : α → Costed (Option β)) (K : ℕ)
    (h : ∀ x, a.value = some x → work (f x) ≤ K) : work (thenD a f) ≤ work a + K + 1 := by
  cases ha : a.value with
  | none => simp only [thenD, ha, work]; omega
  | some x => have := h x ha; simp only [thenD, ha, work] at *; omega

def rootGuardD (J : Input) (m : ℕ) : Costed (Option Instance) :=
  let roots := rootCountCost J.parents J.H
  let test := eqNatD m roots.value
  if h : test.value = true then
    ⟨some ⟨J, m, by simpa only [test, eqNatD_value, decide_eq_true_eq] using h⟩,
      roots.steps + test.steps + 2, roots.allocations + test.allocations + 2⟩
  else ⟨none, roots.steps + test.steps + 2, roots.allocations + test.allocations⟩

@[simp] theorem rootGuardD_value (J : Input) (m : ℕ) :
    (rootGuardD J m).value =
      if h : m = (rootCountCost J.parents J.H).value then some ⟨J, m, h⟩ else none := by
  simp only [rootGuardD, eqNatD_value, decide_eq_true_eq]
  split_ifs <;> rfl

def decodeSpecifiedD (m : ℕ) (raw : RawInput) : Costed (Option Instance) :=
  thenD (decodeRawCost raw) (fun J => rootGuardD J m)

@[simp] theorem decodeSpecifiedD_value (m : ℕ) (raw : RawInput) :
    (decodeSpecifiedD m raw).value = decodeSpecified m raw := by
  simp [decodeSpecifiedD, decodeSpecified]

def parseInstanceD (input : Bits) : Costed (Option Instance) :=
  thenD (parseSpecifiedD input) fun (m, raw) => decodeSpecifiedD m raw

@[simp] theorem parseInstanceD_value (input : Bits) :
    (parseInstanceD input).value = parseInstance input := by simp [parseInstanceD, parseInstance]

def sizesD (n : ℕ) (xs : RawCertificate) : Costed Bool :=
  allD (fun e =>
    let len := lengthD e.2
    let eq := eqNatD len.value n
    ⟨eq.value, len.steps + eq.steps + 1, len.allocations + eq.allocations⟩) xs

@[simp] theorem sizesD_value (n : ℕ) (xs : RawCertificate) :
    (sizesD n xs).value = decide (Sized n xs) := by
  apply Bool.eq_iff_iff.mpr
  simp [sizesD, Sized, List.all_eq_true]

def finishCertificateD (n : ℕ) (xs : RawCertificate) : Costed (Option (TreeBudgetCertificate.Certificate (Fin n))) :=
  let test := sizesD n xs
  if h : test.value = true then
    ⟨some (ofRaw n xs (by simpa only [test, sizesD_value, decide_eq_true_eq] using h)),
      test.steps + 1, test.allocations + 1⟩
  else ⟨none, test.steps + 1, test.allocations⟩

@[simp] theorem finishCertificateD_value (n : ℕ) (xs : RawCertificate) :
    (finishCertificateD n xs).value = decodeRawCertificate n xs := by
  simp only [finishCertificateD, sizesD_value, decide_eq_true_eq, decodeRawCertificate]
  split_ifs <;> rfl

def decodeCertificateD (n : ℕ) (wire : Bits) : Costed (Option (TreeBudgetCertificate.Certificate (Fin n))) :=
  thenD (parseRawD wire) (finishCertificateD n)

@[simp] theorem decodeCertificateD_value (n : ℕ) (wire : Bits) :
    (decodeCertificateD n wire).value = decodeCertificate n wire := by
  simp [decodeCertificateD, decodeCertificate]

def onSomeD {α : Type} (a : Costed (Option α)) (f : α → Costed Bool) : Costed Bool :=
  match a.value with
  | none => ⟨false, a.steps + 1, a.allocations⟩
  | some x => let out := f x
    ⟨out.value, a.steps + out.steps + 1, a.allocations + out.allocations⟩

@[simp] theorem onSomeD_value {α : Type} (a : Costed (Option α)) (f : α → Costed Bool) :
    (onSomeD a f).value = a.value.elim false (fun x => (f x).value) := by
  cases h : a.value <;> simp [onSomeD, h]

theorem onSomeD_work {α : Type} (a : Costed (Option α)) (f : α → Costed Bool) (K : ℕ)
    (h : ∀ x, a.value = some x → work (f x) ≤ K) : work (onSomeD a f) ≤ work a + K + 1 := by
  cases ha : a.value with
  | none => simp only [onSomeD, ha, work]; omega
  | some x => have := h x ha; simp only [onSomeD, ha, work] at *; omega

def verifyD (input wire : Bits) : Costed Bool :=
  onSomeD (parseInstanceD input) fun I =>
    onSomeD (decodeCertificateD I.data.n wire) (checkD I)

@[simp] theorem verifyD_value (input wire : Bits) : (verifyD input wire).value = verify input wire := by
  simp only [verifyD, onSomeD_value, parseInstanceD_value, decodeCertificateD_value, checkD_value]
  cases hp : parseInstance input with
  | none => simp [verify, hp]
  | some I => cases hc : decodeCertificate I.data.n wire <;> simp [verify, hp, checkWire, hc]

end UAVProof.TreeBudgetSparseCostedFrontend
