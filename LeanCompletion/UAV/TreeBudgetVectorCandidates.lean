import LeanCompletion.UAV.TreeBudgetFiniteSearch
import LeanCompletion.UAV.TreeBudgetVectorChecker

/-! Ordered candidate enumeration on materialized vectors. The recursive
enumerator constructs vectors directly, with the same head-first order as the
function-valued reference. Normalize the root bound before enumeration; keep
the original bound for checking. The correspondence is list equality, including
order and multiplicity. No search/cache simulation or time bound is claimed. -/
namespace UAVProof.TreeBudgetVectorCandidates

open TreeFlowExistence TreeBudgetVector TreeBudgetVectorChecker TreeBudgetCertificate
variable {n : ℕ}

def emptyV : Vector ℕ 0 := Vector.ofFn Fin.elim0

def tailV (p : Vector ℕ (n + 1)) : Vector ℕ n :=
  Vector.ofFn fun i => p[i.succ]

def consV (a : ℕ) (p : Vector ℕ n) : Vector ℕ (n + 1) :=
  Vector.ofFn (Fin.cons a (decode p))

@[simp] theorem decode_emptyV : decode emptyV = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

@[simp] theorem decode_tailV (p : Vector ℕ (n + 1)) :
    decode (tailV p) = fun i => decode p i.succ := by
  funext i
  simp [decode, tailV]

@[simp] theorem decode_consV (a : ℕ) (p : Vector ℕ n) :
    decode (consV a p) = Fin.cons a (decode p) := by
  funext i
  simp [decode, consV]

/-- The head range is the outer loop; the recursively enumerated tail is inner. -/
def boundedVectorsV : (n : ℕ) → Vector ℕ n → List (Vector ℕ n)
  | 0, _ => [emptyV]
  | n + 1, b => (List.range (b[0] + 1)).flatMap fun a =>
      (boundedVectorsV n (tailV b)).map (consV a)

theorem map_decode_boundedVectorsV (n : ℕ) (b : Vector ℕ n) :
    (boundedVectorsV n b).map decode =
      TreeBudgetFiniteSearch.boundedVectors n (decode b) := by
  induction n with
  | zero => simp [boundedVectorsV, TreeBudgetFiniteSearch.boundedVectors]
  | succ n ih =>
    simp only [boundedVectorsV, TreeBudgetFiniteSearch.boundedVectors,
      List.map_flatMap, List.map_map]
    congr 1
    funext a
    have ht := ih (tailV b)
    rw [decode_tailV] at ht
    rw [← ht]
    simp [Function.comp_def]

theorem decode_normalize_eq_bound (R : RootedTree (Fin n)) (H : Vector ℕ n) :
    decode (TreeBudgetVector.normalize R H) = TreeBudgetPatterns.bound R (decode H) := by
  rw [decode_normalize]
  rfl

/-- Stable filtering commutes with decoding. Neither injectivity nor no-duplicate
assumptions are needed, so repeated accepted values retain their multiplicity. -/
theorem map_filter_decode {α β : Type*} (δ : α → β) (q : α → Bool) (p : β → Bool)
    (hq : ∀ x, q x = p (δ x)) (xs : List α) :
    (xs.filter q).map δ = (xs.map δ).filter p := by
  have hqp : q = p ∘ δ := funext hq
  rw [hqp, List.filter_map]

/-- A positive scale may be used with arbitrary signed fees and budget. -/
theorem rowValidB_eq_decide (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (p : Vector ℕ n) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, ((A[v] : ℤ) : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    rowValidB R H A AT p = decide (RowValid R (decode H) s T (decode p)) := by
  apply Bool.eq_iff_iff.mpr
  simpa using rowValidB_eq_true_iff R H A AT p s T D hD hA hAT

def candidatesV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) : List (Vector ℕ n) :=
  (boundedVectorsV n (TreeBudgetVector.normalize R H)).filter (rowValidB R H A AT)

theorem map_decode_candidatesV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, ((A[v] : ℤ) : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    (candidatesV R H A AT).map decode =
      TreeBudgetFiniteSearch.candidates R (decode H) s T := by
  unfold candidatesV TreeBudgetFiniteSearch.candidates
  rw [map_filter_decode decode (rowValidB R H A AT)
    (fun p => decide (RowValid R (decode H) s T p))
    (fun p => rowValidB_eq_decide R H A AT p s T D hD hA hAT)]
  rw [map_decode_boundedVectorsV, decode_normalize_eq_bound]

/-- Raw fraction entry point. Scale all fees and the budget once, outside the
candidate filter. Denominators may be unreduced and numerators may be signed. -/
def candidatesVScaled (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT : ℕ) : List (Vector ℕ n) :=
  let A := scaleFees a b bT
  let AT := scaleBudget b aT bT
  candidatesV R H A AT

theorem map_decode_candidatesV_scaled (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    (candidatesVScaled R H a b aT bT).map decode =
      TreeBudgetFiniteSearch.candidates R (decode H)
        (fun v => (a[v] : ℚ) / (b[v] : ℚ)) ((aT : ℚ) / (bT : ℚ)) := by
  unfold candidatesVScaled candidatesV TreeBudgetFiniteSearch.candidates
  rw [map_filter_decode decode _
    (fun p => decide (RowValid R (decode H)
      (fun v => (a[v] : ℚ) / (b[v] : ℚ)) ((aT : ℚ) / (bT : ℚ)) p))]
  · rw [map_decode_boundedVectorsV, decode_normalize_eq_bound]
  · intro p
    apply Bool.eq_iff_iff.mpr
    simpa using rowValidB_scaled_eq_true_iff R H a b aT bT p hb hbT

end UAVProof.TreeBudgetVectorCandidates

#print axioms UAVProof.TreeBudgetVectorCandidates.decode_emptyV
#print axioms UAVProof.TreeBudgetVectorCandidates.decode_tailV
#print axioms UAVProof.TreeBudgetVectorCandidates.decode_consV
#print axioms UAVProof.TreeBudgetVectorCandidates.map_decode_boundedVectorsV
#print axioms UAVProof.TreeBudgetVectorCandidates.decode_normalize_eq_bound
#print axioms UAVProof.TreeBudgetVectorCandidates.map_filter_decode
#print axioms UAVProof.TreeBudgetVectorCandidates.rowValidB_eq_decide
#print axioms UAVProof.TreeBudgetVectorCandidates.map_decode_candidatesV
#print axioms UAVProof.TreeBudgetVectorCandidates.map_decode_candidatesV_scaled
