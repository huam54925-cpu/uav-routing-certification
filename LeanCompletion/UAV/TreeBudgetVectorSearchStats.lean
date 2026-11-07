import LeanCompletion.UAV.TreeBudgetVectorMemoSearch
import LeanCompletion.UAV.TreeBudgetSearchStats

/-! Independent vector execution with the reference six logical event counters.
The refinement preserves the actual answer, ordered cache and all counters for
arbitrary candidate lists and raw caches. Decoding occurs only in specifications.
These events are not a machine-time or bit-cost semantics. -/
namespace UAVProof.TreeBudgetVectorSearchStats
open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetVectorMemoSearch
open TreeBudgetSearchStats
variable {n : ℕ}

def decodeMeasured (out : Measured (AnswerV n × CacheV n)) :
    Measured (TreeBudgetMemoState.Answer n × TreeBudgetMemoState.Cache n) :=
  (decodeResult out.1, out.2)

@[simp] theorem decodeMeasured_bump (c : Counts) (out : Measured (AnswerV n × CacheV n)) :
    decodeMeasured (bump c out) = bump c (decodeMeasured out) := rfl

def lookupStatV : CacheV n → KeyV n → Option (AnswerV n) × ℕ
  | [], _ => (none, 0)
  | e :: cs, q => if keyEqB e.1 q then (some e.2, 1) else
      let out := lookupStatV cs q
      (out.1, out.2 + 1)

@[simp] theorem lookupStatV_erase (cs : CacheV n) (q : KeyV n) :
    (lookupStatV cs q).1 = lookupV cs q := by
  induction cs with
  | nil => rfl
  | cons e cs ih => simp only [lookupStatV, lookupV]; split <;> simp_all

def insertStatV (cs : CacheV n) (q : KeyV n) (a : AnswerV n) : Measured (CacheV n) :=
  (insertV cs q a, { insertionScans := cs.length })

def witnessRowsV (cs : CacheV n) : ℕ :=
  (cs.map fun e => (e.2.getD []).length).sum

def scanStatV (solve : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (r : Vector ℕ n) : List (Vector ℕ n) → CacheV n → Measured (AnswerV n × CacheV n)
  | [], cs => ((none, cs), {})
  | p :: ps, cs => bump { candidates := 1 } <|
    if leB p r then
      let out := solve (sub r p) cs
      match out.1.1 with
      | some rows => ((some (p :: rows), out.1.2), out.2)
      | none => bump out.2 (scanStatV solve r ps out.1.2)
    else scanStatV solve r ps cs

theorem scanStatV_erase
    (solve : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (base : Vector ℕ n → CacheV n → AnswerV n × CacheV n)
    (h : ∀ r cs, (solve r cs).1 = base r cs)
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n) :
    (scanStatV solve r ps cs).1 = scanCandidatesV base r ps cs := by
  induction ps generalizing cs with
  | nil => rfl
  | cons p ps ih =>
    simp only [scanStatV, bump_erase, scanCandidatesV]
    split_ifs with hp
    · simp only [h]
      cases (base (sub r p) cs).1 <;> simp [bump, ih]
    · exact ih cs

def memoStatV (ps : List (Vector ℕ n)) :
    ℕ → Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n)
  | k, r, cs =>
    let found := lookupStatV cs (k, r)
    match found.1 with
    | some a => ((a, cs), { calls := 1, hits := 1, lookupComparisons := found.2 })
    | none =>
      let out := match k with
        | 0 => ((if isZero r then some [] else none, cs), ({} : Counts))
        | j + 1 => scanStatV (memoStatV ps j) r ps cs
      let saved := insertStatV out.1.2 (k, r) out.1.1
      ((out.1.1, saved.1),
        (Counts.add { calls := 1, expansions := 1, lookupComparisons := found.2 }
          out.2).add saved.2)

theorem memoStatV_erase (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n)
    (cs : CacheV n) : (memoStatV ps k r cs).1 = memoRowsWithV ps k r cs := by
  induction k generalizing r cs with
  | zero =>
    cases he : lookupV cs (0, r) <;>
      simp [memoStatV, lookupStatV_erase, he, memoRowsWithV, insertStatV]
  | succ k ih =>
    cases he : lookupV cs (k + 1, r) <;>
      simp [memoStatV, lookupStatV_erase, he, memoRowsWithV, insertStatV,
        scanStatV_erase _ _ ih]

theorem lookupStatV_refines (cs : CacheV n) (q : KeyV n) :
    ((lookupStatV cs q).1.map decodeAnswer, (lookupStatV cs q).2) =
      lookupStat (decodeCache cs) (decodeKey q) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    simp only [lookupStatV, decodeCache, List.map_cons, lookupStat]
    by_cases he : keyEqB e.1 q = true
    · have hf := (keyEqB_eq_true e.1 q).mp he
      simp [he, hf]
    · have hf : decodeKey e.1 ≠ decodeKey q := fun h => he ((keyEqB_eq_true ..).mpr h)
      simp only [he, Bool.false_eq_true, ↓reduceIte, hf]
      exact congrArg (fun out : Option (TreeBudgetMemoState.Answer n) × ℕ =>
        (out.1, out.2 + 1)) ih

theorem witnessRowsV_refines (cs : CacheV n) :
    witnessRowsV cs = witnessRows (decodeCache cs) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    rcases e with ⟨q, a⟩
    cases a <;> simp_all [witnessRowsV, witnessRows, decodeCache, decodeAnswer, decodeRows]

/-- The induction generalizes the cache: a failed child supplies the next cache. -/
theorem scanStatV_refines
    (solveV : Vector ℕ n → CacheV n → Measured (AnswerV n × CacheV n))
    (solve : (Fin n → ℕ) → TreeBudgetMemoState.Cache n →
      Measured (TreeBudgetMemoState.Answer n × TreeBudgetMemoState.Cache n))
    (h : ∀ r cs, decodeMeasured (solveV r cs) = solve (decode r) (decodeCache cs))
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n) :
    decodeMeasured (scanStatV solveV r ps cs) =
      scanStat solve (decode r) (ps.map decode) (decodeCache cs) := by
  induction ps generalizing cs with
  | nil => rfl
  | cons p ps ih =>
    simp only [scanStatV, List.map_cons, scanStat, decodeMeasured_bump]
    by_cases hp : leB p r = true
    · have hf : ∀ v, decode p v ≤ decode r v := (leB_eq_true p r).mp hp
      rw [if_pos hp, if_pos hf]
      have hs := h (sub r p) cs
      rw [decode_sub] at hs
      rw [← hs]
      cases he : solveV (sub r p) cs with
      | mk out counts =>
        rcases out with ⟨a, cache⟩
        cases a with
        | none =>
          simpa [decodeMeasured, decodeResult, decodeAnswer, bump] using
            (congrArg (bump ({ candidates := 1 } : Counts))
              (congrArg (bump counts) (ih cache)))
        | some rows => rfl
    · have hf : ¬ ∀ v, decode p v ≤ decode r v := fun h => hp ((leB_eq_true ..).mpr h)
      rw [if_neg hp, if_neg hf, ih]

/-- Exact execution refinement, with no validity or no-duplicate hypotheses. -/
theorem memoStatV_refines (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n)
    (cs : CacheV n) :
    decodeMeasured (memoStatV ps k r cs) =
      memoStat (ps.map decode) k (decode r) (decodeCache cs) := by
  induction k generalizing r cs with
  | zero =>
    have hl := lookupStatV_refines cs (0, r)
    simp only [decodeKey] at hl
    simp only [memoStat, ← hl, memoStatV]
    cases he : (lookupStatV cs (0, r)).1 with
    | some a => rfl
    | none =>
      by_cases hz : isZero r = true
      · have hf := (isZero_eq_true r).mp hz
        simp [hz, hf, decodeMeasured, decodeResult, insertStatV, insertStat, decodeKey]
      · have hf : decode r ≠ 0 := fun h => hz ((isZero_eq_true r).mpr h)
        simp [hz, hf, decodeMeasured, decodeResult, insertStatV, insertStat, decodeKey]
  | succ k ih =>
    have hl := lookupStatV_refines cs (k + 1, r)
    simp only [decodeKey] at hl
    have hs := scanStatV_refines (memoStatV ps k) (memoStat (ps.map decode) k) ih r ps cs
    simp only [memoStat, ← hl, memoStatV]
    cases he : (lookupStatV cs (k + 1, r)).1 with
    | some a => rfl
    | none =>
      simp only [Option.map_none]
      rw [← hs]
      simp [decodeMeasured, decodeResult, insertStatV, insertStat, decodeKey]

/-- Ordinary execution is independent of instrumentation, with the same result. -/
theorem scanCandidatesV_refines
    (solveV : Vector ℕ n → CacheV n → AnswerV n × CacheV n)
    (solve : (Fin n → ℕ) → TreeBudgetMemoState.Cache n →
      TreeBudgetMemoState.Answer n × TreeBudgetMemoState.Cache n)
    (h : ∀ r cs, decodeResult (solveV r cs) = solve (decode r) (decodeCache cs))
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n) :
    decodeResult (scanCandidatesV solveV r ps cs) =
      TreeBudgetMemoSearch.scanCandidates solve (decode r) (ps.map decode) (decodeCache cs) := by
  have hs := scanStatV_refines (fun r cs => (solveV r cs, ({} : Counts)))
    (fun r cs => (solve r cs, ({} : Counts)))
    (fun r cs => congrArg (fun out => (out, ({} : Counts))) (h r cs)) r ps cs
  have he := congrArg Prod.fst hs
  change decodeResult (scanStatV _ r ps cs).1 = (scanStat _ _ _ _).1 at he
  rw [scanStatV_erase _ solveV (fun _ _ => rfl),
    scanStat_erase _ solve (fun _ _ => rfl)] at he
  exact he

/-- Ordinary execution preserves the complete answer and ordered cache. -/
theorem memoRowsWithV_refines (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n)
    (cs : CacheV n) :
    decodeResult (memoRowsWithV ps k r cs) =
      TreeBudgetMemoSearch.memoRowsWith (ps.map decode) k (decode r) (decodeCache cs) := by
  have h := congrArg Prod.fst (memoStatV_refines ps k r cs)
  simpa only [decodeMeasured, memoStatV_erase, memoStat_erase] using h

end UAVProof.TreeBudgetVectorSearchStats

#print axioms UAVProof.TreeBudgetVectorSearchStats.decodeMeasured_bump
#print axioms UAVProof.TreeBudgetVectorSearchStats.lookupStatV_erase
#print axioms UAVProof.TreeBudgetVectorSearchStats.scanStatV_erase
#print axioms UAVProof.TreeBudgetVectorSearchStats.memoStatV_erase
#print axioms UAVProof.TreeBudgetVectorSearchStats.lookupStatV_refines
#print axioms UAVProof.TreeBudgetVectorSearchStats.witnessRowsV_refines
#print axioms UAVProof.TreeBudgetVectorSearchStats.scanStatV_refines
#print axioms UAVProof.TreeBudgetVectorSearchStats.memoStatV_refines
#print axioms UAVProof.TreeBudgetVectorSearchStats.scanCandidatesV_refines
#print axioms UAVProof.TreeBudgetVectorSearchStats.memoRowsWithV_refines
