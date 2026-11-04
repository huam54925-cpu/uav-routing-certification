import LeanCompletion.UAV.TreeBudgetMemoState

/-! Complete residual search with an explicit, input-local association-list cache.
Only a full state evaluation writes its own key. A failed candidate passes its
updated cache to the remaining candidates, without declaring the parent infeasible. -/
namespace UAVProof.TreeBudgetMemoSearch
open TreeFlowExistence TreeBudgetRow TreeBudgetResidualSearch TreeBudgetMemoState
open TreeBudgetCertificate
variable {n : ℕ}

/-- The child solver is fixed while the candidate suffix decreases. -/
def scanCandidates (solve : (Fin n → ℕ) → Cache n → Answer n × Cache n)
    (r : Fin n → ℕ) : List (Fin n → ℕ) → Cache n → Answer n × Cache n
  | [], cache => (none, cache)
  | p :: ps, cache =>
    if ∀ v, p v ≤ r v then
      let out := solve (r - p) cache
      match out.1 with
      | some rows => (some (p :: rows), out.2)
      | none => scanCandidates solve r ps out.2
    else scanCandidates solve r ps cache

/-- Every recursive depth reuses the complete list ps, including repeated rows. -/
def memoRowsWith (ps : List (Fin n → ℕ)) :
    ℕ → (Fin n → ℕ) → Cache n → Answer n × Cache n
  | 0, r, cache =>
    match lookup cache (0, r) with
    | some answer => (answer, cache)
    | none =>
      let answer := if r = 0 then some [] else none
      (answer, insert cache (0, r) answer)
  | k + 1, r, cache =>
    match lookup cache (k + 1, r) with
    | some answer => (answer, cache)
    | none =>
      let out := scanCandidates (memoRowsWith ps k) r ps cache
      (out.1, insert out.2 (k + 1, r) out.1)

def memoRows (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ)
    (k : ℕ) (r : Fin n → ℕ) (cache : Cache n) : Answer n × Cache n :=
  memoRowsWith (TreeBudgetFiniteSearch.candidates R H s T) k r cache

/-- Failure rules out only the supplied suffix, not all legal first rows. -/
def ScanSpec (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ)
    (k : ℕ) (r : Fin n → ℕ) (ps : List (Fin n → ℕ)) : Answer n → Prop
  | some rows => ResidualWitness R H s T (k + 1) r rows
  | none => ∀ p ∈ ps, p ≤ r → ¬ ResidualFeasible R H s T k (r - p)

theorem scanCandidates_spec (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ)
    (solve : (Fin n → ℕ) → Cache n → Answer n × Cache n)
    (hsolve : ∀ r cache, CacheValid R H s T cache →
      CacheValid R H s T (solve r cache).2 ∧ AnswerValid R H s T (k, r) (solve r cache).1)
    (r : Fin n → ℕ) (ps : List (Fin n → ℕ))
    (hp : ∀ p ∈ ps, RowValid R H s T p) (cache : Cache n)
    (hc : CacheValid R H s T cache) :
    CacheValid R H s T (scanCandidates solve r ps cache).2 ∧
      ScanSpec R H s T k r ps (scanCandidates solve r ps cache).1 := by
  induction ps generalizing cache with
  | nil => exact ⟨hc, by simp [scanCandidates, ScanSpec]⟩
  | cons p ps ih =>
    have ht : ∀ q ∈ ps, RowValid R H s T q := fun q hq => hp q (by simp [hq])
    by_cases hle : ∀ v, p v ≤ r v
    · obtain ⟨hv, ha⟩ := hsolve (r - p) cache hc
      cases he : (solve (r - p) cache).1 with
      | some rows =>
        simp only [he, AnswerValid] at ha
        simp only [scanCandidates, if_pos hle, he, ScanSpec]
        exact ⟨hv, (residualWitness_cons_iff ..).mpr ⟨hp p (by simp), hle, ha⟩⟩
      | none =>
        simp only [he, AnswerValid] at ha
        obtain ⟨hv', hs⟩ := ih ht (solve (r - p) cache).2 hv
        simp only [scanCandidates, if_pos hle, he]
        refine ⟨hv', ?_⟩
        cases ho : (scanCandidates solve r ps (solve (r - p) cache).2).1 with
        | some rows => simpa only [ho, ScanSpec] using hs
        | none =>
          simp only [ho, ScanSpec] at hs ⊢
          intro q hq hqr
          rcases List.mem_cons.mp hq with hq | hq
          · subst q; exact ha
          · exact hs q hq hqr
    · obtain ⟨hv, hs⟩ := ih ht cache hc
      simp only [scanCandidates, if_neg hle]
      refine ⟨hv, ?_⟩
      cases ho : (scanCandidates solve r ps cache).1 with
      | some rows => simpa only [ho, ScanSpec] using hs
      | none =>
        simp only [ho, ScanSpec] at hs ⊢
        intro q hq hqr
        rcases List.mem_cons.mp hq with hq | hq
        · subst q; exact (hle hqr).elim
        · exact hs q hq hqr

theorem memoRowsWith_spec (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (ps : List (Fin n → ℕ))
    (hp : ∀ p, p ∈ ps ↔ RowValid R H s T p)
    (k : ℕ) (r : Fin n → ℕ) (cache : Cache n) (hc : CacheValid R H s T cache) :
    CacheValid R H s T (memoRowsWith ps k r cache).2 ∧
      AnswerValid R H s T (k, r) (memoRowsWith ps k r cache).1 := by
  induction k generalizing r cache with
  | zero =>
    cases he : lookup cache (0, r) with
    | some answer => exact ⟨by simpa [memoRowsWith, he] using hc,
        by simpa [memoRowsWith, he] using hc (0, r) answer he⟩
    | none =>
      have ha : AnswerValid R H s T (0, r) (if r = 0 then some [] else none) := by
        by_cases hr : r = 0
        · simp [hr, AnswerValid, ResidualWitness]
        · simp [hr, AnswerValid, residualFeasible_zero_iff]
      simpa only [memoRowsWith, he] using
        And.intro (cacheValid_insert R H s T cache (0, r) _ hc ha) ha
  | succ k ih =>
    cases he : lookup cache (k + 1, r) with
    | some answer => exact ⟨by simpa [memoRowsWith, he] using hc,
        by simpa [memoRowsWith, he] using hc (k + 1, r) answer he⟩
    | none =>
      obtain ⟨hv, hs⟩ := scanCandidates_spec R H s T k (memoRowsWith ps k)
        ih r ps (fun p h => (hp p).mp h) cache hc
      have ha : AnswerValid R H s T (k + 1, r)
          (scanCandidates (memoRowsWith ps k) r ps cache).1 := by
        cases ho : (scanCandidates (memoRowsWith ps k) r ps cache).1 with
        | some rows => simpa only [ho, ScanSpec, AnswerValid] using hs
        | none =>
          simp only [ho, ScanSpec] at hs
          change ¬ ResidualFeasible R H s T (k + 1) r
          intro hf
          obtain ⟨p, hv, hle, hf⟩ := (residualFeasible_succ_iff ..).mp hf
          exact hs p ((hp p).mpr hv) hle hf
      simpa only [memoRowsWith, he] using
        And.intro (cacheValid_insert R H s T _ (k + 1, r) _ hv ha) ha

theorem memoRows_spec (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (hc : CacheValid R H s T cache) :
    CacheValid R H s T (memoRows R H s T k r cache).2 ∧
      AnswerValid R H s T (k, r) (memoRows R H s T k r cache).1 :=
  memoRowsWith_spec R H s T _ (fun _ => TreeBudgetFiniteSearch.mem_candidates ..) k r cache hc

/-- This representation invariant does not require semantic validity. -/
theorem scanCandidates_preserves (P : Cache n → Prop)
    (solve : (Fin n → ℕ) → Cache n → Answer n × Cache n)
    (hsolve : ∀ r cache, P cache → P (solve r cache).2)
    (r : Fin n → ℕ) (ps : List (Fin n → ℕ)) (cache : Cache n) (hc : P cache) :
    P (scanCandidates solve r ps cache).2 := by
  induction ps generalizing cache with
  | nil => exact hc
  | cons p ps ih =>
    simp only [scanCandidates]
    split_ifs with hle
    · cases he : (solve (r - p) cache).1 with
      | none => exact ih _ (hsolve _ _ hc)
      | some rows => exact hsolve _ _ hc
    · exact ih _ hc

theorem memoRowsWith_nodup (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ)
    (cache : Cache n) (hc : KeysNodup cache) : KeysNodup (memoRowsWith ps k r cache).2 := by
  induction k generalizing r cache with
  | zero =>
    cases he : lookup cache (0, r) <;> simp only [memoRowsWith, he]
    · exact keysNodup_insert _ _ _ hc
    · exact hc
  | succ k ih =>
    cases he : lookup cache (k + 1, r) <;> simp only [memoRowsWith, he]
    · exact keysNodup_insert _ _ _ (scanCandidates_preserves KeysNodup _ ih r ps cache hc)
    · exact hc

theorem memoRows_nodup (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (hc : KeysNodup cache) : KeysNodup (memoRows R H s T k r cache).2 :=
  memoRowsWith_nodup _ k r cache hc

theorem memoRowsWith_lookup (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ)
    (cache : Cache n) : lookup (memoRowsWith ps k r cache).2 (k, r) =
      some (memoRowsWith ps k r cache).1 := by
  cases k <;> simp only [memoRowsWith] <;> split <;> simp_all

theorem memoRows_lookup (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n) :
    lookup (memoRows R H s T k r cache).2 (k, r) = some (memoRows R H s T k r cache).1 :=
  memoRowsWith_lookup _ k r cache

theorem memoRowsWith_hit (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ)
    (cache : Cache n) (answer : Answer n) (hh : lookup cache (k, r) = some answer) :
    memoRowsWith ps k r cache = (answer, cache) := by
  cases k <;> simp [memoRowsWith, hh]

theorem memoRows_hit (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (answer : Answer n) (hh : lookup cache (k, r) = some answer) :
    memoRows R H s T k r cache = (answer, cache) := memoRowsWith_hit _ k r cache answer hh

/-- Previously visible answers are retained exactly, even for an arbitrary raw cache. -/
def CacheExtends (before after : Cache n) : Prop :=
  ∀ q answer, lookup before q = some answer → lookup after q = some answer

theorem memoRowsWith_extends (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ)
    (cache : Cache n) : CacheExtends cache (memoRowsWith ps k r cache).2 := by
  induction k generalizing r cache with
  | zero =>
    intro q answer hh
    cases he : lookup cache (0, r) with
    | some a => simpa only [memoRowsWith, he] using hh
    | none =>
      have hne : q ≠ (0, r) := by rintro rfl; rw [he] at hh; contradiction
      simpa only [memoRowsWith, he, lookup_insert_other _ _ _ _ hne] using hh
  | succ k ih =>
    intro q answer hh
    cases he : lookup cache (k + 1, r) with
    | some a => simpa only [memoRowsWith, he] using hh
    | none =>
      have hne : q ≠ (k + 1, r) := by rintro rfl; rw [he] at hh; contradiction
      have hp := scanCandidates_preserves (fun c => lookup c q = some answer)
        (memoRowsWith ps k) (fun r c hc => ih r c q answer hc) r ps cache hh
      simpa only [memoRowsWith, he, lookup_insert_other _ _ _ _ hne] using hp

theorem memoRows_extends (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n) :
    CacheExtends cache (memoRows R H s T k r cache).2 := memoRowsWith_extends _ k r cache

theorem memoRows_repeat (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n) :
    memoRows R H s T k r (memoRows R H s T k r cache).2 = memoRows R H s T k r cache := by
  rw [memoRows_hit R H s T k r _ _ (memoRows_lookup R H s T k r cache)]

theorem memoRows_sound (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (rows : Rows n) (hc : CacheValid R H s T cache)
    (hs : (memoRows R H s T k r cache).1 = some rows) :
    ResidualWitness R H s T k r rows := by
  have ha := (memoRows_spec R H s T k r cache hc).2
  simpa only [hs, AnswerValid] using ha

theorem memoRows_correct (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (hc : CacheValid R H s T cache) :
    (memoRows R H s T k r cache).1.isSome = true ↔ ResidualFeasible R H s T k r := by
  have ha := (memoRows_spec R H s T k r cache hc).2
  cases he : (memoRows R H s T k r cache).1 with
  | none =>
    have hn : ¬ ResidualFeasible R H s T k r := by
      simpa only [he, AnswerValid] using ha
    simp [hn]
  | some rows =>
    have hw : ResidualWitness R H s T k r rows := by simpa only [he, AnswerValid] using ha
    simp only [Option.isSome_some, true_iff]
    exact ⟨rows, hw⟩

theorem memoRows_none_iff (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (hc : CacheValid R H s T cache) :
    (memoRows R H s T k r cache).1 = none ↔ ¬ ResidualFeasible R H s T k r := by
  rw [← memoRows_correct R H s T k r cache hc]
  cases (memoRows R H s T k r cache).1 <;> simp

theorem memoRows_isSome_eq_searchRows (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cache : Cache n)
    (hc : CacheValid R H s T cache) :
    (memoRows R H s T k r cache).1.isSome = (searchRows R H s T k r).isSome := by
  apply Bool.eq_iff_iff.mpr
  exact (memoRows_correct R H s T k r cache hc).trans (searchRows_correct ..).symm

end UAVProof.TreeBudgetMemoSearch

#print axioms UAVProof.TreeBudgetMemoSearch.scanCandidates_spec
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_spec
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_nodup
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_lookup
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_hit
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_extends
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_repeat
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_sound
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_correct
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_none_iff
#print axioms UAVProof.TreeBudgetMemoSearch.memoRows_isSome_eq_searchRows
