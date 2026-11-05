import LeanCompletion.UAV.TreeBudgetSearchStats
import LeanCompletion.UAV.TreeBudgetMemoBounds

/-! Operation accounting for the existing measured search: cache growth, exact
insertion scans, candidate checks and calls, including initial tree-entry bounds.
The generic results allow arbitrary candidate lists and raw caches, including
duplicate keys and semantically invalid answers. Tree-entry corollaries use the
existing finite-state bound. These are logical counts, not runtime or bit costs. -/
namespace UAVProof.TreeBudgetSearchStatsBounds
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMemoState TreeBudgetMemoSearch
open TreeBudgetSearchStats TreeBudgetMemoBounds
variable {n : ℕ}

/-- An absent key cannot cause the replacement filter to delete any old entry. -/
theorem filter_eq_self_of_lookup_none (cs : Cache n) (q : Key n)
    (hm : lookup cs q = none) :
    cs.filter (fun e => decide (e.1 ≠ q)) = cs := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    have he : e.1 ≠ q := by
      intro he
      simp [lookup, he] at hm
    have ht : lookup cs q = none := by
      simpa only [lookup, if_neg he] using hm
    rw [List.filter_cons_of_pos (by simp [he]), ih ht]

theorem insert_eq_cons_of_lookup_none (cs : Cache n) (q : Key n) (a : Answer n)
    (hm : lookup cs q = none) : insert cs q a = (q, a) :: cs := by
  simp only [TreeBudgetMemoState.insert, filter_eq_self_of_lookup_none cs q hm]

theorem insert_length_of_lookup_none (cs : Cache n) (q : Key n) (a : Answer n)
    (hm : lookup cs q = none) : (insert cs q a).length = cs.length + 1 := by
  rw [insert_eq_cons_of_lookup_none cs q a hm]
  rfl

/-- Depth k can only write keys of depth at most k. Unlike CacheExtends, this
preserves absent entries as well as existing answers, even in a raw cache. -/
theorem memoRowsWith_lookup_above (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) (q : Key n) (hq : k < q.1) :
    lookup (memoRowsWith ps k r cs).2 q = lookup cs q := by
  induction k generalizing r cs with
  | zero =>
    have hne : q ≠ (0, r) := by
      intro he
      have hf := congrArg Prod.fst he
      omega
    cases hm : lookup cs (0, r) with
    | none =>
      simpa only [memoRowsWith, hm] using
        lookup_insert_other cs (0, r) q (if r = 0 then some [] else none) hne
    | some a => simp only [memoRowsWith, hm]
  | succ k ih =>
    have hne : q ≠ (k + 1, r) := by
      intro he
      have hf := congrArg Prod.fst he
      omega
    cases hm : lookup cs (k + 1, r) with
    | some a => simp only [memoRowsWith, hm]
    | none =>
      have hs : lookup (scanCandidates (memoRowsWith ps k) r ps cs).2 q =
          lookup cs q := by
        apply scanCandidates_preserves (fun c => lookup c q = lookup cs q)
          (memoRowsWith ps k)
        · intro r' c hc
          exact (ih r' c (by omega)).trans hc
        · rfl
      simpa only [memoRowsWith, hm, lookup_insert_other _ _ _ _ hne] using hs

/-- A candidate suffix cannot fill the parent key before the parent inserts it. -/
theorem scan_parent_lookup_none (ps tail : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n)
    (hm : lookup cs (k + 1, r) = none) :
    lookup (scanCandidates (memoRowsWith ps k) r tail cs).2 (k + 1, r) = none := by
  apply scanCandidates_preserves (fun c => lookup c (k + 1, r) = none)
    (memoRowsWith ps k)
  · intro r' c hc
    exact (memoRowsWith_lookup_above ps k r' c (k + 1, r) (by omega)).trans hc
  · exact hm

theorem memoStat_lookup_above (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) (q : Key n) (hq : k < q.1) :
    lookup (memoStat ps k r cs).1.2 q = lookup cs q := by
  rw [memoStat_erase]
  exact memoRowsWith_lookup_above ps k r cs q hq

theorem scanStat_parent_lookup_none (ps tail : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n)
    (hm : lookup cs (k + 1, r) = none) :
    lookup (scanStat (memoStat ps k) r tail cs).1.2 (k + 1, r) = none := by
  rw [scanStat_erase _ _ (memoStat_erase ps k)]
  exact scan_parent_lookup_none ps tail k r cs hm

/-- Growth composes through failed children, skipped candidates and early success. -/
theorem scanStat_cache_length
    (solve : (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n))
    (hsolve : ∀ r cs, (solve r cs).1.2.length = cs.length + (solve r cs).2.expansions)
    (r : Fin n → ℕ) (ps : List (Fin n → ℕ)) (cs : Cache n) :
    (scanStat solve r ps cs).1.2.length =
      cs.length + (scanStat solve r ps cs).2.expansions := by
  induction ps generalizing cs with
  | nil => simp [scanStat]
  | cons p ps ih =>
    by_cases hp : ∀ v, p v ≤ r v
    · have hc := hsolve (r - p) cs
      cases ha : (solve (r - p) cs).1.1 with
      | none =>
        have ht := ih (solve (r - p) cs).1.2
        simp only [scanStat, if_pos hp, ha, bump, Counts.add]
        omega
      | some rows =>
        simpa only [scanStat, if_pos hp, ha, bump, Counts.add, Nat.zero_add] using hc
    · simpa only [scanStat, if_neg hp, bump, Counts.add, Nat.zero_add] using ih cs

/-- Exact list-length growth, without CacheValid, KeysNodup or row validity. -/
theorem memoStat_cache_length (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).1.2.length = cs.length + (memoStat ps k r cs).2.expansions := by
  induction k generalizing r cs with
  | zero =>
    cases hm : lookup cs (0, r) with
    | some a => simp [memoStat, lookupStat_erase, hm]
    | none =>
      simp [memoStat, lookupStat_erase, hm, insertStat, Counts.add,
        insert_length_of_lookup_none cs (0, r) _ hm]
  | succ k ih =>
    cases hm : lookup cs (k + 1, r) with
    | some a => simp [memoStat, lookupStat_erase, hm]
    | none =>
      have hs := scanStat_cache_length (memoStat ps k) ih r ps cs
      have hp := scanStat_parent_lookup_none ps ps k r cs hm
      simp only [memoStat, lookupStat_erase, hm, insertStat, Counts.add]
      rw [insert_length_of_lookup_none _ _ _ hp]
      dsimp
      omega

theorem memoStat_cache_length_mono (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    cs.length ≤ (memoStat ps k r cs).1.2.length := by
  rw [memoStat_cache_length]
  omega

/-- Cold execution has one retained entry per expansion. -/
theorem memoStat_empty_cache_length (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) :
    (memoStat ps k r emptyCache).1.2.length = (memoStat ps k r emptyCache).2.expansions := by
  simpa only [emptyCache, List.length_nil, Nat.zero_add] using
    memoStat_cache_length ps k r emptyCache

/-- Connect measured execution, erasure and the existing reachable-state bound. -/
theorem initial_expansions_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.expansions ≤ stateBound R H := by
  have hg : (memoRowsStat R H s T (rootCount R H) H emptyCache).1.2.length =
      (memoRowsStat R H s T (rootCount R H) H emptyCache).2.expansions :=
    memoStat_empty_cache_length _ _ _
  rw [← hg, memoRowsStat_erase]
  exact initial_cache_length_le R H s T

/-- Insertion-scan potential, kept division-free throughout the recursive proofs. -/
def triangle : ℕ → ℕ
  | 0 => 0
  | m + 1 => triangle m + m

@[simp] theorem triangle_zero : triangle 0 = 0 := rfl

@[simp] theorem triangle_succ (m : ℕ) : triangle (m + 1) = triangle m + m := rfl

theorem triangle_add (a b : ℕ) :
    triangle (a + b) = triangle a + a * b + triangle b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, triangle_succ, triangle_succ, ih]
    ring

theorem triangle_mono : Monotone triangle := by
  intro a b hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [triangle_add]
  omega

/-- The four remaining accounting facts. Growth is provided separately by the
already proved cache-length theorems. `P` is the full candidate-list length;
`budget` is the current suffix length for scans, and zero for state calls. -/
def Accounting (P budget rootCalls : ℕ) (before : Cache n)
    (out : Measured (Answer n × Cache n)) : Prop :=
  out.2.insertionScans + triangle before.length = triangle out.1.2.length ∧
  out.2.candidates ≤ budget + P * out.2.expansions ∧
  out.2.calls ≤ rootCalls + out.2.candidates ∧
  out.2.calls = out.2.hits + out.2.expansions

/-- Failed children pass their cache to the suffix: the intermediate potential
cancels. A successful child stops scanning, so no unvisited suffix is counted. -/
theorem scanStat_accounting (P : ℕ)
    (solve : (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n))
    (hsolve : ∀ r cs, Accounting P 0 1 cs (solve r cs))
    (r : Fin n → ℕ) (tail : List (Fin n → ℕ)) (cs : Cache n) :
    Accounting P tail.length 0 cs (scanStat solve r tail cs) := by
  induction tail generalizing cs with
  | nil => simp [scanStat, Accounting]
  | cons p tail ih =>
    by_cases hp : ∀ v, p v ≤ r v
    · have hc := hsolve (r - p) cs
      cases ha : (solve (r - p) cs).1.1 with
      | none =>
        have ht := ih (solve (r - p) cs).1.2
        simp only [scanStat, if_pos hp, ha, bump, Counts.add, Accounting,
          List.length_cons, Nat.zero_add] at hc ht ⊢
        rcases hc with ⟨hcScan, hcCand, hcCall, hcSplit⟩
        rcases ht with ⟨htScan, htCand, htCall, htSplit⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · nlinarith
        · omega
        · omega
      | some rows =>
        simp only [scanStat, if_pos hp, ha, bump, Counts.add, Accounting,
          List.length_cons, Nat.zero_add] at hc ⊢
        rcases hc with ⟨hcScan, hcCand, hcCall, hcSplit⟩
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · have ht := ih cs
      simp only [scanStat, if_neg hp, bump, Counts.add, Accounting,
        List.length_cons, Nat.zero_add] at ht ⊢
      rcases ht with ⟨htScan, htCand, htCall, htSplit⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Four accounting facts for arbitrary candidate lists and raw caches. The
parent's final insertion uses the previously proved absence of its key. -/
theorem memoStat_accounting (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    Accounting ps.length 0 1 cs (memoStat ps k r cs) := by
  induction k generalizing r cs with
  | zero =>
    cases hm : lookup cs (0, r) with
    | some a => simp [Accounting, memoStat, lookupStat_erase, hm]
    | none =>
      simp only [Accounting, memoStat, lookupStat_erase, hm, insertStat, Counts.add]
      rw [insert_length_of_lookup_none cs (0, r) _ hm]
      rw [triangle_succ]
      simp [Nat.add_comm]
  | succ k ih =>
    cases hm : lookup cs (k + 1, r) with
    | some a => simp [Accounting, memoStat, lookupStat_erase, hm]
    | none =>
      have hs := scanStat_accounting ps.length (memoStat ps k) ih r ps cs
      have hp := scanStat_parent_lookup_none ps ps k r cs hm
      rcases hs with ⟨hsScan, hsCand, hsCall, hsSplit⟩
      simp only [Accounting, memoStat, lookupStat_erase, hm, insertStat, Counts.add]
      rw [insert_length_of_lookup_none _ _ _ hp]
      simp only [triangle_succ, Nat.zero_add, Nat.add_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · omega
      · omega

/-- The actual child solver keeps the full list ps while tail is independent. -/
theorem scanStat_memoStat_accounting (ps tail : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    Accounting ps.length tail.length 0 cs (scanStat (memoStat ps k) r tail cs) :=
  scanStat_accounting ps.length (memoStat ps k) (memoStat_accounting ps k) r tail cs

theorem memoStat_insertionScans_potential (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.insertionScans + triangle cs.length =
      triangle (memoStat ps k r cs).1.2.length :=
  (memoStat_accounting ps k r cs).1

/-- The existing growth theorem converts the potential into an exact count. -/
theorem memoStat_insertionScans_eq (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.insertionScans =
      cs.length * (memoStat ps k r cs).2.expansions +
        triangle (memoStat ps k r cs).2.expansions := by
  have h := memoStat_insertionScans_potential ps k r cs
  rw [memoStat_cache_length, triangle_add] at h
  omega

theorem memoStat_candidates_le (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.candidates ≤ ps.length * (memoStat ps k r cs).2.expansions := by
  simpa only [Nat.zero_add] using (memoStat_accounting ps k r cs).2.1

theorem memoStat_calls_le (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.calls ≤ 1 + (memoStat ps k r cs).2.candidates :=
  (memoStat_accounting ps k r cs).2.2.1

theorem memoStat_calls_eq_hits_add_expansions (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.calls =
      (memoStat ps k r cs).2.hits + (memoStat ps k r cs).2.expansions :=
  (memoStat_accounting ps k r cs).2.2.2

/-- The closed form is introduced only after the recursive accounting proof. -/
theorem two_mul_triangle (e : ℕ) : 2 * triangle e = e * (e - 1) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [triangle_succ]
    cases e with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      nlinarith

theorem triangle_closed (e : ℕ) : triangle e = e * (e - 1) / 2 := by
  rw [← two_mul_triangle e]
  exact (Nat.mul_div_cancel_left (triangle e) (by decide)).symm

theorem memoStat_insertionScans_closed (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.insertionScans =
      cs.length * (memoStat ps k r cs).2.expansions +
        (memoStat ps k r cs).2.expansions * ((memoStat ps k r cs).2.expansions - 1) / 2 := by
  rw [memoStat_insertionScans_eq, triangle_closed]

/-- Candidate checks at the actual empty-cache tree entry, with candidate
generation excluded and P kept as the complete candidate-list length. -/
theorem initial_candidates_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.candidates ≤
      (TreeBudgetFiniteSearch.candidates R H s T).length * stateBound R H := by
  exact (memoStat_candidates_le _ _ _ _).trans
    (Nat.mul_le_mul_left _ (initial_expansions_le R H s T))

theorem initial_calls_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.calls ≤
      1 + (TreeBudgetFiniteSearch.candidates R H s T).length * stateBound R H := by
  exact (memoStat_calls_le _ _ _ _).trans
    (Nat.add_le_add_left (initial_candidates_le R H s T) 1)

/-- Monotonicity is applied to the potential, avoiding truncated subtraction. -/
theorem initial_insertionScans_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.insertionScans ≤
      triangle (stateBound R H) := by
  have hi : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.insertionScans =
      triangle (memoRowsStat R H s T (rootCount R H) H emptyCache).2.expansions := by
    simpa only [emptyCache, List.length_nil, Nat.zero_mul, Nat.zero_add] using
      memoStat_insertionScans_eq (TreeBudgetFiniteSearch.candidates R H s T)
        (rootCount R H) H emptyCache
  rw [hi]
  exact triangle_mono (initial_expansions_le R H s T)

theorem initial_insertionScans_le_closed (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.insertionScans ≤
      stateBound R H * (stateBound R H - 1) / 2 := by
  simpa only [triangle_closed] using initial_insertionScans_le R H s T

end UAVProof.TreeBudgetSearchStatsBounds

#print axioms UAVProof.TreeBudgetSearchStatsBounds.filter_eq_self_of_lookup_none
#print axioms UAVProof.TreeBudgetSearchStatsBounds.insert_eq_cons_of_lookup_none
#print axioms UAVProof.TreeBudgetSearchStatsBounds.insert_length_of_lookup_none
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoRowsWith_lookup_above
#print axioms UAVProof.TreeBudgetSearchStatsBounds.scan_parent_lookup_none
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_lookup_above
#print axioms UAVProof.TreeBudgetSearchStatsBounds.scanStat_parent_lookup_none
#print axioms UAVProof.TreeBudgetSearchStatsBounds.scanStat_cache_length
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_cache_length
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_cache_length_mono
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_empty_cache_length
#print axioms UAVProof.TreeBudgetSearchStatsBounds.initial_expansions_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.triangle_zero
#print axioms UAVProof.TreeBudgetSearchStatsBounds.triangle_succ
#print axioms UAVProof.TreeBudgetSearchStatsBounds.triangle_add
#print axioms UAVProof.TreeBudgetSearchStatsBounds.triangle_mono
#print axioms UAVProof.TreeBudgetSearchStatsBounds.scanStat_accounting
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_accounting
#print axioms UAVProof.TreeBudgetSearchStatsBounds.scanStat_memoStat_accounting
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_insertionScans_potential
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_insertionScans_eq
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_candidates_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_calls_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_calls_eq_hits_add_expansions
#print axioms UAVProof.TreeBudgetSearchStatsBounds.two_mul_triangle
#print axioms UAVProof.TreeBudgetSearchStatsBounds.triangle_closed
#print axioms UAVProof.TreeBudgetSearchStatsBounds.memoStat_insertionScans_closed
#print axioms UAVProof.TreeBudgetSearchStatsBounds.initial_candidates_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.initial_calls_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.initial_insertionScans_le
#print axioms UAVProof.TreeBudgetSearchStatsBounds.initial_insertionScans_le_closed
