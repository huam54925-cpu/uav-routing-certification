import LeanCompletion.UAV.TreeBudgetVectorSearchStats
import LeanCompletion.UAV.TreeBudgetVectorCandidates
import LeanCompletion.UAV.TreeBudgetMemoIntegration
import LeanCompletion.UAV.TreeBudgetCacheEntryBounds

/-! Tree-budget entry points for the independent vector executor. Candidate
generation is outside recursion; the normalized input and complete candidate
list are fixed throughout a run. Refinement transfers certificate semantics,
cache member invariants and logical event bounds, not a machine-time bound. -/
namespace UAVProof.TreeBudgetVectorMemoIntegration
open TreeFlowExistence TreeBudgetVector TreeBudgetVectorCandidates
open TreeBudgetVectorMemoState TreeBudgetVectorMemoSearch TreeBudgetVectorSearchStats
open TreeBudgetSearchStats TreeBudgetCacheEntryBounds TreeBudgetMemoReachability
open TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate TreeBudgetResidualSearch
open TreeBudgetParameterizedBounds TreeBudgetMemoBounds TreeBudgetStateParameters
variable {n : ℕ}

def memoRowsV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :=
  memoRowsWithV (candidatesV R H A AT) k r cs

def memoRowsStatV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :=
  memoStatV (candidatesV R H A AT) k r cs

theorem memoRowsV_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    decodeResult (memoRowsV R H A AT k r cs) =
      TreeBudgetMemoSearch.memoRows R (decode H) s T k (decode r) (decodeCache cs) := by
  unfold memoRowsV TreeBudgetMemoSearch.memoRows
  rw [memoRowsWithV_refines, map_decode_candidatesV R H A AT s T D hD hA hAT]

theorem memoRowsStatV_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    decodeMeasured (memoRowsStatV R H A AT k r cs) =
      memoRowsStat R (decode H) s T k (decode r) (decodeCache cs) := by
  unfold memoRowsStatV memoRowsStat
  rw [memoStatV_refines, map_decode_candidatesV R H A AT s T D hD hA hAT]

/-- Normalize before constructing the one candidate list used for the entire run. -/
def initialRowsV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (m : ℕ) :=
  let H0 := TreeBudgetVector.normalize R H
  memoRowsV R H0 A AT m H0 []

def initialRowsStatV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (m : ℕ) :=
  let H0 := TreeBudgetVector.normalize R H
  memoRowsStatV R H0 A AT m H0 []

theorem initialRowsV_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) :
    decodeResult (initialRowsV R H A AT m) =
      TreeBudgetMemoSearch.memoRows R (TreeBudgetPatterns.normalize R (decode H)) s T m
        (TreeBudgetPatterns.normalize R (decode H)) TreeBudgetMemoState.emptyCache := by
  simpa [initialRowsV, decodeCache, TreeBudgetMemoState.emptyCache] using
    memoRowsV_refines R (TreeBudgetVector.normalize R H) A AT s T D hD hA hAT m
      (TreeBudgetVector.normalize R H) []

theorem initialRowsStatV_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) :
    decodeMeasured (initialRowsStatV R H A AT m) =
      memoRowsStat R (TreeBudgetPatterns.normalize R (decode H)) s T m
        (TreeBudgetPatterns.normalize R (decode H)) TreeBudgetMemoState.emptyCache := by
  simpa [initialRowsStatV, decodeCache, TreeBudgetMemoState.emptyCache] using
    memoRowsStatV_refines R (TreeBudgetVector.normalize R H) A AT s T D hD hA hAT m
      (TreeBudgetVector.normalize R H) []

/-- Decode only the final vector witness to construct the existing certificate. -/
def searchMemoV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (m : ℕ) : Option (Certificate (Fin n)) :=
  (decodeAnswer (initialRowsV R H A AT m).1).map unitCertificate

theorem searchMemoV_eq (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) :
    searchMemoV R H A AT m = TreeBudgetMemoIntegration.searchMemo R (decode H) m s T := by
  have he := congrArg Prod.fst (initialRowsV_refines R H A AT s T D hD hA hAT m)
  exact congrArg (Option.map unitCertificate) he

theorem searchMemoV_sound (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) (C : Certificate (Fin n))
    (hc : searchMemoV R H A AT m = some C) :
    checkCertificate R (decode H) m s T C = true := by
  rw [searchMemoV_eq R H A AT s T D hD hA hAT m] at hc
  exact TreeBudgetMemoIntegration.searchMemo_sound R (decode H) m s T C hc

theorem searchMemoV_correct (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) :
    (searchMemoV R H A AT m).isSome = true ↔ MatrixFeasible R (decode H) m s T := by
  rw [searchMemoV_eq R H A AT s T D hD hA hAT m]
  exact TreeBudgetMemoIntegration.searchMemo_correct ..

theorem searchMemoV_none_iff (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (m : ℕ) :
    searchMemoV R H A AT m = none ↔ ¬ MatrixFeasible R (decode H) m s T := by
  rw [searchMemoV_eq R H A AT s T D hD hA hAT m]
  exact TreeBudgetMemoIntegration.searchMemo_none_iff ..

def initialRowsVScaled (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ) :=
  let H0 := TreeBudgetVector.normalize R H
  memoRowsWithV (candidatesVScaled R H0 a b aT bT) m H0 []

def initialRowsStatVScaled (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ) :=
  let H0 := TreeBudgetVector.normalize R H
  memoStatV (candidatesVScaled R H0 a b aT bT) m H0 []

theorem initialRowsVScaled_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    decodeResult (initialRowsVScaled R H a b aT bT m) =
      TreeBudgetMemoSearch.memoRows R (TreeBudgetPatterns.normalize R (decode H))
        (fun v => (a[v] : ℚ) / (b[v] : ℚ)) ((aT : ℚ) / (bT : ℚ)) m
        (TreeBudgetPatterns.normalize R (decode H)) TreeBudgetMemoState.emptyCache := by
  simp only [initialRowsVScaled, memoRowsWithV_refines,
    map_decode_candidatesV_scaled R _ a b aT bT hb hbT, decode_normalize]
  rfl

theorem initialRowsStatVScaled_refines (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    decodeMeasured (initialRowsStatVScaled R H a b aT bT m) =
      memoRowsStat R (TreeBudgetPatterns.normalize R (decode H))
        (fun v => (a[v] : ℚ) / (b[v] : ℚ)) ((aT : ℚ) / (bT : ℚ)) m
        (TreeBudgetPatterns.normalize R (decode H)) TreeBudgetMemoState.emptyCache := by
  simp only [initialRowsStatVScaled, memoStatV_refines,
    map_decode_candidatesV_scaled R _ a b aT bT hb hbT, decode_normalize]
  rfl

def searchMemoVScaled (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ) :
    Option (Certificate (Fin n)) :=
  (decodeAnswer (initialRowsVScaled R H a b aT bT m).1).map unitCertificate

theorem searchMemoVScaled_eq (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    searchMemoVScaled R H a b aT bT m =
      TreeBudgetMemoIntegration.searchMemo R (decode H) m
        (fun v => (a[v] : ℚ) / (b[v] : ℚ)) ((aT : ℚ) / (bT : ℚ)) := by
  exact congrArg (Option.map unitCertificate)
    (congrArg Prod.fst (initialRowsVScaled_refines R H a b aT bT m hb hbT))

theorem searchMemoVScaled_correct (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    (searchMemoVScaled R H a b aT bT m).isSome = true ↔
      MatrixFeasible R (decode H) m (fun v => (a[v] : ℚ) / (b[v] : ℚ))
        ((aT : ℚ) / (bT : ℚ)) := by
  rw [searchMemoVScaled_eq R H a b aT bT m hb hbT]
  exact TreeBudgetMemoIntegration.searchMemo_correct ..

theorem searchMemoVScaled_none_iff (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT m : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    searchMemoVScaled R H a b aT bT m = none ↔
      ¬ MatrixFeasible R (decode H) m (fun v => (a[v] : ℚ) / (b[v] : ℚ))
        ((aT : ℚ) / (bT : ℚ)) := by
  rw [searchMemoVScaled_eq R H a b aT bT m hb hbT]
  exact TreeBudgetMemoIntegration.searchMemo_none_iff ..

/-- All three reference invariants are required; validity alone is insufficient. -/
def CacheReadyV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (s : Fin n → ℚ) (T : ℚ) (cs : CacheV n) : Prop :=
  CacheReady R (decode H) s T (decodeCache cs)

theorem memoRowsV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n)
    (hr : ReachableResidual R (decode H) s T k (decode r))
    (cs : CacheV n) (hc : CacheReadyV R H s T cs) :
    CacheReadyV R H s T (memoRowsV R H A AT k r cs).2 := by
  have he := congrArg Prod.snd (memoRowsV_refines R H A AT s T D hD hA hAT k r cs)
  change CacheReady R (decode H) s T _
  change decodeCache (memoRowsV R H A AT k r cs).2 = _ at he
  rw [he]
  exact memoRows_cacheReady R (decode H) s T k (decode r) hr (decodeCache cs) hc

theorem cache_success_entry_boundsV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (s : Fin n → ℚ) (T : ℚ) (cs : CacheV n) (hc : CacheReadyV R H s T cs)
    (k : ℕ) (r : Vector ℕ n) (rows : RowsV n) (hm : ((k, r), some rows) ∈ cs) :
    rows.length = k ∧ k ≤ rootCount R (decode H) ∧
      (∀ p ∈ rows, p[R.root] = 0) ∧ (∀ p ∈ rows, ∀ v : Fin n, p[v] ≤ H[v]) := by
  have hm' : ((k, decode r), some (decodeRows rows)) ∈ decodeCache cs := by
    exact List.mem_map.mpr ⟨((k, r), some rows), hm, rfl⟩
  have h := cache_success_entry_bounds R (decode H) s T (decodeCache cs) hc k
    (decode r) (decodeRows rows) hm'
  refine ⟨?_, h.count_le_initial, ?_, ?_⟩
  · simpa [decodeRows] using h.length_eq
  · intro p hp
    exact h.row_root (decode p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro p hp v
    exact h.row_le (decode p) (List.mem_map.mpr ⟨p, hp, rfl⟩) v

theorem memoRowsStatV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n)
    (hr : ReachableResidual R (decode H) s T k (decode r))
    (cs : CacheV n) (hc : CacheReadyV R H s T cs) :
    CacheReadyV R H s T (memoRowsStatV R H A AT k r cs).1.2 := by
  simpa only [memoRowsStatV, memoStatV_erase, memoRowsV] using
    memoRowsV_cacheReady R H A AT s T D hD hA hAT k r hr cs hc

theorem scanCandidatesV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n)
    (hr : ReachableResidual R (decode H) s T (k + 1) (decode r))
    (tail : List (Vector ℕ n)) (hp : ∀ p ∈ tail, RowValid R (decode H) s T (decode p))
    (cs : CacheV n) (hc : CacheReadyV R H s T cs) :
    CacheReadyV R H s T (scanCandidatesV (memoRowsV R H A AT k) r tail cs).2 := by
  have he := congrArg Prod.snd (scanCandidatesV_refines
    (memoRowsV R H A AT k) (TreeBudgetMemoSearch.memoRows R (decode H) s T k)
    (fun r cs => memoRowsV_refines R H A AT s T D hD hA hAT k r cs) r tail cs)
  change CacheReady R (decode H) s T _
  change decodeCache (scanCandidatesV (memoRowsV R H A AT k) r tail cs).2 = _ at he
  rw [he]
  apply scanCandidates_cacheReady R (decode H) s T k (decode r) hr (tail.map decode)
    _ (decodeCache cs) hc
  intro p hp'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
  exact hp q hq

theorem scanStatV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n)
    (hr : ReachableResidual R (decode H) s T (k + 1) (decode r))
    (tail : List (Vector ℕ n)) (hp : ∀ p ∈ tail, RowValid R (decode H) s T (decode p))
    (cs : CacheV n) (hc : CacheReadyV R H s T cs) :
    CacheReadyV R H s T (scanStatV (memoRowsStatV R H A AT k) r tail cs).1.2 := by
  have he := scanStatV_erase (memoRowsStatV R H A AT k) (memoRowsV R H A AT k)
    (fun r cs => show (memoRowsStatV R H A AT k r cs).1 = memoRowsV R H A AT k r cs
      from memoStatV_erase (candidatesV R H A AT) k r cs) r tail cs
  rw [he]
  exact scanCandidatesV_cacheReady R H A AT s T D hD hA hAT k r hr tail hp cs hc

theorem initialRowsV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    CacheReadyV R (TreeBudgetVector.normalize R H) s T
      (initialRowsV R H A AT (rootCount R (decode (TreeBudgetVector.normalize R H)))).2 := by
  apply memoRowsV_cacheReady R (TreeBudgetVector.normalize R H) A AT s T D hD hA hAT
    _ _ .initial []
  exact cacheReady_empty ..

theorem initialRowsStatV_cacheReady (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    CacheReadyV R (TreeBudgetVector.normalize R H) s T
      (initialRowsStatV R H A AT (rootCount R (decode (TreeBudgetVector.normalize R H)))).1.2 := by
  simpa only [initialRowsStatV, memoRowsStatV, memoStatV_erase, initialRowsV, memoRowsV]
    using initialRowsV_cacheReady R H A AT s T D hD hA hAT

theorem initial_success_entry_boundsV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n) (rows : RowsV n)
    (hm : ((k, r), some rows) ∈
      (initialRowsStatV R H A AT (rootCount R (decode (TreeBudgetVector.normalize R H)))).1.2) :
    rows.length = k ∧ k ≤ rootCount R (decode (TreeBudgetVector.normalize R H)) ∧
      (∀ p ∈ rows, p[R.root] = 0) ∧
      (∀ p ∈ rows, ∀ v : Fin n, p[v] ≤ (TreeBudgetVector.normalize R H)[v]) :=
  cache_success_entry_boundsV R (TreeBudgetVector.normalize R H) s T _
    (initialRowsStatV_cacheReady R H A AT s T D hD hA hAT) k r rows hm

/-- Bounds use the normalized input and include every field of `Counts`. -/
structure EventBoundsV (out : Measured (AnswerV n × CacheV n)) (B : ℕ) : Prop where
  expansions : out.2.expansions ≤ B
  cacheLength : out.1.2.length ≤ B
  candidates : out.2.candidates ≤ B ^ 2
  calls : out.2.calls ≤ 1 + B ^ 2
  hits : out.2.hits ≤ 1 + B ^ 2
  insertionScans : out.2.insertionScans ≤ B * (B - 1) / 2
  lookupComparisons : out.2.lookupComparisons ≤ B + B ^ 3

theorem initial_eventBoundsV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (B : ℕ)
    (hB : stateBound R (TreeBudgetPatterns.normalize R (decode H)) ≤ B) :
    EventBoundsV (initialRowsStatV R H A AT
      (rootCount R (TreeBudgetPatterns.normalize R (decode H)))) B := by
  let H0 := TreeBudgetPatterns.normalize R (decode H)
  have hb := initial_bounds_of_stateBound_le R H0 s T B hB
  have he := initialRowsStatV_refines R H A AT s T D hD hA hAT (rootCount R H0)
  have hcounts : (initialRowsStatV R H A AT (rootCount R H0)).2 =
      (memoRowsStat R H0 s T (rootCount R H0) H0 TreeBudgetMemoState.emptyCache).2 :=
    congrArg Prod.snd he
  have hcache : (initialRowsStatV R H A AT (rootCount R H0)).1.2.length =
      (memoRowsStat R H0 s T (rootCount R H0) H0 TreeBudgetMemoState.emptyCache).1.2.length := by
    have hc := congrArg (fun out => out.1.2.length) he
    simpa only [decodeMeasured, decodeResult, decodeCache_length] using hc
  have hh : (memoRowsStat R H0 s T (rootCount R H0) H0 TreeBudgetMemoState.emptyCache).2.calls =
      (memoRowsStat R H0 s T (rootCount R H0) H0 TreeBudgetMemoState.emptyCache).2.hits +
      (memoRowsStat R H0 s T (rootCount R H0) H0 TreeBudgetMemoState.emptyCache).2.expansions :=
    TreeBudgetSearchStatsBounds.memoStat_calls_eq_hits_add_expansions
      (TreeBudgetFiniteSearch.candidates R H0 s T) (rootCount R H0) H0
      TreeBudgetMemoState.emptyCache
  have hhits : (memoRowsStat R H0 s T (rootCount R H0) H0
      TreeBudgetMemoState.emptyCache).2.hits ≤ 1 + B ^ 2 := by
    have hcalls := hb.calls
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Counts.expansions hcounts).trans_le hb.expansions
  · exact hcache.trans_le hb.cacheLength
  · exact (congrArg Counts.candidates hcounts).trans_le hb.candidates
  · exact (congrArg Counts.calls hcounts).trans_le hb.calls
  · exact (congrArg Counts.hits hcounts).trans_le hhits
  · exact (congrArg Counts.insertionScans hcounts).trans_le hb.insertionScans
  · exact (congrArg Counts.lookupComparisons hcounts).trans_le hb.lookupComparisons

theorem initial_candidates_lengthV (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    (candidatesV R (TreeBudgetVector.normalize R H) A AT).length ≤
      stateBound R (TreeBudgetPatterns.normalize R (decode H)) := by
  have he := congrArg List.length (map_decode_candidatesV R
    (TreeBudgetVector.normalize R H) A AT s T D hD hA hAT)
  simp only [List.length_map, decode_normalize] at he
  rw [he]
  exact TreeBudgetCandidateCount.candidates_length_le_stateBound ..

theorem initial_eventBoundsV_stateBound (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    EventBoundsV (initialRowsStatV R H A AT
      (rootCount R (TreeBudgetPatterns.normalize R (decode H))))
      (stateBound R (TreeBudgetPatterns.normalize R (decode H))) :=
  initial_eventBoundsV R H A AT s T D hD hA hAT _ le_rfl

theorem initial_eventBoundsV_two_pow (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    EventBoundsV (initialRowsStatV R H A AT
      (rootCount R (TreeBudgetPatterns.normalize R (decode H))))
      (2 ^ totalMultiplicity R (TreeBudgetPatterns.normalize R (decode H))) :=
  initial_eventBoundsV R H A AT s T D hD hA hAT _
    (stateBound_le_two_pow_totalMultiplicity R _)

theorem initial_eventBoundsV_support (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    EventBoundsV (initialRowsStatV R H A AT
      (rootCount R (TreeBudgetPatterns.normalize R (decode H))))
      ((maxMultiplicity R (TreeBudgetPatterns.normalize R (decode H)) + 1) ^
        positiveCount R (TreeBudgetPatterns.normalize R (decode H))) :=
  initial_eventBoundsV R H A AT s T D hD hA hAT _
    (stateBound_le_maxMultiplicity_pow_positiveCount R _)

end UAVProof.TreeBudgetVectorMemoIntegration

#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsStatV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsV_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsStatV_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsStatV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsV_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsStatV_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoV_eq
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoV_sound
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoV_correct
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoV_none_iff
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsVScaled
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsStatVScaled
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsVScaled_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsStatVScaled_refines
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoVScaled
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoVScaled_eq
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoVScaled_correct
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.searchMemoVScaled_none_iff
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.CacheReadyV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.cache_success_entry_boundsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.memoRowsStatV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.scanCandidatesV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.scanStatV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initialRowsStatV_cacheReady
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_success_entry_boundsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.EventBoundsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_eventBoundsV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_candidates_lengthV
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_eventBoundsV_stateBound
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_eventBoundsV_two_pow
#print axioms UAVProof.TreeBudgetVectorMemoIntegration.initial_eventBoundsV_support
