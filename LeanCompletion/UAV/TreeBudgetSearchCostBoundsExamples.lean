import LeanCompletion.UAV.TreeBudgetSearchCostBounds
import LeanCompletion.UAV.TreeBudgetSearchStatsBoundsExamples

/-! Kernel-checked boundary cases for bounded-list lengths and association-list
comparisons. Existing measured runs are reused; raw cache answers need not be
semantically valid. Comparisons count visited entries, not key-comparison internals. -/
namespace UAVProof.TreeBudgetSearchCostBoundsExamples
open TreeBudgetFiniteSearch TreeBudgetMemoState TreeBudgetSearchStats
open TreeBudgetSearchStatsBoundsExamples

/-- The empty coordinate set has one vector, matching an empty product of one. -/
theorem empty_dimension_has_one_vector :
    (boundedVectors 0 Fin.elim0).length = 1 := by
  decide +kernel

/-- A zero bound contributes one choice, while other coordinates vary independently. -/
theorem nonuniform_bounds_count :
    (boundedVectors 2 ![1, 2]).length = 6 ∧
      (boundedVectors 2 ![0, 2]).length = 3 := by
  decide +kernel

theorem empty_lookup_has_no_comparisons :
    lookupStat (emptyCache : Cache 1) (0, zeroRow) = (none, 0) := by
  decide +kernel

/-- A miss visits both duplicate entries, and a measured zero-step miss records both. -/
theorem duplicate_cache_miss_scans_all :
    lookupStat duplicateOld (0, zeroRow) = (none, 2) ∧
      (memoStat [] 0 zeroRow duplicateOld).2.lookupComparisons = 2 := by
  decide +kernel

/-- Cached failure is a hit at the first entry; conflicting later copies are not read. -/
theorem cached_failure_stops_at_first_match :
    lookupStat duplicateCurrent (2, oneRow) = (some none, 1) ∧
      cachedFailure.2.lookupComparisons = 1 ∧
      cachedFailure.2.lookupComparisons < duplicateCurrent.length := by
  decide +kernel

def lateHitCache : Cache 1 :=
  [((7, zeroRow), none), ((0, zeroRow), some [])]

def lateHit := memoStat [] 0 zeroRow lateHitCache

/-- A late warm hit has no expansion, but attains L = C*K0. The initial-cache
term in the general bound cannot be replaced by the cold-cache expression C*E. -/
theorem late_warm_hit_attains_initial_cache_bound :
    lateHit.2.lookupComparisons = 2 ∧ lateHit.2.calls = 1 ∧
      lateHit.2.expansions = 0 ∧
      lateHit.2.lookupComparisons =
        lateHit.2.calls * (lateHitCache.length + lateHit.2.expansions) ∧
      lateHit.2.calls * lateHit.2.expansions < lateHit.2.lookupComparisons := by
  decide +kernel

/-- Both runs inspect one learned entry: one hits it, the other misses and grows
the cache before succeeding. A visited entry is charged in either case. -/
theorem learned_hit_and_backtrack_comparisons :
    repeatedZero.2.lookupComparisons = 1 ∧ repeatedZero.2.hits = 1 ∧
      backtrack.2.lookupComparisons = 1 ∧ backtrack.2.hits = 0 := by
  decide +kernel

end UAVProof.TreeBudgetSearchCostBoundsExamples

#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.empty_dimension_has_one_vector
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.nonuniform_bounds_count
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.empty_lookup_has_no_comparisons
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.duplicate_cache_miss_scans_all
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.cached_failure_stops_at_first_match
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.late_warm_hit_attains_initial_cache_bound
#print axioms UAVProof.TreeBudgetSearchCostBoundsExamples.learned_hit_and_backtrack_comparisons
