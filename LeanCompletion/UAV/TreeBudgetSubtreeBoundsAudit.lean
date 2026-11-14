import LeanCompletion.UAV.TreeBudgetSubtreeBoundsSeed
import LeanCompletion.UAV.TreeBudgetSubtreeInvariants
import LeanCompletion.UAV.TreeBudgetSubtreeCompositionBounds
import LeanCompletion.UAV.TreeBudgetSubtreeGridBounds
import LeanCompletion.UAV.TreeBudgetSubtreeTableBounds
import LeanCompletion.UAV.TreeBudgetSubtreeCandidateBounds
import LeanCompletion.UAV.TreeBudgetSubtreeSupportBounds
import LeanCompletion.UAV.TreeBudgetSubtreeStatsBounds
import LeanCompletion.UAV.TreeBudgetSubtreeStatsGlobalBounds
import LeanCompletion.UAV.TreeBudgetSubtreeCountsExact
import LeanCompletion.UAV.TreeBudgetSubtreeMassBounds
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerDP
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerTrace
import LeanCompletion.UAV.TreeBudgetSubtreeWitnessDP
import LeanCompletion.UAV.TreeBudgetSubtreeBoundsExamples
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerBench

/-! Reproducible axiom audit of all explicitly named declarations in the
subtree bounds, integer refinement, witness and regression modules.
The output belongs in ignored verification/runs/, never in version control. -/

#check @UAVProof.TreeBudgetSubtreeStats.checkCompactStats_bounds
#check @UAVProof.TreeBudgetSubtreeStats.checkCompactStats_eqCalls_le
#check @UAVProof.TreeBudgetSubtreeStats.checkCompactStats_logicalWork_le


-- TreeBudgetSubtreeBoundsSeed.lean
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.subtreeTotal
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_sum
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_zero_of_not_active
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_eq_of_le
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_eq_of_succ_eq
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.executable_cost_sum
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.insideCosts_length_le
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.rootFold_length_le

-- TreeBudgetSubtreeInvariants.lean
#print axioms UAVProof.TreeBudgetSubtreeState.subtreeTotal
#print axioms UAVProof.TreeBudgetSubtreeState.compact_cost_sum
#print axioms UAVProof.TreeBudgetSubtreeState.compact_cost_zero_of_not_active
#print axioms UAVProof.TreeBudgetSubtreeState.compact_cost_eq_of_le
#print axioms UAVProof.TreeBudgetSubtreeState.compact_cost_eq_of_succ_eq
#print axioms UAVProof.TreeBudgetSubtreeState.compact_cost_recover
#print axioms UAVProof.TreeBudgetSubtreeState.compact_active_card_le
#print axioms UAVProof.TreeBudgetSubtreeState.compact_active_card_root_child
#print axioms UAVProof.TreeBudgetSubtreeState.compact_zero_top_demands
#print axioms UAVProof.TreeBudgetSubtreeState.compact_zero_routes_demands
#print axioms UAVProof.TreeBudgetSubtreeState.compact_zero_rep
#print axioms UAVProof.TreeBudgetSubtreeState.compact_zero_top_iff
#print axioms UAVProof.TreeBudgetSubtreeState.compact_zero_routes_iff
#print axioms UAVProof.TreeBudgetSubtreeExecutable.executable_cost_sum

-- TreeBudgetSubtreeCompositionBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnCount
#print axioms UAVProof.TreeBudgetSubtreeExecutable.consV_injective
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compositionsV_nodup
#print axioms UAVProof.TreeBudgetSubtreeExecutable.sum_range_reverse
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compositionsV_length
#print axioms UAVProof.TreeBudgetSubtreeStats.sumStats_compositionCalls
#print axioms UAVProof.TreeBudgetSubtreeStats.sumStats_rangeChoices
#print axioms UAVProof.TreeBudgetSubtreeStats.compositionProfile_calls
#print axioms UAVProof.TreeBudgetSubtreeStats.compositionProfile_choices
#print axioms UAVProof.TreeBudgetSubtreeStats.compositionProfile_calls_le

-- TreeBudgetSubtreeGridBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeState.GridScale
#print axioms UAVProof.TreeBudgetSubtreeState.gridLower
#print axioms UAVProof.TreeBudgetSubtreeState.gridUpper
#print axioms UAVProof.TreeBudgetSubtreeState.signed_entry_bounds
#print axioms UAVProof.TreeBudgetSubtreeState.grid_width
#print axioms UAVProof.TreeBudgetSubtreeState.compact_integer_grid
#print axioms UAVProof.TreeBudgetSubtreeState.remaining_lower_bound
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_finset_card_grid
#print axioms UAVProof.TreeBudgetSubtreeExecutable.computeCompact_length_le_grid

-- TreeBudgetSubtreeTableBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeExecutable.tableProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.insideCosts_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.insideRaw_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.rootFold_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.rootRaw_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.nodeRaw
#print axioms UAVProof.TreeBudgetSubtreeExecutable.length_flatMap_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.nodeRaw_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.nodeTable_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnFactor
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.globalProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.prod_subtree
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnProduct_split
#print axioms UAVProof.TreeBudgetSubtreeExecutable.localCandidates_length_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.tableProduct_children_le
#print axioms UAVProof.TreeBudgetSubtreeExecutable.computeCompact_length_le_columnProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnProduct_le_globalProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.nodeRaw_length_le_columnProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.root_children_product
#print axioms UAVProof.TreeBudgetSubtreeExecutable.rootFold_length_le_globalProduct
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnProduct_pos
#print axioms UAVProof.TreeBudgetSubtreeExecutable.globalProduct_pos

-- TreeBudgetSubtreeCandidateBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeExecutable.localCandidates_root_child_length
#print axioms UAVProof.TreeBudgetSubtreeExecutable.localCandidates_root_child_empty
#print axioms UAVProof.TreeBudgetSubtreeExecutable.computeCompact_root_child_empty

-- TreeBudgetSubtreeSupportBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_finset_card_fixed_support
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_active_nonempty
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_finset_card_supports
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_finset_card_support_size
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compact_finset_card_stratified
#print axioms UAVProof.TreeBudgetSubtreeExecutable.root_child_finset_card_grid
#print axioms UAVProof.TreeBudgetSubtreeExecutable.computeCompact_length_le_stratified

-- TreeBudgetSubtreeStatsBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeStats.logicalWork
#print axioms UAVProof.TreeBudgetSubtreeStats.Covers
#print axioms UAVProof.TreeBudgetSubtreeStats.covers_add
#print axioms UAVProof.TreeBudgetSubtreeStats.covers_mono
#print axioms UAVProof.TreeBudgetSubtreeStats.dedupEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.dedupProfile_bounds
#print axioms UAVProof.TreeBudgetSubtreeStats.safeProduct
#print axioms UAVProof.TreeBudgetSubtreeStats.safeProduct_pos
#print axioms UAVProof.TreeBudgetSubtreeStats.tableProduct_le_safeProduct
#print axioms UAVProof.TreeBudgetSubtreeStats.insideEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.insideProfile_bounds
#print axioms UAVProof.TreeBudgetSubtreeStats.rootEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.rootProfile_bounds

-- TreeBudgetSubtreeStatsGlobalBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeStats.scaleEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.covers_sum
#print axioms UAVProof.TreeBudgetSubtreeStats.sumStats_compositions_only
#print axioms UAVProof.TreeBudgetSubtreeStats.compositionProfile_only
#print axioms UAVProof.TreeBudgetSubtreeStats.compositionProfile_covers
#print axioms UAVProof.TreeBudgetSubtreeStats.nodeEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.nodeProfile_bounds
#print axioms UAVProof.TreeBudgetSubtreeStats.forestEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.forestEnvelope_add
#print axioms UAVProof.TreeBudgetSubtreeStats.covers_forest_sum
#print axioms UAVProof.TreeBudgetSubtreeStats.subtreeSize
#print axioms UAVProof.TreeBudgetSubtreeStats.subtreeSize_pos
#print axioms UAVProof.TreeBudgetSubtreeStats.subtreeSize_split
#print axioms UAVProof.TreeBudgetSubtreeStats.sum_pred_sizes
#print axioms UAVProof.TreeBudgetSubtreeStats.safeProduct_children_le
#print axioms UAVProof.TreeBudgetSubtreeStats.computeProfile_bounds
#print axioms UAVProof.TreeBudgetSubtreeStats.globalEnvelope
#print axioms UAVProof.TreeBudgetSubtreeStats.acceptComparisons_le
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_covers
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_bounds
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_eqCalls_le
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_logicalWork_le
#print axioms UAVProof.TreeBudgetSubtreeStats.nodeProfile_nodeCalls
#print axioms UAVProof.TreeBudgetSubtreeStats.sumStats_nodeCalls
#print axioms UAVProof.TreeBudgetSubtreeStats.computeProfile_nodeCalls
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_nodeCalls

-- TreeBudgetSubtreeCountsExact.lean
#print axioms UAVProof.TreeBudgetSubtreeStats.insideProfile_candidates
#print axioms UAVProof.TreeBudgetSubtreeStats.rootProfile_candidates
#print axioms UAVProof.TreeBudgetSubtreeStats.nodeProfile_candidates
#print axioms UAVProof.TreeBudgetSubtreeStats.computeProfile_candidates
#print axioms UAVProof.TreeBudgetSubtreeStats.root_children_sum
#print axioms UAVProof.TreeBudgetSubtreeStats.checkCompactStats_candidates

-- TreeBudgetSubtreeMassBounds.lean
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnCount_le_pow
#print axioms UAVProof.TreeBudgetSubtreeExecutable.columnFactor_le_pow
#print axioms UAVProof.TreeBudgetSubtreeExecutable.totalMass
#print axioms UAVProof.TreeBudgetSubtreeExecutable.globalProduct_le_mass
#print axioms UAVProof.TreeBudgetSubtreeExecutable.compatible_routes_le_mass
#print axioms UAVProof.TreeBudgetSubtreeExecutable.canonical_logicalWork_le

-- TreeBudgetSubtreeIntegerDP.lean
#print axioms UAVProof.TreeBudgetSubtreeInteger.IntState
#print axioms UAVProof.TreeBudgetSubtreeInteger.IntRoot
#print axioms UAVProof.TreeBudgetSubtreeInteger.add
#print axioms UAVProof.TreeBudgetSubtreeInteger.inside
#print axioms UAVProof.TreeBudgetSubtreeInteger.node
#print axioms UAVProof.TreeBudgetSubtreeInteger.compute
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootZero
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootAdd
#print axioms UAVProof.TreeBudgetSubtreeInteger.cap
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootFold
#print axioms UAVProof.TreeBudgetSubtreeInteger.accept
#print axioms UAVProof.TreeBudgetSubtreeInteger.check
#print axioms UAVProof.TreeBudgetSubtreeInteger.floorBudget
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftCost
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftState
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftRoot
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftCost_injective
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftState_injective
#print axioms UAVProof.TreeBudgetSubtreeInteger.liftRoot_injective
#print axioms UAVProof.TreeBudgetSubtreeInteger.lift_add
#print axioms UAVProof.TreeBudgetSubtreeInteger.lift_initial
#print axioms UAVProof.TreeBudgetSubtreeInteger.lift_budget
#print axioms UAVProof.TreeBudgetSubtreeInteger.inside_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.lift_rootZero
#print axioms UAVProof.TreeBudgetSubtreeInteger.lift_rootAdd
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootFold_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.node_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.compute_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.accept_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.check_eq

-- TreeBudgetSubtreeIntegerStats.lean
#print axioms UAVProof.TreeBudgetSubtreeInteger.scanComparisons_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupComparisons_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupProfile_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.insideMeasured
#print axioms UAVProof.TreeBudgetSubtreeInteger.insideMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.insideMeasured_count
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootMeasured
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootMeasured_count
#print axioms UAVProof.TreeBudgetSubtreeInteger.nodeMeasured
#print axioms UAVProof.TreeBudgetSubtreeInteger.nodeMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.nodeMeasured_count
#print axioms UAVProof.TreeBudgetSubtreeInteger.computeMeasured
#print axioms UAVProof.TreeBudgetSubtreeInteger.computeMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.computeMeasured_count
#print axioms UAVProof.TreeBudgetSubtreeInteger.checkMeasured
#print axioms UAVProof.TreeBudgetSubtreeInteger.checkMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.anyCounted_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.checkMeasured_count

-- TreeBudgetSubtreeIntegerTrace.lean
#print axioms UAVProof.TreeBudgetSubtreeInteger.scanTrace
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace
#print axioms UAVProof.TreeBudgetSubtreeInteger.scanTrace_length
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace_length
#print axioms UAVProof.TreeBudgetSubtreeInteger.scanTrace_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace_map
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace_liftCost
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace_liftState
#print axioms UAVProof.TreeBudgetSubtreeInteger.dedupTrace_liftRoot

-- TreeBudgetSubtreeWitnessDP.lean
#print axioms UAVProof.TreeBudgetSubtreeWitness.dedupKey
#print axioms UAVProof.TreeBudgetSubtreeWitness.dedupKey_map
#print axioms UAVProof.TreeBudgetSubtreeWitness.mem_of_mem_dedupKey
#print axioms UAVProof.TreeBudgetSubtreeWitness.Matrix
#print axioms UAVProof.TreeBudgetSubtreeWitness.matrixVal
#print axioms UAVProof.TreeBudgetSubtreeWitness.Entry
#print axioms UAVProof.TreeBudgetSubtreeWitness.Inside
#print axioms UAVProof.TreeBudgetSubtreeWitness.inside
#print axioms UAVProof.TreeBudgetSubtreeWitness.inside_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.inside_spec
#print axioms UAVProof.TreeBudgetSubtreeWitness.glue
#print axioms UAVProof.TreeBudgetSubtreeWitness.glue_eq
#print axioms UAVProof.TreeBudgetSubtreeWitness.node
#print axioms UAVProof.TreeBudgetSubtreeWitness.node_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.compute
#print axioms UAVProof.TreeBudgetSubtreeWitness.compute_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.Realizes
#print axioms UAVProof.TreeBudgetSubtreeWitness.node_realizes
#print axioms UAVProof.TreeBudgetSubtreeWitness.compute_realizes
#print axioms UAVProof.TreeBudgetSubtreeWitness.Root
#print axioms UAVProof.TreeBudgetSubtreeWitness.roots
#print axioms UAVProof.TreeBudgetSubtreeWitness.roots_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.roots_spec
#print axioms UAVProof.TreeBudgetSubtreeWitness.certificate
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve
#print axioms UAVProof.TreeBudgetSubtreeWitness.certificate_sound
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve_isSome
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve_sound
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve_none_iff
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve_size
#print axioms UAVProof.TreeBudgetSubtreeWitness.solve_exact_iff

-- TreeBudgetSubtreeBoundsExamples.lean
#print axioms UAVProof.TreeBudgetSubtreeBoundsExamples.checkCase
#print axioms UAVProof.TreeBudgetSubtreeBoundsExamples.runCases

-- TreeBudgetSubtreeIntegerBench.lean
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.Prepared
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.prepare
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.selected
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.runArm
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.validate
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.timedBatch
#print axioms UAVProof.TreeBudgetSubtreeIntegerBench.main
