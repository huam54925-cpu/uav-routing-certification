import LeanCompletion.UAV.TreeBudgetStoredSearchExamples
import LeanCompletion.UAV.TreeBudgetStoredExecutionExamples
import LeanCompletion.UAV.TreeBudgetStoredInputBounds
import LeanCompletion.UAV.TreeBudgetStoredPrimitiveBounds
import LeanCompletion.UAV.TreeBudgetStoredRejectionBounds
import LeanCompletion.UAV.TreeBudgetStoredTotalWork

/-! Public audit entry for A--E: full refinement, allocation-derived capacity,
actual total work, rejected inputs and parameterized bounds for every bitstring. -/

#print axioms UAVProof.TreeBudgetSharedAnswerStore.rowsRep_persist
#print axioms UAVProof.TreeBudgetSharedAnswerStore.answerRep_persist
#print axioms UAVProof.TreeBudgetSharedAnswerStore.failure_ne_success
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prependRows_correct
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prependRows_shares
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prependRows_wellFormed
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prependRowsD_value
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prependRowsD_allocations
#print axioms UAVProof.TreeBudgetSharedAnswerStore.prepend_success_size
#print axioms UAVProof.TreeBudgetChargedCache.load_value
#print axioms UAVProof.TreeBudgetChargedCache.alloc_value
#print axioms UAVProof.TreeBudgetChargedCache.lengthRead_value
#print axioms UAVProof.TreeBudgetChargedCache.blobRead_correct
#print axioms UAVProof.TreeBudgetChargedCache.keyRead_correct
#print axioms UAVProof.TreeBudgetChargedCache.lookupD_correct
#print axioms UAVProof.TreeBudgetChargedCache.filterD_correct
#print axioms UAVProof.TreeBudgetChargedCache.insertD_correct
#print axioms UAVProof.TreeBudgetStoredSearch.vectorRead_correct
#print axioms UAVProof.TreeBudgetStoredSearch.frameRead_correct
#print axioms UAVProof.TreeBudgetStoredSearch.framesRep_persist
#print axioms UAVProof.TreeBudgetStoredSearch.allocate_scan_frame
#print axioms UAVProof.TreeBudgetStoredSearch.allocate_memo_frame
#print axioms UAVProof.TreeBudgetStoredSearch.scanD_correct
#print axioms UAVProof.TreeBudgetStoredSearch.memoD_correct
#print axioms UAVProof.TreeBudgetStoredSearch.memoD_refines_cost
#print axioms UAVProof.TreeBudgetStoredSearch.memoD_preserves
#print axioms UAVProof.TreeBudgetStoredPreparation.rowsWrite_correct
#print axioms UAVProof.TreeBudgetStoredPreparation.initializeStore_correct
#print axioms UAVProof.TreeBudgetStoredPreparation.prepareInput_search
#print axioms UAVProof.TreeBudgetStoredOutput.rowsRead_correct
#print axioms UAVProof.TreeBudgetStoredOutput.emitStored_correct
#print axioms UAVProof.TreeBudgetStoredOutput.emitStored_roundtrip
#print axioms UAVProof.TreeBudgetStoredOutput.observeCache_correct
#print axioms UAVProof.TreeBudgetStoredExecution.executeInput_correct
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_refines
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_no_storage_error
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_rejected
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_accepted
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_output_correct
#print axioms UAVProof.TreeBudgetStoredExecution.executeStored_success_sound
#print axioms UAVProof.TreeBudgetStoredCursor.cursorStep_succ
#print axioms UAVProof.TreeBudgetStoredCursor.cursorStep_steps
#print axioms UAVProof.TreeBudgetStoredCursor.cursorStep_allocations
#print axioms UAVProof.TreeBudgetStoredCursor.cursorStep_allocations_le_steps
#print axioms UAVProof.TreeBudgetStoredAllocation.alloc_size
#print axioms UAVProof.TreeBudgetStoredAllocation.alloc_heap_le_allocations
#print axioms UAVProof.TreeBudgetStoredAllocation.vectorWrite_size
#print axioms UAVProof.TreeBudgetStoredAllocation.keyWrite_size
#print axioms UAVProof.TreeBudgetStoredAllocation.rowsWrite_size
#print axioms UAVProof.TreeBudgetStoredAllocation.initializeStore_size
#print axioms UAVProof.TreeBudgetStoredAllocation.insert_heap_growth
#print axioms UAVProof.TreeBudgetStoredAllocation.prefix_capacity
#print axioms UAVProof.TreeBudgetStoredAllocation.prefix_address_width
#print axioms UAVProof.TreeBudgetStoredAllocation.allocation_endpoint_width
#print axioms UAVProof.TreeBudgetStoredHeapGrowth.scanD_growth
#print axioms UAVProof.TreeBudgetStoredHeapGrowth.memoD_growth
#print axioms UAVProof.TreeBudgetStoredInputBounds.prepared_events
#print axioms UAVProof.TreeBudgetStoredInputBounds.executeInput_heap_bound
#print axioms UAVProof.TreeBudgetStoredInputBounds.executeStored_heap_bound
#print axioms UAVProof.TreeBudgetStoredInputBounds.executeStored_address_width
#print axioms UAVProof.TreeBudgetStoredInputBounds.executeStored_heap_mass
#print axioms UAVProof.TreeBudgetStoredInputBounds.executeStored_heap_support_maximum
#print axioms UAVProof.TreeBudgetStoredPrimitiveBounds.load_steps
#print axioms UAVProof.TreeBudgetStoredPrimitiveBounds.load_allocations
#print axioms UAVProof.TreeBudgetStoredPrimitiveBounds.alloc_steps
#print axioms UAVProof.TreeBudgetStoredPrimitiveBounds.alloc_allocations_le_steps
#print axioms UAVProof.TreeBudgetStoredRejectionBounds.executeStored_rejection_work
#print axioms UAVProof.TreeBudgetStoredCacheWork.lookupD_work
#print axioms UAVProof.TreeBudgetStoredCacheWork.filterD_work
#print axioms UAVProof.TreeBudgetStoredCacheWork.insertD_work
#print axioms UAVProof.TreeBudgetStoredSearchWork.scanD_work
#print axioms UAVProof.TreeBudgetStoredMemoWork.memoLayer_work
#print axioms UAVProof.TreeBudgetStoredMemoWork.memoD_work
#print axioms UAVProof.TreeBudgetStoredPreparationWork.rowsWrite_work
#print axioms UAVProof.TreeBudgetStoredPreparationWork.initializeStore_work
#print axioms UAVProof.TreeBudgetStoredPreparationWork.prepareInput_work
#print axioms UAVProof.TreeBudgetStoredOutputWork.rowsRead_work
#print axioms UAVProof.TreeBudgetStoredOutputWork.emitStored_work
#print axioms UAVProof.TreeBudgetStoredCapacityWork.input_payload
#print axioms UAVProof.TreeBudgetStoredCapacityWork.input_envelope
#print axioms UAVProof.TreeBudgetStoredCapacityWork.input_width_bound
#print axioms UAVProof.TreeBudgetStoredCapacityWork.input_rate_bound
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeInput_work
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_work
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_time_and_allocations
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_work_mass
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_work_support_maximum
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_fpt_mass
#print axioms UAVProof.TreeBudgetStoredTotalWork.executeStored_fpt_support_maximum
