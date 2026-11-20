import LeanCompletion.UAV.TreeBudgetFeeTailBudget
import LeanCompletion.UAV.TreeBudgetFeeTailExamples
import LeanCompletion.UAV.TreeBudgetFeeTailFields
import LeanCompletion.UAV.TreeBudgetFeeTailFieldSemantics
import LeanCompletion.UAV.TreeBudgetFeeTailFieldTime
import LeanCompletion.UAV.TreeBudgetFeeTailFlush
import LeanCompletion.UAV.TreeBudgetFeeTailGroups
import LeanCompletion.UAV.TreeBudgetFeeTailLoops
import LeanCompletion.UAV.TreeBudgetFeeTailLoopTime
import LeanCompletion.UAV.TreeBudgetFeeTailSemantics
import LeanCompletion.UAV.TreeBudgetFeeTailSetup
import LeanCompletion.UAV.TreeBudgetFeeTailSpec
import LeanCompletion.UAV.TreeBudgetFeeTailTM2
import LeanCompletion.UAV.TreeBudgetFeeTailTotal
import LeanCompletion.UAV.TreeBudgetInstanceEntry
import LeanCompletion.UAV.TreeBudgetInstanceSpec
import LeanCompletion.UAV.TreeBudgetInstanceTotal

/-! Explicit named declarations in the complete-instance TM2 batch.
Raw audit output remains under ignored verification/runs/. -/

-- TreeBudgetFeeTailBudget
#print axioms UAVProof.A4FeeTailMachine.scalarField
#print axioms UAVProof.A4FeeTailMachine.scalarEntry
#print axioms UAVProof.A4FeeTailMachine.scalarEnd
#print axioms UAVProof.A4FeeTailMachine.fieldStore
#print axioms UAVProof.A4FeeTailMachine.scalar_start
#print axioms UAVProof.A4FeeTailMachine.scalar_flush_input
#print axioms UAVProof.A4FeeTailMachine.scalar_flush_output
#print axioms UAVProof.A4FeeTailMachine.scalar_checked_run
#print axioms UAVProof.A4FeeTailMachine.halted
#print axioms UAVProof.A4FeeTailMachine.bad_run
#print axioms UAVProof.A4FeeTailMachine.eof_run
#print axioms UAVProof.A4FeeTailMachine.budgetParse
#print axioms UAVProof.A4FeeTailMachine.budgetStore
#print axioms UAVProof.A4FeeTailMachine.budgetKept
#print axioms UAVProof.A4FeeTailMachine.budget_run

-- TreeBudgetFeeTailExamples
#print axioms UAVProof.A4FeeTailChecks.f
#print axioms UAVProof.A4FeeTailChecks.xraw
#print axioms UAVProof.A4FeeTailChecks.ctx
#print axioms UAVProof.A4FeeTailChecks.outputs
#print axioms UAVProof.A4FeeTailChecks.snapshot
#print axioms UAVProof.A4FeeTailChecks.saved_outputs
#print axioms UAVProof.A4FeeTailChecks.rejects_zero_denominator
#print axioms UAVProof.A4FeeTailChecks.rejects_trailing
#print axioms UAVProof.A4FeeTailChecks.raw_start_accepts
#print axioms UAVProof.A4FeeTailChecks.raw_start_rejects_trailing
#print axioms UAVProof.A4FeeTailChecks.standard_init_accepts
#print axioms UAVProof.A4FeeTailChecks.raw_start_wrong_routes

-- TreeBudgetFeeTailFields
#print axioms UAVProof.A4FeeTailMachine.Run
#print axioms UAVProof.A4FeeTailMachine.seq
#print axioms UAVProof.A4FeeTailMachine.streamStore
#print axioms UAVProof.A4FeeTailMachine.streamCfg
#print axioms UAVProof.A4FeeTailMachine.stream_src
#print axioms UAVProof.A4FeeTailMachine.stream_rev
#print axioms UAVProof.A4FeeTailMachine.stream_update_src
#print axioms UAVProof.A4FeeTailMachine.stream_update_rev
#print axioms UAVProof.A4FeeTailMachine.wordEnd
#print axioms UAVProof.A4FeeTailMachine.word_run
#print axioms UAVProof.A4FeeTailMachine.wordEnd_framed
#print axioms UAVProof.A4FeeTailMachine.wordEnd_truncated
#print axioms UAVProof.A4FeeTailMachine.wordEnd_kept
#print axioms UAVProof.A4FeeTailMachine.wordEnd_length
#print axioms UAVProof.A4FeeTailMachine.readWord
#print axioms UAVProof.A4FeeTailMachine.wordEnd_read
#print axioms UAVProof.A4FeeTailMachine.readWord_true
#print axioms UAVProof.A4FeeTailMachine.lastDigit_false
#print axioms UAVProof.A4FeeTailMachine.readWord_false
#print axioms UAVProof.A4FeeTailMachine.signedEnd
#print axioms UAVProof.A4FeeTailMachine.signed_run
#print axioms UAVProof.A4FeeTailMachine.readSigned
#print axioms UAVProof.A4FeeTailMachine.signedEnd_read
#print axioms UAVProof.A4FeeTailMachine.signedEnd_kept
#print axioms UAVProof.A4FeeTailMachine.signedEnd_length

-- TreeBudgetFeeTailFieldSemantics
#print axioms UAVProof.A4FeeTailMachine.readSigned_int
#print axioms UAVProof.A4FeeTailMachine.guarded
#print axioms UAVProof.A4FeeTailMachine.parseMany_guarded
#print axioms UAVProof.A4FeeTailMachine.parseMany_signed
#print axioms UAVProof.A4FeeTailMachine.parseMany_positive
#print axioms UAVProof.A4FeeTailMachine.readSigned_some
#print axioms UAVProof.A4FeeTailMachine.readPositive_some
#print axioms UAVProof.A4FeeTailMachine.manySigned_some
#print axioms UAVProof.A4FeeTailMachine.manyPositive_some

-- TreeBudgetFeeTailFieldTime
#print axioms UAVProof.A4FeeTailMachine.word_run_framed
#print axioms UAVProof.A4FeeTailMachine.word_run_success
#print axioms UAVProof.A4FeeTailMachine.signed_run_success

-- TreeBudgetFeeTailFlush
#print axioms UAVProof.A4FeeTailMachine.flushPorts
#print axioms UAVProof.A4FeeTailMachine.flushCfg
#print axioms UAVProof.A4FeeTailMachine.flush_top
#print axioms UAVProof.A4FeeTailMachine.flush_output
#print axioms UAVProof.A4FeeTailMachine.flush_pop
#print axioms UAVProof.A4FeeTailMachine.flush_push
#print axioms UAVProof.A4FeeTailMachine.flush_run

-- TreeBudgetFeeTailGroups
#print axioms UAVProof.A4FeeTailMachine.groupParse
#print axioms UAVProof.A4FeeTailMachine.groupStore
#print axioms UAVProof.A4FeeTailMachine.groupClean
#print axioms UAVProof.A4FeeTailMachine.plainCfg
#print axioms UAVProof.A4FeeTailMachine.groupKept
#print axioms UAVProof.A4FeeTailMachine.group_store_kept
#print axioms UAVProof.A4FeeTailMachine.dimension_input
#print axioms UAVProof.A4FeeTailMachine.dimension_output
#print axioms UAVProof.A4FeeTailMachine.count_input
#print axioms UAVProof.A4FeeTailMachine.count_output
#print axioms UAVProof.A4FeeTailMachine.flush_input
#print axioms UAVProof.A4FeeTailMachine.flush_output_layout
#print axioms UAVProof.A4FeeTailMachine.group_checked_run

-- TreeBudgetFeeTailLoops
#print axioms UAVProof.A4FeeTailMachine.groupField
#print axioms UAVProof.A4FeeTailMachine.groupRead
#print axioms UAVProof.A4FeeTailMachine.groupEnd
#print axioms UAVProof.A4FeeTailMachine.groupEntry
#print axioms UAVProof.A4FeeTailMachine.group_run
#print axioms UAVProof.A4FeeTailMachine.group_read
#print axioms UAVProof.A4FeeTailMachine.group_kept
#print axioms UAVProof.A4FeeTailMachine.group_length
#print axioms UAVProof.A4FeeTailMachine.readWord_consumed
#print axioms UAVProof.A4FeeTailMachine.readSigned_consumed
#print axioms UAVProof.A4FeeTailMachine.group_consumed
#print axioms UAVProof.A4FeeTailMachine.groupMany_consumed
#print axioms UAVProof.A4FeeTailMachine.tickBase
#print axioms UAVProof.A4FeeTailMachine.loopCfg
#print axioms UAVProof.A4FeeTailMachine.loopEnd
#print axioms UAVProof.A4FeeTailMachine.stream_ticks
#print axioms UAVProof.A4FeeTailMachine.update_ticks
#print axioms UAVProof.A4FeeTailMachine.loop_run
#print axioms UAVProof.A4FeeTailMachine.loop_read
#print axioms UAVProof.A4FeeTailMachine.loop_kept

-- TreeBudgetFeeTailLoopTime
#print axioms UAVProof.A4FeeTailMachine.group_run_success
#print axioms UAVProof.A4FeeTailMachine.loop_run_linear

-- TreeBudgetFeeTailSemantics
#print axioms UAVProof.A4FeeTailMachine.group_signed_some
#print axioms UAVProof.A4FeeTailMachine.group_positive_some
#print axioms UAVProof.A4FeeTailMachine.group_signed_append
#print axioms UAVProof.A4FeeTailMachine.group_positive_append
#print axioms UAVProof.A4FeeTailMachine.FeeWords
#print axioms UAVProof.A4FeeTailMachine.wireWords
#print axioms UAVProof.A4FeeTailMachine.readFeeWords
#print axioms UAVProof.A4FeeTailMachine.budget_some
#print axioms UAVProof.A4FeeTailMachine.budget_append
#print axioms UAVProof.A4FeeTailMachine.readFeeWords_some
#print axioms UAVProof.A4FeeTailMachine.readFeeWords_wire
#print axioms UAVProof.A4FeeTailMachine.readFeeWords_eq

-- TreeBudgetFeeTailSetup
#print axioms UAVProof.A4FeeTailMachine.headerPorts
#print axioms UAVProof.A4FeeTailMachine.headerCfg
#print axioms UAVProof.A4FeeTailMachine.header_src
#print axioms UAVProof.A4FeeTailMachine.header_expected
#print axioms UAVProof.A4FeeTailMachine.header_update_src
#print axioms UAVProof.A4FeeTailMachine.header_update_expected
#print axioms UAVProof.A4FeeTailMachine.stripHeader
#print axioms UAVProof.A4FeeTailMachine.stripHeader_iff
#print axioms UAVProof.A4FeeTailMachine.headerEnd
#print axioms UAVProof.A4FeeTailMachine.header_run
#print axioms UAVProof.A4FeeTailMachine.header_success
#print axioms UAVProof.A4FeeTailMachine.header_failure
#print axioms UAVProof.A4FeeTailMachine.header_preserved
#print axioms UAVProof.A4FeeTailMachine.dimension_run
#print axioms UAVProof.A4FeeTailMachine.parent_count_run

-- TreeBudgetFeeTailSpec
#print axioms UAVProof.A4FeeTailSpec.Fields
#print axioms UAVProof.A4FeeTailSpec.wire
#print axioms UAVProof.A4FeeTailSpec.good
#print axioms UAVProof.A4FeeTailSpec.readPrefix
#print axioms UAVProof.A4FeeTailSpec.read
#print axioms UAVProof.A4FeeTailSpec.prefix_append
#print axioms UAVProof.A4FeeTailSpec.prefix_canonical
#print axioms UAVProof.A4FeeTailSpec.read_iff
#print axioms UAVProof.A4FeeTailSpec.good_iff
#print axioms UAVProof.A4FeeTailSpec.rebuild
#print axioms UAVProof.A4FeeTailSpec.rebuild_wire
#print axioms UAVProof.A4FeeTailSpec.parseInstance_finish

-- TreeBudgetFeeTailTM2
#print axioms UAVProof.A4FeeTailMachine.FeeField
#print axioms UAVProof.A4FeeTailMachine.Aux
#print axioms UAVProof.A4FeeTailMachine.K
#print axioms UAVProof.A4FeeTailMachine.L
#print axioms UAVProof.A4FeeTailMachine.Cfg
#print axioms UAVProof.A4FeeTailMachine.Stmt
#print axioms UAVProof.A4FeeTailMachine.src
#print axioms UAVProof.A4FeeTailMachine.dimension
#print axioms UAVProof.A4FeeTailMachine.parents
#print axioms UAVProof.A4FeeTailMachine.context
#print axioms UAVProof.A4FeeTailMachine.prefixW
#print axioms UAVProof.A4FeeTailMachine.dimPorts
#print axioms UAVProof.A4FeeTailMachine.countPorts
#print axioms UAVProof.A4FeeTailMachine.go
#print axioms UAVProof.A4FeeTailMachine.doneField
#print axioms UAVProof.A4FeeTailMachine.nextGroup
#print axioms UAVProof.A4FeeTailMachine.readBit
#print axioms UAVProof.A4FeeTailMachine.program
#print axioms UAVProof.A4FeeTailMachine.machine
#print axioms UAVProof.A4FeeTailMachine.start
#print axioms UAVProof.A4FeeTailMachine.prepared
#print axioms UAVProof.A4FeeTailMachine.observe
#print axioms UAVProof.A4FeeTailMachine.finite_alphabet
#print axioms UAVProof.A4FeeTailMachine.finite_control

-- TreeBudgetFeeTailTotal
#print axioms UAVProof.A4FeeTailMachine.feeStore
#print axioms UAVProof.A4FeeTailMachine.feeKept
#print axioms UAVProof.A4FeeTailMachine.groupParse_consumed
#print axioms UAVProof.A4FeeTailMachine.groupKept_prefix
#print axioms UAVProof.A4FeeTailMachine.budgetKept_prefix
#print axioms UAVProof.A4FeeTailMachine.groupStore_prefix
#print axioms UAVProof.A4FeeTailMachine.fee_words_run
#print axioms UAVProof.A4FeeTailMachine.fee_tail_run

-- TreeBudgetInstanceEntry
#print axioms UAVProof.A4FeeTailMachine.root_bank
#print axioms UAVProof.A4FeeTailMachine.afterRoot
#print axioms UAVProof.A4FeeTailMachine.prefix_true_step
#print axioms UAVProof.A4FeeTailMachine.prefix_false_step
#print axioms UAVProof.A4FeeTailMachine.init_eq

-- TreeBudgetInstanceSpec
#print axioms UAVProof.A4FeeTailSpec.accepted
#print axioms UAVProof.A4FeeTailSpec.read_wire
#print axioms UAVProof.A4FeeTailSpec.decodeRaw_some
#print axioms UAVProof.A4FeeTailSpec.decoded_rootSum
#print axioms UAVProof.A4FeeTailSpec.decodeSpecified_some
#print axioms UAVProof.A4FeeTailSpec.rawFields
#print axioms UAVProof.A4FeeTailSpec.accepted_encode
#print axioms UAVProof.A4FeeTailSpec.root_parse_of_accept
#print axioms UAVProof.A4FeeTailSpec.accepted_eq_parseInstance
#print axioms UAVProof.A4FeeTailSpec.root_contract
#print axioms UAVProof.A4FeeTailSpec.fee_input_bounds

-- TreeBudgetInstanceTotal
#print axioms UAVProof.A4FeeTailMachine.InstanceFields
#print axioms UAVProof.A4FeeTailMachine.SavedInstance
#print axioms UAVProof.A4FeeTailMachine.instance_polynomial
#print axioms UAVProof.A4FeeTailMachine.instance_from_init
