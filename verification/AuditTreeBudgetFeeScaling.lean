import LeanCompletion.UAV.TreeBudgetFeeScalingTotal
import LeanCompletion.UAV.TreeBudgetFeeScalingExamples

/-! All explicit declarations of this batch, including physical bounded-run definitions. -/

-- TreeBudgetWeightedWidth.lean
#print axioms UAVProof.TreeBudgetWeightedTM2.weighted_length
#print axioms UAVProof.TreeBudgetWeightedTM2.product_length

-- TreeBudgetSignedWordTM2.lean
#print axioms UAVProof.TreeBudgetSignedWordTM2.signed
#print axioms UAVProof.TreeBudgetSignedWordTM2.signed_mul
#print axioms UAVProof.TreeBudgetSignedWordTM2.signed_zero
#print axioms UAVProof.TreeBudgetSignedWordTM2.signed_encoding
#print axioms UAVProof.TreeBudgetSignedWordTM2.value_append_zero
#print axioms UAVProof.TreeBudgetSignedWordTM2.last_true
#print axioms UAVProof.TreeBudgetSignedWordTM2.high_true_encoding
#print axioms UAVProof.TreeBudgetSignedWordTM2.Phase
#print axioms UAVProof.TreeBudgetSignedWordTM2.jump
#print axioms UAVProof.TreeBudgetSignedWordTM2.code
#print axioms UAVProof.TreeBudgetSignedWordTM2.reverse_run
#print axioms UAVProof.TreeBudgetSignedWordTM2.emit_run
#print axioms UAVProof.TreeBudgetSignedWordTM2.trim_run
#print axioms UAVProof.TreeBudgetSignedWordTM2.write_run

-- TreeBudgetRegisterTM2.lean
#print axioms UAVProof.TreeBudgetRegisterTM2.Instr
#print axioms UAVProof.TreeBudgetRegisterTM2.Label
#print axioms UAVProof.TreeBudgetRegisterTM2.reject
#print axioms UAVProof.TreeBudgetRegisterTM2.program
#print axioms UAVProof.TreeBudgetRegisterTM2.Cfg
#print axioms UAVProof.TreeBudgetRegisterTM2.cfg
#print axioms UAVProof.TreeBudgetRegisterTM2.stopped
#print axioms UAVProof.TreeBudgetRegisterTM2.Run
#print axioms UAVProof.TreeBudgetRegisterTM2.seq

-- TreeBudgetRegisterRuns.lean
#print axioms UAVProof.TreeBudgetRegisterTM2.tapes_update
#print axioms UAVProof.TreeBudgetRegisterTM2.tapes_self
#print axioms UAVProof.TreeBudgetRegisterTM2.copy_run
#print axioms UAVProof.TreeBudgetRegisterTM2.clear_run
#print axioms UAVProof.TreeBudgetRegisterTM2.read_run
#print axioms UAVProof.TreeBudgetRegisterTM2.emit_run
#print axioms UAVProof.TreeBudgetRegisterTM2.mul_run
#print axioms UAVProof.TreeBudgetRegisterTM2.bit_run
#print axioms UAVProof.TreeBudgetRegisterTM2.push_run
#print axioms UAVProof.TreeBudgetRegisterTM2.test_run
#print axioms UAVProof.TreeBudgetRegisterTM2.halt_run

-- TreeBudgetFeeScalingSpec.lean
#print axioms UAVProof.A4FeeScaling.Row
#print axioms UAVProof.A4FeeScaling.mulWord
#print axioms UAVProof.A4FeeScaling.mulWord_value
#print axioms UAVProof.A4FeeScaling.mulWord_length
#print axioms UAVProof.A4FeeScaling.Item
#print axioms UAVProof.A4FeeScaling.prefixEnd
#print axioms UAVProof.A4FeeScaling.history
#print axioms UAVProof.A4FeeScaling.denProd
#print axioms UAVProof.A4FeeScaling.denWidth
#print axioms UAVProof.A4FeeScaling.mass
#print axioms UAVProof.A4FeeScaling.historyWidth
#print axioms UAVProof.A4FeeScaling.denWidth_le_mass
#print axioms UAVProof.A4FeeScaling.prefixEnd_value
#print axioms UAVProof.A4FeeScaling.prefixEnd_length
#print axioms UAVProof.A4FeeScaling.history_width
#print axioms UAVProof.A4FeeScaling.Fits
#print axioms UAVProof.A4FeeScaling.fits_append
#print axioms UAVProof.A4FeeScaling.fits_mono
#print axioms UAVProof.A4FeeScaling.history_fits
#print axioms UAVProof.A4FeeScaling.coefficient
#print axioms UAVProof.A4FeeScaling.backward
#print axioms UAVProof.A4FeeScaling.backward_append
#print axioms UAVProof.A4FeeScaling.formula
#print axioms UAVProof.A4FeeScaling.backward_history
#print axioms UAVProof.A4FeeScaling.formula_length
#print axioms UAVProof.A4FeeScaling.formula_get
#print axioms UAVProof.A4FeeScaling.rows
#print axioms UAVProof.A4FeeScaling.vector_list
#print axioms UAVProof.A4FeeScaling.rows_fst
#print axioms UAVProof.A4FeeScaling.rows_snd
#print axioms UAVProof.A4FeeScaling.formula_scaleFees
#print axioms UAVProof.A4FeeScaling.budget_scaleBudget

-- TreeBudgetFeeScalingTM2.lean
#print axioms UAVProof.A4FeeScaling.R
#print axioms UAVProof.A4FeeScaling.K
#print axioms UAVProof.A4FeeScaling.old
#print axioms UAVProof.A4FeeScaling.mr
#print axioms UAVProof.A4FeeScaling.wr
#print axioms UAVProof.A4FeeScaling.PC
#print axioms UAVProof.A4FeeScaling.mw
#print axioms UAVProof.A4FeeScaling.inputField
#print axioms UAVProof.A4FeeScaling.instr
#print axioms UAVProof.A4FeeScaling.Data
#print axioms UAVProof.A4FeeScaling.store
#print axioms UAVProof.A4FeeScaling.put
#print axioms UAVProof.A4FeeScaling.store_put
#print axioms UAVProof.A4FeeScaling.Cfg
#print axioms UAVProof.A4FeeScaling.cfg
#print axioms UAVProof.A4FeeScaling.Run
#print axioms UAVProof.A4FeeScaling.seq
#print axioms UAVProof.A4FeeScaling.forwardState
#print axioms UAVProof.A4FeeScaling.backwardState

-- TreeBudgetFeeScalingOps.lean
#print axioms UAVProof.A4FeeScaling.data_ext
#print axioms UAVProof.A4FeeScaling.copyData
#print axioms UAVProof.A4FeeScaling.clearData
#print axioms UAVProof.A4FeeScaling.readData
#print axioms UAVProof.A4FeeScaling.emitData
#print axioms UAVProof.A4FeeScaling.multiplied
#print axioms UAVProof.A4FeeScaling.mult_input
#print axioms UAVProof.A4FeeScaling.mult_output
#print axioms UAVProof.A4FeeScaling.mulData
#print axioms UAVProof.A4FeeScaling.bitData
#print axioms UAVProof.A4FeeScaling.pushData
#print axioms UAVProof.A4FeeScaling.testData
#print axioms UAVProof.A4FeeScaling.haltData

-- TreeBudgetFeeScalingForward.lean
#print axioms UAVProof.A4FeeScaling.forward_round
#print axioms UAVProof.A4FeeScaling.forward_loop

-- TreeBudgetFeeScalingBudget.lean
#print axioms UAVProof.A4FeeScaling.budget_run

-- TreeBudgetFeeScalingBackward.lean
#print axioms UAVProof.A4FeeScaling.backward_round
#print axioms UAVProof.A4FeeScaling.backward_loop

-- TreeBudgetFeeScalingBounds.lean
#print axioms UAVProof.A4FeeScaling.mass_split
#print axioms UAVProof.A4FeeScaling.history_length
#print axioms UAVProof.A4FeeScaling.instance_bounds
#print axioms UAVProof.A4FeeScaling.parsed_fee_fields

-- TreeBudgetFeeScalingCore.lean
#print axioms UAVProof.A4FeeScaling.Fields
#print axioms UAVProof.A4FeeScaling.prepare_run
#print axioms UAVProof.A4FeeScaling.coreBound
#print axioms UAVProof.A4FeeScaling.outputData
#print axioms UAVProof.A4FeeScaling.core_run

-- TreeBudgetFeeScalingEntry.lean
#print axioms UAVProof.A4FeeScaling.Entry.L
#print axioms UAVProof.A4FeeScaling.Entry.Cfg
#print axioms UAVProof.A4FeeScaling.Entry.pw
#print axioms UAVProof.A4FeeScaling.Entry.sw
#print axioms UAVProof.A4FeeScaling.Entry.program
#print axioms UAVProof.A4FeeScaling.Entry.machine
#print axioms UAVProof.A4FeeScaling.Entry.after
#print axioms UAVProof.A4FeeScaling.Entry.halted
#print axioms UAVProof.A4FeeScaling.Entry.view
#print axioms UAVProof.A4FeeScaling.Entry.Run
#print axioms UAVProof.A4FeeScaling.Entry.seq
#print axioms UAVProof.A4FeeScaling.Entry.paired_bank
#print axioms UAVProof.A4FeeScaling.Entry.scale_bank
#print axioms UAVProof.A4FeeScaling.Entry.init_eq
#print axioms UAVProof.A4FeeScaling.Entry.paired_return
#print axioms UAVProof.A4FeeScaling.Entry.true_step
#print axioms UAVProof.A4FeeScaling.Entry.false_step
#print axioms UAVProof.A4FeeScaling.Entry.return_step
#print axioms UAVProof.A4FeeScaling.Entry.finite_alphabet

-- TreeBudgetFeeScalingTotal.lean
#print axioms UAVProof.A4FeeScaling.Entry.Scaled
#print axioms UAVProof.A4FeeScaling.Entry.saved_fields
#print axioms UAVProof.A4FeeScaling.Entry.output_scaled
#print axioms UAVProof.A4FeeScaling.Entry.from_paired_success
#print axioms UAVProof.A4FeeScaling.Entry.totalBound
#print axioms UAVProof.A4FeeScaling.Entry.total_bound
#print axioms UAVProof.A4FeeScaling.Entry.scaled_from_init
#print axioms UAVProof.A4FeeScaling.Entry.scaled_wire_from_init

-- TreeBudgetFeeScalingExamples.lean
#print axioms UAVProof.A4FeeScalingChecks.run
#print axioms UAVProof.A4FeeScalingChecks.runWire
#print axioms UAVProof.A4FeeScalingChecks.outputs
#print axioms UAVProof.A4FeeScalingChecks.result
#print axioms UAVProof.A4FeeScalingChecks.repeatedDenominators
#print axioms UAVProof.A4FeeScalingChecks.carryInput
#print axioms UAVProof.A4FeeScalingChecks.positiveRoot
#print axioms UAVProof.A4FeeScalingChecks.two_vertices_exact
#print axioms UAVProof.A4FeeScalingChecks.repeated_denominators_exact
#print axioms UAVProof.A4FeeScalingChecks.carries_exact
#print axioms UAVProof.A4FeeScalingChecks.positive_root_exact
#print axioms UAVProof.A4FeeScalingChecks.zero_fields_exact
#print axioms UAVProof.A4FeeScalingChecks.saved_order_and_counts
#print axioms UAVProof.A4FeeScalingChecks.zero_count_row_retained
#print axioms UAVProof.A4FeeScalingChecks.truncated_second_record_rejected
#print axioms UAVProof.A4FeeScalingChecks.invalid_instance_rejected
#print axioms UAVProof.A4FeeScalingChecks.truncated_outer_rejected
