import LeanCompletion.UAV.TreeBudgetPairedParserTotal
import LeanCompletion.UAV.TreeBudgetPairedParserExamples

/-! Explicit declaration audit, including bounded-run definitions. -/

-- TreeBudgetPairedParserExamples.lean
#print axioms UAVProof.A4PairedParserChecks.run
#print axioms UAVProof.A4PairedParserChecks.runWire
#print axioms UAVProof.A4PairedParserChecks.result
#print axioms UAVProof.A4PairedParserChecks.rootOnly
#print axioms UAVProof.A4PairedParserChecks.rootInput
#print axioms UAVProof.A4PairedParserChecks.zeroRow
#print axioms UAVProof.A4PairedParserChecks.twoVertices
#print axioms UAVProof.A4PairedParserChecks.twoInput
#print axioms UAVProof.A4PairedParserChecks.records
#print axioms UAVProof.A4PairedParserChecks.instanceWords
#print axioms UAVProof.A4PairedParserChecks.certificateWords
#print axioms UAVProof.A4PairedParserChecks.empty_records_accept
#print axioms UAVProof.A4PairedParserChecks.zero_count_row_parses
#print axioms UAVProof.A4PairedParserChecks.empty_records_verify
#print axioms UAVProof.A4PairedParserChecks.zero_count_row_fails_semantics
#print axioms UAVProof.A4PairedParserChecks.saved_both_banks
#print axioms UAVProof.A4PairedParserChecks.wrong_row_size_rejects
#print axioms UAVProof.A4PairedParserChecks.second_record_cut_rejects
#print axioms UAVProof.A4PairedParserChecks.certificate_trailing_rejects
#print axioms UAVProof.A4PairedParserChecks.instance_trailing_rejects
#print axioms UAVProof.A4PairedParserChecks.instance_failure_keeps_certificate
#print axioms UAVProof.A4PairedParserChecks.truncated_outer_rejects
#print axioms UAVProof.A4PairedParserChecks.empty_instance_rejects

-- TreeBudgetPairedParserRuns.lean
#print axioms UAVProof.A4PairedParser.instance_bank
#print axioms UAVProof.A4PairedParser.records_bank
#print axioms UAVProof.A4PairedParser.init_eq
#print axioms UAVProof.A4PairedParser.split_layout
#print axioms UAVProof.A4PairedParser.split_run
#print axioms UAVProof.A4PairedParser.instance_return
#print axioms UAVProof.A4PairedParser.instance_true
#print axioms UAVProof.A4PairedParser.instance_false
#print axioms UAVProof.A4PairedParser.dimension_layout
#print axioms UAVProof.A4PairedParser.dimension_run
#print axioms UAVProof.A4PairedParser.records_return
#print axioms UAVProof.A4PairedParser.split_truncated
#print axioms UAVProof.A4PairedParser.bad_step

-- TreeBudgetPairedParserSpec.lean
#print axioms UAVProof.A4PairedParser.accepted
#print axioms UAVProof.A4PairedParser.wireAccepted
#print axioms UAVProof.A4PairedParser.wireAccepted_pair
#print axioms UAVProof.A4PairedParser.parsed_fields
#print axioms UAVProof.A4PairedParser.recordBound_cubic
#print axioms UAVProof.A4PairedParser.pairBound
#print axioms UAVProof.A4PairedParser.combined_bound

-- TreeBudgetPairedParserTM2.lean
#print axioms UAVProof.A4PairedParser.K
#print axioms UAVProof.A4PairedParser.L
#print axioms UAVProof.A4PairedParser.Cfg
#print axioms UAVProof.A4PairedParser.Stmt
#print axioms UAVProof.A4PairedParser.ik
#print axioms UAVProof.A4PairedParser.ck
#print axioms UAVProof.A4PairedParser.scratch
#print axioms UAVProof.A4PairedParser.iw
#print axioms UAVProof.A4PairedParser.cw
#print axioms UAVProof.A4PairedParser.framePorts
#print axioms UAVProof.A4PairedParser.dimPorts
#print axioms UAVProof.A4PairedParser.program
#print axioms UAVProof.A4PairedParser.machine
#print axioms UAVProof.A4PairedParser.store
#print axioms UAVProof.A4PairedParser.certBase
#print axioms UAVProof.A4PairedParser.base
#print axioms UAVProof.A4PairedParser.afterInstance
#print axioms UAVProof.A4PairedParser.stopped
#print axioms UAVProof.A4PairedParser.instanceView
#print axioms UAVProof.A4PairedParser.Run
#print axioms UAVProof.A4PairedParser.seq
#print axioms UAVProof.A4PairedParser.Saved
#print axioms UAVProof.A4PairedParser.finite_alphabet
#print axioms UAVProof.A4PairedParser.finite_control

-- TreeBudgetPairedParserTotal.lean
#print axioms UAVProof.A4PairedParser.paired_from_init
#print axioms UAVProof.A4PairedParser.wire_from_init
