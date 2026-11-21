import LeanCompletion.UAV.TreeBudgetCertificateRecordsTotal
import LeanCompletion.UAV.TreeBudgetCertificateRecordsExamples

/-! Every explicit named declaration in the certificate-record parser batch. -/

-- TreeBudgetEntryLayout
#print axioms UAVProof.TreeBudgetCountedNatsTM2.returned
#print axioms UAVProof.TreeBudgetCountedNatsTM2.stopped_success
#print axioms UAVProof.TreeBudgetEntryTM2.returned
#print axioms UAVProof.TreeBudgetEntryTM2.stopped_success
#print axioms UAVProof.TreeBudgetEntryTM2.stopped_flag
#print axioms UAVProof.TreeBudgetEntryTM2.returned_fields
#print axioms UAVProof.TreeBudgetEntryTM2.returned_scratch
#print axioms UAVProof.TreeBudgetEntryTM2.stopped_halted
#print axioms UAVProof.TreeBudgetEntryTM2.entry_success_run
#print axioms UAVProof.TreeBudgetEntryTM2.entry_layout_polynomial

-- TreeBudgetCertificateRecordsSpec
#print axioms UAVProof.A4CertRecords.sizedEntries
#print axioms UAVProof.A4CertRecords.sizedEntries_append
#print axioms UAVProof.A4CertRecords.sizedEntries_sound
#print axioms UAVProof.A4CertRecords.packet
#print axioms UAVProof.A4CertRecords.packet_encode
#print axioms UAVProof.A4CertRecords.packet_iff
#print axioms UAVProof.A4CertRecords.packet_isSome

-- TreeBudgetCertificateRecordsTM2
#print axioms UAVProof.A4CertRecords.Aux
#print axioms UAVProof.A4CertRecords.K
#print axioms UAVProof.A4CertRecords.Job
#print axioms UAVProof.A4CertRecords.L
#print axioms UAVProof.A4CertRecords.Cfg
#print axioms UAVProof.A4CertRecords.Stmt
#print axioms UAVProof.A4CertRecords.gs
#print axioms UAVProof.A4CertRecords.es
#print axioms UAVProof.A4CertRecords.cursor
#print axioms UAVProof.A4CertRecords.rowBody
#print axioms UAVProof.A4CertRecords.mult
#print axioms UAVProof.A4CertRecords.savedBody
#print axioms UAVProof.A4CertRecords.savedCount
#print axioms UAVProof.A4CertRecords.ctxStack
#print axioms UAVProof.A4CertRecords.gw
#print axioms UAVProof.A4CertRecords.ew
#print axioms UAVProof.A4CertRecords.ports
#print axioms UAVProof.A4CertRecords.next
#print axioms UAVProof.A4CertRecords.jump
#print axioms UAVProof.A4CertRecords.reject
#print axioms UAVProof.A4CertRecords.program
#print axioms UAVProof.A4CertRecords.machine
#print axioms UAVProof.A4CertRecords.start
#print axioms UAVProof.A4CertRecords.recordBound
#print axioms UAVProof.A4CertRecords.RecordsPolynomialSpec

-- TreeBudgetCertificateRecordsData
#print axioms UAVProof.A4CertRecords.Data
#print axioms UAVProof.A4CertRecords.store
#print axioms UAVProof.A4CertRecords.cfg
#print axioms UAVProof.A4CertRecords.stop
#print axioms UAVProof.A4CertRecords.Run
#print axioms UAVProof.A4CertRecords.seq
#print axioms UAVProof.A4CertRecords.Kept
#print axioms UAVProof.A4CertRecords.work
#print axioms UAVProof.A4CertRecords.source
#print axioms UAVProof.A4CertRecords.dest
#print axioms UAVProof.A4CertRecords.replace
#print axioms UAVProof.A4CertRecords.replace_original
#print axioms UAVProof.A4CertRecords.tapes_replace
#print axioms UAVProof.A4CertRecords.conf_replace
#print axioms UAVProof.A4CertRecords.copied
#print axioms UAVProof.A4CertRecords.copy_job
#print axioms UAVProof.A4CertRecords.clear_mult
#print axioms UAVProof.A4CertRecords.increment_job
#print axioms UAVProof.A4CertRecords.finite_alphabet
#print axioms UAVProof.A4CertRecords.finite_control

-- TreeBudgetCertificateRecordsGuard
#print axioms UAVProof.A4CertRecords.Guard.outside
#print axioms UAVProof.A4CertRecords.Guard.lift
#print axioms UAVProof.A4CertRecords.Guard.GRun
#print axioms UAVProof.A4CertRecords.Guard.lift_step
#print axioms UAVProof.A4CertRecords.Guard.headerPorts
#print axioms UAVProof.A4CertRecords.Guard.headerLabels
#print axioms UAVProof.A4CertRecords.Guard.headerBase
#print axioms UAVProof.A4CertRecords.Guard.header_cfg
#print axioms UAVProof.A4CertRecords.Guard.header_link
#print axioms UAVProof.A4CertRecords.Guard.header_run
#print axioms UAVProof.A4CertRecords.Guard.ones_run
#print axioms UAVProof.A4CertRecords.Guard.clear_run
#print axioms UAVProof.A4CertRecords.Guard.borrow_run
#print axioms UAVProof.A4CertRecords.Guard.restore_run
#print axioms UAVProof.A4CertRecords.Guard.guard_run
#print axioms UAVProof.A4CertRecords.Guard.precheck_run
#print axioms UAVProof.A4CertRecords.Guard.start_eq

-- TreeBudgetCertificateRecordsCalls
#print axioms UAVProof.A4CertRecords.afterEntry
#print axioms UAVProof.A4CertRecords.entry_input
#print axioms UAVProof.A4CertRecords.entry_return
#print axioms UAVProof.A4CertRecords.entry_success
#print axioms UAVProof.A4CertRecords.entry_failure

-- TreeBudgetCertificateRecordsRow
#print axioms UAVProof.A4CertRecords.row_nil
#print axioms UAVProof.A4CertRecords.row_zero
#print axioms UAVProof.A4CertRecords.row_pair
#print axioms UAVProof.A4CertRecords.row_field
#print axioms UAVProof.A4CertRecords.row_fields
#print axioms UAVProof.A4CertRecords.equal_nil
#print axioms UAVProof.A4CertRecords.equal_left
#print axioms UAVProof.A4CertRecords.equal_right
#print axioms UAVProof.A4CertRecords.equal_pair
#print axioms UAVProof.A4CertRecords.equalEnd
#print axioms UAVProof.A4CertRecords.equal_run
#print axioms UAVProof.A4CertRecords.equalEnd_same
#print axioms UAVProof.A4CertRecords.equalEnd_different
#print axioms UAVProof.A4CertRecords.equalEnd_kept
#print axioms UAVProof.A4CertRecords.bits_eq

-- TreeBudgetCertificateRecordsRound
#print axioms UAVProof.A4CertRecords.cleaned
#print axioms UAVProof.A4CertRecords.entry_size_bounds
#print axioms UAVProof.A4CertRecords.row_check_run
#print axioms UAVProof.A4CertRecords.tick_cons
#print axioms UAVProof.A4CertRecords.round_run

-- TreeBudgetCertificateRecordsLoop
#print axioms UAVProof.A4CertRecords.tailFlag
#print axioms UAVProof.A4CertRecords.finish_run
#print axioms UAVProof.A4CertRecords.loop_polynomial

-- TreeBudgetCertificateRecordsTotal
#print axioms UAVProof.A4CertRecords.initial
#print axioms UAVProof.A4CertRecords.prepared_guard
#print axioms UAVProof.A4CertRecords.prepare_run
#print axioms UAVProof.A4CertRecords.guard_failure
#print axioms UAVProof.A4CertRecords.guard_result
#print axioms UAVProof.A4CertRecords.records_polynomial

-- TreeBudgetCertificateRecordsExamples
#print axioms UAVProof.A4CertRecords.run
#print axioms UAVProof.A4CertRecords.result
#print axioms UAVProof.A4CertRecords.accepted
#print axioms UAVProof.A4CertRecords.empty_good
#print axioms UAVProof.A4CertRecords.empty_trailing
#print axioms UAVProof.A4CertRecords.count_is_not_multiplicity
#print axioms UAVProof.A4CertRecords.count_too_large
#print axioms UAVProof.A4CertRecords.second_cut
#print axioms UAVProof.A4CertRecords.short_row
#print axioms UAVProof.A4CertRecords.long_row
#print axioms UAVProof.A4CertRecords.zero_dim_nonempty
#print axioms UAVProof.A4CertRecords.ordered
#print axioms UAVProof.A4CertRecords.saved_in_order
#print axioms UAVProof.A4CertRecords.same_row_different_counts
