import LeanCompletion.UAV.TreeBudgetRootFlowTotal
import LeanCompletion.UAV.TreeBudgetRootFlowExamples

/-! Explicit named declarations in the H/root-flow batch. Raw audit output stays local. -/

-- TreeBudgetTM2CallOn
#print axioms UAVProof.TreeBudgetTM2CallOn.Wiring
#print axioms UAVProof.TreeBudgetTM2CallOn.bank
#print axioms UAVProof.TreeBudgetTM2CallOn.bank_put
#print axioms UAVProof.TreeBudgetTM2CallOn.updated
#print axioms UAVProof.TreeBudgetTM2CallOn.compile
#print axioms UAVProof.TreeBudgetTM2CallOn.embed
#print axioms UAVProof.TreeBudgetTM2CallOn.statement_step
#print axioms UAVProof.TreeBudgetTM2CallOn.selected_step
#print axioms UAVProof.TreeBudgetTM2CallOn.call_run

-- TreeBudgetRootFlowSpec
#print axioms UAVProof.TreeBudgetRootFlowSpec.selected
#print axioms UAVProof.TreeBudgetRootFlowSpec.rootSum
#print axioms UAVProof.TreeBudgetRootFlowSpec.accumulated
#print axioms UAVProof.TreeBudgetRootFlowSpec.accumulated_value
#print axioms UAVProof.TreeBudgetRootFlowSpec.accumulated_length
#print axioms UAVProof.TreeBudgetRootFlowSpec.rootSum_ofFn
#print axioms UAVProof.TreeBudgetRootFlowSpec.reference
#print axioms UAVProof.TreeBudgetRootFlowSpec.Raw
#print axioms UAVProof.TreeBudgetRootFlowSpec.front
#print axioms UAVProof.TreeBudgetRootFlowSpec.encode
#print axioms UAVProof.TreeBudgetRootFlowSpec.parse
#print axioms UAVProof.TreeBudgetRootFlowSpec.parse_encode
#print axioms UAVProof.TreeBudgetRootFlowSpec.canonical
#print axioms UAVProof.TreeBudgetRootFlowSpec.listOK
#print axioms UAVProof.TreeBudgetRootFlowSpec.suffixOK
#print axioms UAVProof.TreeBudgetRootFlowSpec.accepted
#print axioms UAVProof.TreeBudgetRootFlowSpec.accepted_encode
#print axioms UAVProof.TreeBudgetRootFlowSpec.accepts_iff
#print axioms UAVProof.TreeBudgetRootFlowSpec.occupied

-- TreeBudgetRootFlowScanTM2
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Check
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Control
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.L
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.K
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Cfg
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Stmt
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.acc
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.temp
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.entry
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.next
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.ports
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.framePorts
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.frameNext
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.comparePorts
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.equal
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.jump
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.program
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.machine
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Data
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.saved
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.store
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.cfg
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.stop
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.initial
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.start
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.Kept
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.source
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.dest
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.replace
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.replace_original
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.tapes_replace
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.conf_replace
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.copied
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.copy_job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.clear_job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.increment_job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.finite_alphabet
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.finite_control

-- TreeBudgetRootFlowScanRuns
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.frameSource
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.frameDest
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.frameSet
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.frame_layout
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.field_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.compare_layout
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.comparison
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.compared
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.compare_job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.comparison_eq
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.comparison_le
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.bits_eq
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.addition_job
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.testEnd
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.test_step
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.work
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.setup_run

-- TreeBudgetRootFlowScanLoop
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.seq
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.body_cons_ne_nil
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.pending
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.skip_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.take_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.parent_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.index_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.round_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scanEnd
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scan_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scanEnd_equal
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scanEnd_unequal
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scanEnd_kept

-- TreeBudgetRootFlowScanTotal
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.exit_run
#print axioms UAVProof.TreeBudgetRootFlowScanTM2.scan_polynomial

-- TreeBudgetRootFlowTM2
#print axioms UAVProof.TreeBudgetRootFlowTM2.K
#print axioms UAVProof.TreeBudgetRootFlowTM2.decidableStack
#print axioms UAVProof.TreeBudgetRootFlowTM2.Job
#print axioms UAVProof.TreeBudgetRootFlowTM2.Control
#print axioms UAVProof.TreeBudgetRootFlowTM2.L
#print axioms UAVProof.TreeBudgetRootFlowTM2.Cfg
#print axioms UAVProof.TreeBudgetRootFlowTM2.Stmt
#print axioms UAVProof.TreeBudgetRootFlowTM2.prefixW
#print axioms UAVProof.TreeBudgetRootFlowTM2.listW
#print axioms UAVProof.TreeBudgetRootFlowTM2.scanW
#print axioms UAVProof.TreeBudgetRootFlowTM2.context
#print axioms UAVProof.TreeBudgetRootFlowTM2.suffix
#print axioms UAVProof.TreeBudgetRootFlowTM2.demands
#print axioms UAVProof.TreeBudgetRootFlowTM2.temp
#print axioms UAVProof.TreeBudgetRootFlowTM2.entry
#print axioms UAVProof.TreeBudgetRootFlowTM2.next
#print axioms UAVProof.TreeBudgetRootFlowTM2.ports
#print axioms UAVProof.TreeBudgetRootFlowTM2.program
#print axioms UAVProof.TreeBudgetRootFlowTM2.machine
#print axioms UAVProof.TreeBudgetRootFlowTM2.Data
#print axioms UAVProof.TreeBudgetRootFlowTM2.store
#print axioms UAVProof.TreeBudgetRootFlowTM2.cfg
#print axioms UAVProof.TreeBudgetRootFlowTM2.start
#print axioms UAVProof.TreeBudgetRootFlowTM2.Run
#print axioms UAVProof.TreeBudgetRootFlowTM2.source
#print axioms UAVProof.TreeBudgetRootFlowTM2.dest
#print axioms UAVProof.TreeBudgetRootFlowTM2.setDest
#print axioms UAVProof.TreeBudgetRootFlowTM2.copied
#print axioms UAVProof.TreeBudgetRootFlowTM2.restored
#print axioms UAVProof.TreeBudgetRootFlowTM2.copy_layout
#print axioms UAVProof.TreeBudgetRootFlowTM2.original_dest
#print axioms UAVProof.TreeBudgetRootFlowTM2.copy_job
#print axioms UAVProof.TreeBudgetRootFlowTM2.prefix_bank
#print axioms UAVProof.TreeBudgetRootFlowTM2.list_bank
#print axioms UAVProof.TreeBudgetRootFlowTM2.scan_bank
#print axioms UAVProof.TreeBudgetRootFlowTM2.finite_alphabet
#print axioms UAVProof.TreeBudgetRootFlowTM2.finite_control

-- TreeBudgetRootFlowRuns
#print axioms UAVProof.TreeBudgetRootFlowTM2.seq
#print axioms UAVProof.TreeBudgetRootFlowTM2.prefix_return
#print axioms UAVProof.TreeBudgetRootFlowTM2.prefix_continue
#print axioms UAVProof.TreeBudgetRootFlowTM2.list_input
#print axioms UAVProof.TreeBudgetRootFlowTM2.list_halted
#print axioms UAVProof.TreeBudgetRootFlowTM2.list_continue
#print axioms UAVProof.TreeBudgetRootFlowTM2.prepare_run
#print axioms UAVProof.TreeBudgetRootFlowTM2.scan_call

-- TreeBudgetRootFlowTotal
#print axioms UAVProof.TreeBudgetRootFlowTM2.SavedPrefix
#print axioms UAVProof.TreeBudgetRootFlowTM2.SavedH
#print axioms UAVProof.TreeBudgetRootFlowTM2.root_flow_polynomial
#print axioms UAVProof.TreeBudgetRootFlowTM2.saved_fields
#print axioms UAVProof.TreeBudgetRootFlowTM2.init_eq
#print axioms UAVProof.TreeBudgetRootFlowTM2.root_flow_from_init
#print axioms UAVProof.TreeBudgetRootFlowTM2.inputFields
#print axioms UAVProof.TreeBudgetRootFlowTM2.inputFields_encoding
#print axioms UAVProof.TreeBudgetRootFlowTM2.parse_inputFields

-- TreeBudgetRootFlowExamples
#print axioms UAVProof.TreeBudgetRootFlowExamples.observe
#print axioms UAVProof.TreeBudgetRootFlowExamples.acceptsWithin
#print axioms UAVProof.TreeBudgetRootFlowExamples.input
#print axioms UAVProof.TreeBudgetRootFlowExamples.exclude_root_and_grandchild
#print axioms UAVProof.TreeBudgetRootFlowExamples.root_flow_mismatch
#print axioms UAVProof.TreeBudgetRootFlowExamples.full_carry
#print axioms UAVProof.TreeBudgetRootFlowExamples.singleton_large_root
#print axioms UAVProof.TreeBudgetRootFlowExamples.malformed_fee_tail_preserved
#print axioms UAVProof.TreeBudgetRootFlowExamples.short_h
#print axioms UAVProof.TreeBudgetRootFlowExamples.long_h
#print axioms UAVProof.TreeBudgetRootFlowExamples.rawH
#print axioms UAVProof.TreeBudgetRootFlowExamples.huge_h_count_short_suffix
#print axioms UAVProof.TreeBudgetRootFlowExamples.truncated_h_field
#print axioms UAVProof.TreeBudgetRootFlowExamples.noncanonical_h_field
#print axioms UAVProof.TreeBudgetRootFlowExamples.invalid_tree_rejected
#print axioms UAVProof.TreeBudgetRootFlowExamples.scanFlag
#print axioms UAVProof.TreeBudgetRootFlowExamples.padded_accumulator_equality
