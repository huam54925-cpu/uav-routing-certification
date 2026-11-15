import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats

/-! Public axiom audit. Raw output stays under verification/runs/. -/

-- TreeBudgetSubtreeAutoScaleSeed
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.denLCM
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.denLCM_pos
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.den_dvd_denLCM
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.denLCM_le_product
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.scaleNum
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.scaleNum_spec
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.normalizedWeight
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.weightList
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.Prepared
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.prepare
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.prepare_pos
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.normalizedWeight_mem
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.prepare_weight
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.prepare_root
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.prepare_budget
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.checkAuto
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.checkAuto_eq
#print axioms UAVProof.TreeBudgetSubtreeAutoScaleSeed.check_scale_independent

-- TreeBudgetSubtreeIntegerWitnessSeed
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.Matrix
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.dedupKey_natural
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.Entry
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.Inside
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.Root
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.liftEntry
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.liftInside
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.liftRoot
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.liftEntry_matrix
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.dedupEntry_lift
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.inside
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.glue
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.glue_lift
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.node
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.compute
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.roots
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.certificate
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.certificate_lift
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solve
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.inside_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.node_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.compute_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.roots_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solve_lift_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_eq
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solve_scale_independent
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_sound
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_none_iff
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_size
#print axioms UAVProof.TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_exact_iff

-- TreeBudgetSubtreeAutoExamples
#print axioms UAVProof.TreeBudgetSubtreeAutoExamples.observe
#print axioms UAVProof.TreeBudgetSubtreeAutoExamples.checkCase
#print axioms UAVProof.TreeBudgetSubtreeAutoExamples.runCases

#print axioms UAVProof.TreeBudgetSubtreeInteger.inside_cons_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootFold_cons_eq
#print axioms UAVProof.TreeBudgetSubtreeInteger.insideMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.rootMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.computeMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeInteger.checkMeasured_erase
#print axioms UAVProof.TreeBudgetSubtreeWitness.inside_cons_eq
#print axioms UAVProof.TreeBudgetSubtreeWitness.roots_cons_eq
#print axioms UAVProof.TreeBudgetSubtreeWitness.inside_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.roots_keys
#print axioms UAVProof.TreeBudgetSubtreeWitness.compute_keys
