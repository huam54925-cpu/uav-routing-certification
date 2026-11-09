import LeanCompletion.UAV.HubReductionExamples
import Lean.Util.CollectAxioms

/-! Audit every declaration in the five new namespaces, including generated
instances and auxiliary declarations. Fail on any axiom outside the standard
Lean whitelist. Keep the output under ignored verification/runs/.
Run after building the five modules:
  lake env lean verification/AuditHubReduction.lean
-/
open Lean Elab Command

run_cmd do
  let prefixes : List Name := [
    `UAVProof.HubGammaCodec, `UAVProof.HubReductionCodec,
    `UAVProof.HubReductionEncoding, `UAVProof.HubReductionTotal,
    `UAVProof.HubReductionExamples]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf name) then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name}: disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
  if count = 0 then throwError "No reduction declarations found"
  logInfo m!"PASS: audited {count} declarations; only propext, Classical.choice, Quot.sound allowed"
