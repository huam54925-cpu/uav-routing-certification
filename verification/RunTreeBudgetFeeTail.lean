import LeanCompletion.UAV.TreeBudgetFeeTailExamples

#print axioms UAVProof.A4FeeTailSpec.prefix_append
#print axioms UAVProof.A4FeeTailSpec.prefix_canonical
#print axioms UAVProof.A4FeeTailSpec.read_iff
#print axioms UAVProof.A4FeeTailSpec.good_iff
#print axioms UAVProof.A4FeeTailSpec.rebuild_wire
#print axioms UAVProof.A4FeeTailSpec.parseInstance_finish
#print axioms UAVProof.A4FeeTailChecks.saved_outputs
#print axioms UAVProof.A4FeeTailChecks.rejects_zero_denominator
#print axioms UAVProof.A4FeeTailChecks.rejects_trailing
#print axioms UAVProof.A4FeeTailChecks.raw_start_accepts
#print axioms UAVProof.A4FeeTailChecks.raw_start_rejects_trailing
#print axioms UAVProof.A4FeeTailChecks.standard_init_accepts
#print axioms UAVProof.A4FeeTailChecks.raw_start_wrong_routes

namespace UAVProof.A4FeeTailChecks
open TreeBudgetBinaryCodec A4FeeTailSpec A4FeeTailMachine

/-- Input corpus uses ASCII bits. Empty cells are preserved by the tab separator. -/
def bits (s : String) : Bits := s.toList.map (· == '1')

def checkLine (line : String) : IO Unit := do
  let [tag,xs,ys,ps,vs] := line.splitOn "\t" | throw (IO.userError "invalid corpus record")
  let x := bits xs
  let y := bits ys
  let parsed := (TreeBudgetSparseVerifier.parseInstance x).isSome
  let verified := TreeBudgetSparseVerifier.verify x y
  unless parsed == (ps == "1") && verified == (vs == "1") do
    throw (IO.userError (tag ++ ": reference or certificate mismatch"))
  -- Fuel is only a bounded regression budget. It is unrelated to a time proof.
  let some out := observe 200000 (start x y) | throw (IO.userError (tag ++ ": fuel exhausted"))
  unless out.var.2 == parsed && out.stk context == y do
    throw (IO.userError (tag ++ ": machine output or context mismatch"))
  if parsed then
    let some (_,raw) := TreeBudgetSparseVerifier.parseSpecifiedRaw x
      | throw (IO.userError (tag ++ ": inconsistent raw decode"))
    let expected := [raw.numerators.flatMap encodeInt,raw.denominators.flatMap encodeNat,
      encodeInt raw.budgetNumerator,encodeNat raw.budgetDenominator]
    unless outputs out == expected && (out.stk src).isEmpty do
      throw (IO.userError (tag ++ ": wrong saved fields or nonempty suffix"))

end UAVProof.A4FeeTailChecks

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one corpus path")
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· != "")
  for line in lines do UAVProof.A4FeeTailChecks.checkLine line
  IO.println s!"Lean reference, composed instance machine and context agree on {lines.length} cases."
