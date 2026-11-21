import LeanCompletion.UAV.TreeBudgetFeeScalingExamples
import LeanCompletion.UAV.TreeBudgetFeeScalingTotal

namespace UAVProof.A4FeeScalingChecks
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetVectorChecker A4FeeScaling A4FeeScaling.Entry Turing

def bits (s : String) : Bits := s.toList.map (· == '1')

def checkCase (line : String) : IO Unit := do
  let [tag,wire,wanted,wfees,wbudget] := line.splitOn "\t" |
    throw (IO.userError "bad corpus line")
  let s := bits wire
  let some c := run (totalBound s.length+1) (initList machine s) |
    throw (IO.userError (tag++": transition bound exhausted"))
  unless c.l.isNone && c.var.2 == A4PairedParser.wireAccepted s do
    throw (IO.userError (tag++": result mismatch"))
  unless wanted == "-" || c.var.2 == (wanted == "1") do
    throw (IO.userError (tag++": named result mismatch"))
  if c.var.2 then
    let some (x,y) := parseWord s | throw (IO.userError "missing pair")
    let some I := parseInstance x | throw (IO.userError "missing instance")
    let some C := decodeCertificate I.data.n y | throw (IO.userError "missing certificate")
    let some (m,raw) := parseSpecifiedRaw x | throw (IO.userError "missing raw instance")
    unless c.stk (wr .fees) ==
        (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList.flatMap encodeInt &&
        c.stk (wr .budget) == encodeInt (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator) do
      throw (IO.userError (tag++": scaled output mismatch"))
    unless wfees == "-" || c.stk (wr .fees) == bits wfees do
      throw (IO.userError (tag++": independent fee answer mismatch"))
    unless wbudget == "-" || c.stk (wr .budget) == bits wbudget do
      throw (IO.userError (tag++": independent budget answer mismatch"))
    unless A4PairedParserChecks.instanceWords (view c) ==
        [m.bits,raw.n.bits,raw.root.bits,raw.parents.flatMap encodeNat,
          raw.multiplicities.flatMap encodeNat,raw.numerators.flatMap encodeInt,
          raw.denominators.flatMap encodeNat,encodeInt raw.budgetNumerator,
          encodeNat raw.budgetDenominator,[]] do
      throw (IO.userError (tag++": saved instance mismatch"))
    let rawC := toRaw C
    unless A4PairedParserChecks.certificateWords (view c) ==
        [I.data.n.bits,List.replicate rawC.length true,rawC.flatMap encodeEntry,[]] do
      throw (IO.userError (tag++": saved certificate order/count mismatch"))
    let some p := A4PairedParserChecks.run (A4PairedParser.pairBound (x.length+y.length)+1)
        (initList A4PairedParser.machine s) | throw (IO.userError "paired run exhausted")
    let some q := run (coreBound x.length+3) (after p) |
      throw (IO.userError (tag++": instance-only scaling bound exhausted"))
    unless q.l.isNone && q.var.2 && q.stk (wr .fees) == c.stk (wr .fees) &&
        q.stk (wr .budget) == c.stk (wr .budget) &&
        decide (∀ k : A4PairedParser.K, q.stk (old k)=p.stk k) do
      throw (IO.userError (tag++": scaling call or complete saved bank mismatch"))
    for r in (List.ofFn (fun i : Fin 14 => match i.val with
      | 0 => R.nums | 1 => .dens | 2 => .bnum | 3 => .bden | 4 => .pre | 5 => .suf
      | 6 => .a | 7 => .b | 8 => .prefixRev | 9 => .numRev | 10 => .denRev
      | 11 => .signRev | 12 => .sign | _ => .scratch)) do
      unless c.stk (wr r) == [] do throw (IO.userError (tag++": unclean working register"))
    for i in List.finRange 6 do
      unless c.stk (mr i) == [] do throw (IO.userError (tag++": unclean product register"))

end UAVProof.A4FeeScalingChecks

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a corpus path")
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· != "")
  for line in lines do UAVProof.A4FeeScalingChecks.checkCase line
  IO.println s!"fee scaler agrees with specification on {lines.length} cases"
