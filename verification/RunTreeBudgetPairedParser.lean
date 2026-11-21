import LeanCompletion.UAV.TreeBudgetPairedParserExamples

namespace UAVProof.A4PairedParserChecks
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier A4PairedParser Turing

def bits (s : String) : Bits := s.toList.map (· == '1')

def checkCase (line : String) : IO Unit := do
  let [tag,wire,wanted,semantic] := line.splitOn "\t" |
    throw (IO.userError "bad corpus line")
  let s := bits wire
  let bound := match parseWord s with
    | some (x,y) => pairBound (x.length+y.length)
    | none => pairBound s.length
  let some c := run (bound+1) (initList machine s) |
    throw (IO.userError (tag ++ ": transition bound exhausted"))
  unless c.l.isNone && c.var.2 == wireAccepted s do
    throw (IO.userError (tag ++ ": result mismatch"))
  unless wanted == "-" || c.var.2 == (wanted == "1") do
    throw (IO.userError (tag ++ ": named acceptance mismatch"))
  if let some (x,y) := parseWord s then
    unless semantic == "-" || verify x y == (semantic == "1") do
      throw (IO.userError (tag ++ ": semantic boundary mismatch"))
    if let some I := parseInstance x then
      let some (m,raw) := parseSpecifiedRaw x | throw (IO.userError "missing raw instance")
      unless instanceWords c ==
          [m.bits,raw.n.bits,raw.root.bits,raw.parents.flatMap encodeNat,
            raw.multiplicities.flatMap encodeNat,raw.numerators.flatMap encodeInt,
            raw.denominators.flatMap encodeNat,encodeInt raw.budgetNumerator,
            encodeNat raw.budgetDenominator,[]] &&
          c.stk (ik A4FeeTailMachine.context) == [] &&
          c.stk (ck (.inr .dim)) == I.data.n.bits do
        throw (IO.userError (tag ++ ": saved instance or loaded dimension mismatch"))
      if let some C := decodeCertificate I.data.n y then
        let rawC := toRaw C
        unless certificateWords c ==
            [I.data.n.bits,List.replicate rawC.length true,rawC.flatMap encodeEntry,[]] do
          throw (IO.userError (tag ++ ": saved certificate mismatch"))
    else
      unless c.stk (ck A4CertRecords.savedBody) == y do
        throw (IO.userError (tag ++ ": certificate consumed after instance failure"))

end UAVProof.A4PairedParserChecks

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a corpus path")
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· != "")
  for line in lines do UAVProof.A4PairedParserChecks.checkCase line
  IO.println s!"paired parser agrees with specification on {lines.length} cases"
