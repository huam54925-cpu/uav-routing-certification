import LeanCompletion.UAV.TreeBudgetCertificateRecordsExamples

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec
def bitString (s : String) : Bits := s.toList.map (· == '1')

def checkCase (line : String) : IO Unit := do
  let [tag,ns,ys,cs,vs] := line.splitOn "\t" | throw (IO.userError "bad corpus line")
  let some n := ns.toNat? | throw (IO.userError "bad n")
  let y := bitString ys
  let ctx := bitString cs
  let dec := TreeBudgetSparseCodec.decodeCertificate n y
  let some c := run (recordBound y.length n.bits.length + 1) (start n y ctx) |
    throw (IO.userError (tag ++ ": proposed transition bound exhausted"))
  unless c.var.2 == (vs == "1") && dec.isSome == c.var.2 &&
    c.stk ctxStack == ctx && c.stk (.inr .dim) == n.bits do
    throw (IO.userError (tag ++ ": mismatch"))
  if let some cert := dec then
    let raw := TreeBudgetSparseCodec.toRaw cert
    unless c.stk savedCount == List.replicate raw.length true &&
      c.stk savedBody == raw.flatMap TreeBudgetSparseCodec.encodeEntry && (c.stk cursor).isEmpty do
      throw (IO.userError (tag ++ ": record output mismatch"))
end UAVProof.A4CertRecords

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a corpus path")
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· != "")
  for line in lines do UAVProof.A4CertRecords.checkCase line
  IO.println s!"record machine and repository decoder agree on {lines.length} cases"
