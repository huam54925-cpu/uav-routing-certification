import LeanCompletion.UAV.TreeBudgetCostedParsing
import LeanCompletion.UAV.TreeBudgetCostedInput
import LeanCompletion.UAV.TreeBudgetBinaryOutput

/-! One costed executable from bits to a serialized matrix or rejection.
All counters are compositional observations of the same execution. The
reference bit-cell work is distinct from address-charged time. -/
namespace UAVProof.TreeBudgetCostedExecution
open TreeBudgetBitMachine TreeBudgetCostedParsing TreeBudgetCostedInput
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryOutput TreeBudgetBinaryPipeline

def executeChecked (input : Option Input) : Costed (Option Result) :=
  match input with
  | none => ⟨none, 1, 1⟩
  | some I =>
    let out := executeInput I
    ⟨some out.value, out.steps + 1, out.allocations + 2⟩

def executeRaw (raw : Option RawInput) : Costed (Option Result) :=
  match raw with
  | none => ⟨none, 1, 1⟩
  | some I =>
    let checked := decodeRawCost I
    let out := executeChecked checked.value
    ⟨out.value, checked.steps + out.steps + 1,
      checked.allocations + out.allocations + 1⟩

def execute (bits : Bits) : Costed (Option Result) :=
  let parsed := parseInputD bits
  let out := executeRaw parsed.value
  ⟨out.value, parsed.steps + out.steps + 1,
    parsed.allocations + out.allocations + 1⟩

theorem executeChecked_value (input : Option Input) :
    (executeChecked input).value = input.map runInput := by
  cases input <;> simp [executeChecked, executeInput_value]

theorem executeRaw_value (raw : Option RawInput) :
    (executeRaw raw).value = (raw.bind decodeRaw).map runInput := by
  cases raw <;> simp [executeRaw, executeChecked_value]

/-- Includes malformed input and infeasibility. Accepted successful outputs
retain the concrete ordered cache and exactly the original six event counts. -/
theorem execute_value (bits : Bits) : (execute bits).value = run bits := by
  simp [execute, executeRaw_value, run, TreeBudgetBinaryInput.parse]

end UAVProof.TreeBudgetCostedExecution
