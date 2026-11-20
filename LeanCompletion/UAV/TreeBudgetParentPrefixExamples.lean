import LeanCompletion.UAV.TreeBudgetParentPrefixTM2

/-! Kernel reductions from raw input bits, never from a preinstalled parent
array. These assertions exercise the actual combined transition function. -/
namespace UAVProof.TreeBudgetParentPrefixExamples
open TreeBudgetBinaryCodec TreeBudgetParentPrefixTM2

def observe : ℕ → Cfg → Option (Bool × Bits × Bits × Bits × Bits × ℕ)
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some (c.var.2,c.stk suffix,c.stk context,c.stk parsedBody,c.stk parsedRoot,
        value (c.stk (.inl TreeBudgetWholeTreeTM2.index)))
    | some d => observe fuel d

def input (n r : ℕ) (parents : List ℕ) (rest : Bits) : Bits :=
  TreeBudgetParentPrefix.encode ⟨7,n,r,parents,rest⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

theorem dimension_mismatch : observe 5000 (start (input 3 0 [0,0] [true,false]) [false,true]) =
    some (false,[true,false],[false,true],[0,0].flatMap encodeNat,(0 : ℕ).bits,2) := by rfl

theorem parent_equal_to_n : observe 5000 (start (input 2 0 [0,2] [false,true]) [true]) =
    some (false,[false,true],[true],[0,2].flatMap encodeNat,(0 : ℕ).bits,1) := by rfl

/-- All range checks pass. The invoked tree machine then reaches vertex 2. -/
theorem late_disjoint_cycle : observe 18000 (start (input 4 0 [0,0,3,2] [true,false,true]) [false]) =
    some (false,[true,false,true],[false],[0,0,3,2].flatMap encodeNat,(0 : ℕ).bits,2) := by rfl

/-- The unparsed suffix is a canonical H list followed by further fields. -/
theorem h_suffix_preserved : observe 12000
    (start (input 3 2 [2,2,2] (encodeNats [4,0,9] ++ [true,false,true])) [true,false]) =
    some (true,encodeNats [4,0,9] ++ [true,false,true],[true,false],
      [2,2,2].flatMap encodeNat,(2 : ℕ).bits,3) := by rfl

def acceptsWithin : ℕ → Cfg → Option (Bool × Bits)
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some (c.var.2,c.stk context)
    | some d => acceptsWithin fuel d

theorem huge_count_short_suffix : acceptsWithin 3000
    (start (encodeNat 1 ++ encodeNat 1 ++ encodeNat 0 ++ encodeNat 1048576 ++ [false]) [true,false]) =
      some (false,[true,false]) := by rfl

theorem truncated_header : acceptsWithin 100 (start [true] [false,true,false]) =
    some (false,[false,true,false]) := by rfl

theorem noncanonical_header : acceptsWithin 100 (start [true,false,false] [true]) =
    some (false,[true]) := by rfl

theorem empty_parent_table : acceptsWithin 2000 (start (input 0 0 [] [true]) [false]) =
    some (false,[false]) := by rfl

end UAVProof.TreeBudgetParentPrefixExamples
