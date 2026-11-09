import LeanCompletion.UAV.HubReductionTotal

/-! Kernel-reduced format and boundary regressions. General correctness is
proved in the imported modules; these examples lock the wire conventions. -/
namespace UAVProof.HubReductionExamples
open HubGammaCodec HubReductionCodec HubReductionEncoding HubReductionTotal

theorem gamma_small : [0,1,2,3].map encodeGamma =
    [[true],[false,true,false],[false,true,true],[false,false,true,false,false]] := by
  decide +kernel

theorem gamma_boundaries : [7,8,15,16,31,32].map gammaLength = [7,7,9,9,11,11] := by
  decide +kernel

theorem gamma_truncated : parseGamma [] = none ∧ parseGamma [false,false] = none ∧
    parseGamma [false,true] = none := by decide +kernel

theorem integer_suffix : parseGamma (encodeGamma 1024 ++ [false,true]) =
    some (1024,[false,true]) := parseGamma_append _ _

def goodSource : Source := ⟨2,30,[9,10,11,9,10,11]⟩

theorem good_source_roundtrip : decodeSource (encodeSource goodSource) = some goodSource := by
  decide +kernel

theorem good_target_roundtrip : decodeTarget (encodeTarget (canonicalTarget goodSource)) =
    some (canonicalTarget goodSource) := by decide +kernel

theorem source_tails_rejected :
    decodeSource (encodeSource goodSource ++ encodeGamma 0) = none ∧
    decodeSource (encodeSource goodSource ++ [false]) = none := by decide +kernel

theorem target_tails_rejected :
    decodeTarget (encodeTarget (canonicalTarget goodSource) ++ encodeGamma 0) = none ∧
    decodeTarget (encodeTarget (canonicalTarget goodSource) ++ [false]) = none := by decide +kernel

theorem huge_headers_short_input :
    decodeSource (encodeAll [2^100,1]) = none ∧
    decodeTarget (encodeAll [2^100,0,0]) = none := by decide +kernel

theorem zero_vertex_rejected : decodeTarget (encodeAll [0,0,0]) = none := by decide +kernel

theorem invalid_parent_rejected :
    decodeTarget (encodeTarget ⟨2,0,0,[(1,0)],[0,0],[0,0]⟩) = none := by decide +kernel

theorem general_tree_roundtrip :
    decodeTarget (encodeTarget ⟨4,1,9,[(0,1),(1,2),(0,0)],
      [0,3,2,0],[7,1,2,0]⟩) =
      some ⟨4,1,9,[(0,1),(1,2),(0,0)],[0,3,2,0],[7,1,2,0]⟩ := by decide +kernel

theorem zero_budget_target_accepted :
    decodeTarget (encodeTarget (canonicalTarget ⟨0,0,[]⟩)) =
      some (canonicalTarget ⟨0,0,[]⟩) := by decide +kernel

theorem empty_zero_source_parses : decodeSource (encodeSource ⟨0,0,[]⟩) =
    some ⟨0,0,[]⟩ := by decide +kernel

theorem empty_zero_source_maps_to_no : reduceBits (encodeSource ⟨0,0,[]⟩) = noBits := by
  decide +kernel

/-- This feasible direct target explains why the total reduction must also
check source validity after successful format parsing. -/
theorem empty_zero_direct_target_feasible : SparseFeasible (canonicalTarget ⟨0,0,[]⟩) := by
  rw [canonicalTarget_feasible_iff _ (by decide), HubThreePartition.routing_iff_unitMatrix]
  refine ⟨fun r => Fin.elim0 r, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro r; exact Fin.elim0 r

theorem empty_positive_source_reduces : reduceBits (encodeSource ⟨0,1,[]⟩) =
    encodeTarget (canonicalTarget ⟨0,1,[]⟩) := by decide +kernel

theorem fixed_no_lengths : (encodeSource noSource).length = 54 ∧ noBits.length = 129 := by
  decide +kernel

theorem malformed_reduces_to_no : reduceBits [false] = noBits := by decide +kernel

end UAVProof.HubReductionExamples
