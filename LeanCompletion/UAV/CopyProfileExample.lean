import LeanCompletion.UAV.CopyProfileDecomposition

/-!
# 四节点反例的精确轮廓最小割

固定既有结构提升 witnessFlow，证明：
* 轮廓为 (0, 2, 1, 0)；
* 服务量为 4，预算为 3；
* 轮廓最小出割 kappa = 1；
* 取整容量需求为 2，因此该轮廓割失败。

这里的 kappa 数值仅针对 witnessFlow。
-/

namespace UAVProof.CopyProfileExample

open ResourceCuts VisitCopyLift CopyFiberCompression
open CopyProfileService CopyProfileMinimum CopyProfileCuts
open CopyProfileRealizability CopyProfileDecomposition
open FixedFlowObstruction CopyLiftObstruction.FourNode

/-- 由既有违规子集定义目标轮廓。 -/
def badProfile : Node → ℕ :=
  visitProfile (0 : Node) required badSet

theorem badProfile_values :
    badProfile (0 : Node) = 0 ∧
    badProfile (1 : Node) = 2 ∧
    badProfile (2 : Node) = 1 ∧
    badProfile (3 : Node) = 0 := by
  exact CopyFiberCompression.FourNode.profile_values

/-- badSet 本身就是该轮廓的实现见证。 -/
theorem badProfile_realizable :
    RealizableProfile (0 : Node) required badProfile := by
  exact ⟨badSet, depot_not_mem_badSet, rfl⟩

theorem badProfile_bounds :
    badProfile (0 : Node) = 0 ∧
      ∀ v, v ≠ (0 : Node) → badProfile v ≤ required v := by
  exact bounds_of_realizableProfile
    (0 : Node) required badProfile badProfile_realizable

/-- 非零轮廓的任何实现子集都非空。 -/
theorem badProfile_realization_nonempty
    (S : Finset Copy)
    (hprofile : visitProfile (0 : Node) required S = badProfile) :
    S.Nonempty := by
  classical
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  subst S
  have hzero : badProfile (1 : Node) = 0 := by
    rw [← hprofile]
    simp [visitProfile, fibreCount]
  have htwo : badProfile (1 : Node) = 2 :=
    badProfile_values.2.1
  omega

/-- 上界由 badSet 给出，下界来自结构提升的正出割。 -/
theorem badProfile_kappa_eq_one :
    kappa (0 : Node) required witnessFlow
      badProfile badProfile_realizable = 1 := by
  apply le_antisymm
  · calc
      kappa (0 : Node) required witnessFlow
          badProfile badProfile_realizable ≤
          outCutFlow badSet witnessFlow :=
        kappa_le_cut
          (0 : Node) required witnessFlow
          badProfile badProfile_realizable
          badSet depot_not_mem_badSet rfl
      _ = 1 := badSet_outCut_eq_one
  · obtain ⟨S, hdepot, hprofile, hmin⟩ :=
      kappa_attained
        (0 : Node) required witnessFlow
        badProfile badProfile_realizable
    have hnonempty : S.Nonempty :=
      badProfile_realization_nonempty S hprofile
    have hpositive : 1 ≤ outCutFlow S witnessFlow :=
      witness_positive_cuts S hnonempty hdepot
    rw [hmin] at hpositive
    exact hpositive

theorem badProfile_work_eq_four :
    profileWork service badProfile = (4 : ℚ) := by
  calc
    profileWork service badProfile =
        ∑ c ∈ badSet,
          copyService (0 : Node) required service c :=
      (copy_service_eq_profileWork
        (0 : Node) required service badSet
        depot_not_mem_badSet).symm
    _ = 4 := badSet_service_eq_four

theorem badProfile_requirement_eq_two :
    Int.ceil (profileWork service badProfile / capacity) = 2 := by
  rw [badProfile_work_eq_four]
  norm_num [capacity]

/-- 精确违规证书：需要至少两次出割，但最小出割只有一次。 -/
theorem badProfile_violates_profile_cut :
    (kappa (0 : Node) required witnessFlow
      badProfile badProfile_realizable : ℤ) <
      Int.ceil (profileWork service badProfile / capacity) := by
  rw [badProfile_kappa_eq_one, badProfile_requirement_eq_two]
  norm_num

theorem witness_not_all_profile_cuts :
    ¬ AllProfileCuts
      (0 : Node) required witnessFlow service capacity := by
  intro hcuts
  have hcut := hcuts badProfile badProfile_realizable
  exact (not_le_of_gt badProfile_violates_profile_cut) hcut

/-- 同一失败也能通过明确整数范围的接口表达。 -/
theorem witness_not_all_bounded_profile_cuts :
    ¬ AllBoundedProfileCuts
      (0 : Node) required witnessFlow service capacity := by
  intro hcuts
  apply witness_not_all_profile_cuts
  exact
    (profile_cuts_iff_bounded_profile_cuts
      (0 : Node) required witnessFlow service capacity).mpr hcuts

end UAVProof.CopyProfileExample

#print axioms UAVProof.CopyProfileExample.badProfile_values
#print axioms UAVProof.CopyProfileExample.badProfile_bounds
#print axioms UAVProof.CopyProfileExample.badProfile_kappa_eq_one
#print axioms UAVProof.CopyProfileExample.badProfile_work_eq_four
#print axioms UAVProof.CopyProfileExample.badProfile_requirement_eq_two
#print axioms UAVProof.CopyProfileExample.badProfile_violates_profile_cut
#print axioms UAVProof.CopyProfileExample.witness_not_all_bounded_profile_cuts
