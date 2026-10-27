import LeanCompletion.UAV.CopyProfileRealizability
import LeanCompletion.UAV.CopyProfileCuts

/-!
# 有界轮廓割与预算可行精确路线分解

保持原模型：
* 物理流无自环；
* 服务费用非负；
* 预算严格为正；
* 路线数等于基地出流；
* 只计服务费用，不含飞行费用。

本模块组合已有定理，不提供提升搜索或最小割计算算法。
-/

namespace UAVProof.CopyProfileDecomposition

open ResourceCuts VisitCopyLift CopyLiftObstruction
open CopyProfileService CopyProfileMinimum CopyProfileCuts
open CopyProfileRealizability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 只对明确整数范围内的轮廓要求最小割不等式。 -/
def AllBoundedProfileCuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∀ (q : V → ℕ)
    (hzero : q depot = 0)
    (hbound : ∀ v, v ≠ depot → q v ≤ required v),
    Int.ceil (profileWork service q / T) ≤
      (kappa depot required y q
        (realizableProfile_of_bounds
          depot required q hzero hbound) : ℤ)

/-- 可实现轮廓量化与明确整数范围量化完全等价。 -/
theorem profile_cuts_iff_bounded_profile_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    AllProfileCuts depot required y service T ↔
      AllBoundedProfileCuts depot required y service T := by
  constructor
  · intro h q hzero hbound
    exact h q
      (realizableProfile_of_bounds
        depot required q hzero hbound)
  · intro h q hq
    obtain ⟨hzero, hbound⟩ :=
      bounds_of_realizableProfile depot required q hq
    exact h q hzero hbound

/-- 固定同一个副本流：
服务提升条件等价于结构条件加全部有界轮廓割。 -/
theorem serviceCopyLift_iff_structural_bounded_profile_cuts
    (depot : V) (required : V → ℕ)
    (x : V → V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    IsServiceCopyLift depot required x service T y ↔
      IsStructuralCopyLift depot required x y ∧
        AllBoundedProfileCuts depot required y service T := by
  constructor
  · intro h
    refine ⟨{
      project_exact := h.project_exact
      out_one := h.out_one
      in_one := h.in_one
      positive_cuts := h.positive_cuts
    }, ?_⟩
    apply
      (profile_cuts_iff_bounded_profile_cuts
        depot required y service T).mp
    exact
      (nonempty_copy_cuts_iff_profile_cuts
        depot required y service T).mp h.rounded_cuts
  · rintro ⟨hstruct, hcuts⟩
    refine {
      project_exact := hstruct.project_exact
      out_one := hstruct.out_one
      in_one := hstruct.in_one
      positive_cuts := hstruct.positive_cuts
      rounded_cuts := ?_
    }
    apply
      (nonempty_copy_cuts_iff_profile_cuts
        depot required y service T).mpr
    exact
      (profile_cuts_iff_bounded_profile_cuts
        depot required y service T).mpr hcuts

/-- 主定理：
预算可行精确分解存在，当且仅当存在一个结构提升，
使明确整数范围内的全部轮廓最小割约束成立。 -/
theorem exact_decomposition_iff_bounded_profile_lift
    (depot : V) (required : V → ℕ)
    (x : V → V → ℕ)
    (hloop : ∀ v, x v v = 0)
    (service : V → ℚ) (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T) :
    (∃ routes :
        Fin (outFlow Finset.univ x depot) → LegalRoute depot,
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v,
        totalRouteFlow Finset.univ routes u v = x u v) ∧
      (∀ r,
        routeServiceIn (routes r) Finset.univ service ≤ T)) ↔
    (∃ y : VisitCopy depot required → VisitCopy depot required → ℕ,
      IsStructuralCopyLift depot required x y ∧
        AllBoundedProfileCuts depot required y service T) := by
  constructor
  · intro hroutes
    obtain ⟨y, hy⟩ :=
      (serviceCopyLift_iff_exact_decomposition
        depot required x hloop service T hservice hT).mpr hroutes
    exact ⟨y,
      (serviceCopyLift_iff_structural_bounded_profile_cuts
        depot required x y service T).mp hy⟩
  · rintro ⟨y, hstruct, hcuts⟩
    apply
      (serviceCopyLift_iff_exact_decomposition
        depot required x hloop service T hservice hT).mp
    refine ⟨y, ?_⟩
    exact
      (serviceCopyLift_iff_structural_bounded_profile_cuts
        depot required x y service T).mpr ⟨hstruct, hcuts⟩

end UAVProof.CopyProfileDecomposition

#print axioms UAVProof.CopyProfileDecomposition.profile_cuts_iff_bounded_profile_cuts
#print axioms UAVProof.CopyProfileDecomposition.serviceCopyLift_iff_structural_bounded_profile_cuts
#print axioms UAVProof.CopyProfileDecomposition.exact_decomposition_iff_bounded_profile_lift
