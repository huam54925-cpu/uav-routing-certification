import LeanCompletion.UAV.CopyProfileChecker
import Mathlib.Data.Finset.Sort
import Mathlib.Data.String.Basic
import LeanCompletion.UAV.CopyProfileChecker

/-!
# 四节点轮廓割报告与预算 4 的内核认证

报告枚举全部失败轮廓及其全部最优子集。
预算 4 的检查结果使用 decide +kernel 证明，
再通过已有检查器正确性定理接回服务提升和精确分解。

这里的预算仍是服务费用预算，不含飞行费用。
-/

namespace UAVProof.CopyProfileReport

open ResourceCuts VisitCopyLift
open CopyProfileService CopyProfileMinimum
open CopyProfileRealizability CopyProfileDecomposition
open CopyProfileEnumeration CopyProfileChecker
open FixedFlowObstruction CopyLiftObstruction.FourNode

/-- 面向阅读的单条违规报告。 -/
structure CutReport where
  /-- 按物理节点 0、1、2、3 排列。 -/
  counts : List ℕ
  serviceWork : ℚ
  budget : ℚ
  requiredExits : ℤ
  cutValue : ℕ
  selectedCopies : Finset String
  deriving DecidableEq

/-- 副本显示标签；任务副本编号从零开始。 -/
def copyLabel : Copy → String
  | none => "depot"
  | some a => s!"v{reprStr a.1.val}#{a.2.val}"

/-- 把一个轮廓及其实现子集转成显示记录。
只有在 S 为最优子集时，cutValue 才同时是轮廓最小割值。 -/
def makeReport
    (T : ℚ) (q : Node → ℕ) (S : Finset Copy) : CutReport where
  counts := [q 0, q 1, q 2, q 3]
  serviceWork := profileWork service q
  budget := T
  requiredExits := Int.ceil (profileWork service q / T)
  cutValue := outCutFlow S witnessFlow
  selectedCopies := S.image copyLabel

/-- 所有失败轮廓及其所有最优实现子集的报告。 -/
def reportRows (T : ℚ) : Finset CutReport :=
  (violatingProfiles
    (0 : Node) required witnessFlow service T).biUnion
      (fun p =>
        (minimizingSubsets
          (0 : Node) required witnessFlow
          (decodeProfile (0 : Node) required p)).image
            (fun S =>
              makeReport T
                (decodeProfile (0 : Node) required p) S))

/-- 报告使用最优子集时，显示的割值确实等于 kappa。 -/
theorem report_cutValue_eq_kappa
    (T : ℚ)
    (p : BoundedProfile (0 : Node) required)
    (S : Finset Copy)
    (hS : S ∈ minimizingSubsets
      (0 : Node) required witnessFlow
      (decodeProfile (0 : Node) required p)) :
    (makeReport T
      (decodeProfile (0 : Node) required p) S).cutValue =
    kappa (0 : Node) required witnessFlow
      (decodeProfile (0 : Node) required p)
      (decodedProfile_realizable (0 : Node) required p) := by
  have hresult :=
    minimumValue_eq_kappa
      (0 : Node) required witnessFlow
      (decodeProfile (0 : Node) required p)
      (decodedProfile_realizable (0 : Node) required p)
  have hspec :=
    (mem_minimizingSubsets
      (0 : Node) required witnessFlow
      (decodeProfile (0 : Node) required p)
      (kappa (0 : Node) required witnessFlow
        (decodeProfile (0 : Node) required p)
        (decodedProfile_realizable (0 : Node) required p))
      hresult S).mp hS
  exact hspec.2.2

/-- 输出的每条记录都严格违反容量割。 -/
theorem reportRows_sound
    (T : ℚ) (row : CutReport)
    (hrow : row ∈ reportRows T) :
    (row.cutValue : ℤ) < row.requiredExits := by
  classical
  obtain ⟨p, hp, hrow⟩ := Finset.mem_biUnion.mp hrow
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hrow

  have hfalse := (Finset.mem_filter.mp hp).2

  have hnot :
      ¬ Int.ceil
          (profileWork service
            (decodeProfile (0 : Node) required p) / T) ≤
        (kappa (0 : Node) required witnessFlow
          (decodeProfile (0 : Node) required p)
          (decodedProfile_realizable (0 : Node) required p) : ℤ) := by
    intro hle
    have htrue :=
      (profilePasses_eq_true_iff
        (0 : Node) required witnessFlow service T p).mpr hle
    rw [htrue] at hfalse
    cases hfalse

  have hvalue := report_cutValue_eq_kappa T p S hS
  change
    ((makeReport T
      (decodeProfile (0 : Node) required p) S).cutValue : ℤ) <
      Int.ceil
        (profileWork service
          (decodeProfile (0 : Node) required p) / T)
  rw [hvalue]
  exact lt_of_not_ge hnot

/-!
预算 4 的肯定结果。

这一条真正由内核核验布尔计算，不使用 native_decide。
资源上限只作用于这一条有限计算证明。
-/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem witness_check_four :
    checkAll
      (0 : Node) required witnessFlow service (4 : ℚ) = true := by
  decide +kernel

/-- 通过检查对应全部有界轮廓容量割。 -/
theorem witness_all_bounded_cuts_four :
    AllBoundedProfileCuts
      (0 : Node) required witnessFlow service (4 : ℚ) := by
  exact
    (checkAll_eq_true_iff
      (0 : Node) required witnessFlow service (4 : ℚ)).mp
        witness_check_four

/-- 结合已经证明的结构条件，得到预算 4 的完整服务提升。 -/
theorem witness_service_lift_four :
    IsServiceCopyLift
      (0 : Node) required fixedFlow service (4 : ℚ) witnessFlow := by
  exact
    (serviceCopyLift_iff_structural_check
      (0 : Node) required fixedFlow witnessFlow
      service (4 : ℚ)).mpr
        ⟨witness_is_structural, witness_check_four⟩

/-- 预算 4 时，固定物理流具有预算可行的精确路线分解。 -/
theorem exact_decomposition_four :
    ∃ routes :
        Fin (outFlow Finset.univ fixedFlow (0 : Node)) →
          LegalRoute (0 : Node),
      (∀ v, v ≠ (0 : Node) →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v,
        totalRouteFlow Finset.univ routes u v = fixedFlow u v) ∧
      (∀ r,
        routeServiceIn (routes r) Finset.univ service ≤ (4 : ℚ)) := by
  apply
    (serviceCopyLift_iff_exact_decomposition
      (0 : Node) required fixedFlow
      fixed_flow_aggregate_conditions.noDiagonal
      service (4 : ℚ) service_nonneg (by norm_num)).mp
  exact ⟨witnessFlow, witness_service_lift_four⟩

/-- 预算 4 时没有失败轮廓，因此没有违规报告。 -/
theorem reportRows_four_eq_empty :
    reportRows (4 : ℚ) = ∅ := by
  have hempty :
      violatingProfiles
        (0 : Node) required witnessFlow service (4 : ℚ) = ∅ :=
    of_decide_eq_true witness_check_four
  simp [reportRows, hempty]

/-- 将报告转换为可直接打印的文本。
副本集合先排序为列表，避免依赖 Finset 的通用打印实例。 -/
def renderReport (row : CutReport) : String :=
  let copies : List String :=
    row.selectedCopies.sort (fun a b => a ≤ b)
  s!"counts={reprStr row.counts}; " ++
    s!"serviceWork={reprStr row.serviceWork}; " ++
    s!"budget={reprStr row.budget}; " ++
    s!"requiredExits={reprStr row.requiredExits}; " ++
    s!"cutValue={reprStr row.cutValue}; " ++
    s!"selectedCopies={reprStr copies}"

/-- 将报告文本集合排序成列表，供 #eval 显示。 -/
def reportLines (T : ℚ) : List String :=
  ((reportRows T).image renderReport).sort (fun a b => a ≤ b)

-- 原预算：显示违规轮廓及其最优子集。
#eval reportLines capacity

-- 放宽到 4：预期输出 []。
#eval reportLines (4 : ℚ)

-- 同时检查原始报告集合的记录数，预期输出 0。
#eval (reportRows (4 : ℚ)).card

end UAVProof.CopyProfileReport

#print axioms UAVProof.CopyProfileReport.report_cutValue_eq_kappa
#print axioms UAVProof.CopyProfileReport.reportRows_sound
#print axioms UAVProof.CopyProfileReport.witness_check_four
#print axioms UAVProof.CopyProfileReport.witness_all_bounded_cuts_four
#print axioms UAVProof.CopyProfileReport.witness_service_lift_four
#print axioms UAVProof.CopyProfileReport.exact_decomposition_four
#print axioms UAVProof.CopyProfileReport.reportRows_four_eq_empty
