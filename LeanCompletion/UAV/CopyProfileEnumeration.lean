import LeanCompletion.UAV.CopyProfileExample
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

/-!
# 小规模轮廓最小割枚举器

固定副本流 y 和数量轮廓 q：
1. 枚举所有不含基地的副本子集；
2. 保留轮廓恰好为 q 的子集；
3. 枚举其出割值并取最小值；
4. 返回全部达到最小值的子集。

不可实现轮廓返回 none，区别于合法的 some 0。
可执行定义不使用 classical 或 noncomputable。
证明部分允许 classical。

这是指数规模枚举基准，不是高效分离算法，也不搜索副本流 y。
-/

namespace UAVProof.CopyProfileEnumeration

open VisitCopyLift CopyProfileService CopyProfileMinimum
open CopyProfileRealizability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- S 的实际轮廓与 q 不一致的物理节点集合。
用有限集合判空，避免计算时依赖函数相等的经典判定。 -/
def mismatchVertices
    (depot : V) (required : V → ℕ)
    (S : Finset (VisitCopy depot required))
    (q : V → ℕ) : Finset V :=
  Finset.univ.filter
    (fun v => visitProfile depot required S v ≠ q v)

theorem mismatchVertices_eq_empty_iff
    (depot : V) (required : V → ℕ)
    (S : Finset (VisitCopy depot required))
    (q : V → ℕ) :
    mismatchVertices depot required S q = ∅ ↔
      visitProfile depot required S = q := by
  classical
  constructor
  · intro h
    funext v
    by_contra hv
    have hm : v ∈ mismatchVertices depot required S q := by
      simp [mismatchVertices, hv]
    rw [h] at hm
    simp at hm
  · intro h
    simp [mismatchVertices, h]

/-- 全部不含基地、且精确实现 q 的副本子集。 -/
def candidateSubsets
    (depot : V) (required : V → ℕ) (q : V → ℕ) :
    Finset (Finset (VisitCopy depot required)) :=
  ((Finset.univ : Finset (VisitCopy depot required)).erase none).powerset.filter
    (fun S => mismatchVertices depot required S q = ∅)

theorem mem_candidateSubsets
    (depot : V) (required : V → ℕ) (q : V → ℕ)
    (S : Finset (VisitCopy depot required)) :
    S ∈ candidateSubsets depot required q ↔
      none ∉ S ∧ visitProfile depot required S = q := by
  classical
  rw [candidateSubsets, Finset.mem_filter, Finset.mem_powerset,
    mismatchVertices_eq_empty_iff]
  constructor
  · rintro ⟨hsub, hprofile⟩
    refine ⟨?_, hprofile⟩
    intro hn
    have hm := hsub hn
    exact (Finset.mem_erase.mp hm).1 rfl
  · rintro ⟨hdepot, hprofile⟩
    refine ⟨?_, hprofile⟩
    intro c hc
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro heq
    subst c
    exact hdepot hc

/-- 全部候选子集实际达到的出割值。 -/
def cutValues
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) : Finset ℕ :=
  (candidateSubsets depot required q).image
    (fun S => outCutFlow S y)

theorem mem_cutValues
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (k : ℕ) :
    k ∈ cutValues depot required y q ↔
      ∃ S : Finset (VisitCopy depot required),
        none ∉ S ∧
        visitProfile depot required S = q ∧
        outCutFlow S y = k := by
  classical
  constructor
  · intro hk
    obtain ⟨S, hS, hvalue⟩ := Finset.mem_image.mp hk
    obtain ⟨hdepot, hprofile⟩ :=
      (mem_candidateSubsets depot required q S).mp hS
    exact ⟨S, hdepot, hprofile, hvalue⟩
  · rintro ⟨S, hdepot, hprofile, hvalue⟩
    apply Finset.mem_image.mpr
    exact ⟨S,
      (mem_candidateSubsets depot required q S).mpr
        ⟨hdepot, hprofile⟩,
      hvalue⟩

theorem cutValues_nonempty_iff
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) :
    (cutValues depot required y q).Nonempty ↔
      RealizableProfile depot required q := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨S, hdepot, hprofile, _⟩ :=
      (mem_cutValues depot required y q k).mp hk
    exact ⟨S, hdepot, hprofile⟩
  · rintro ⟨S, hdepot, hprofile⟩
    refine ⟨outCutFlow S y, ?_⟩
    exact
      (mem_cutValues depot required y q (outCutFlow S y)).mpr
        ⟨S, hdepot, hprofile, rfl⟩

/-- 可执行最小割：没有实现子集时返回 none。 -/
def minimumValue?
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) : Option ℕ :=
  if h : (cutValues depot required y q).Nonempty then
    some ((cutValues depot required y q).min' h)
  else
    none

/-- 核心正确性：枚举最小值等于数学定义的 kappa。 -/
theorem minimumValue_eq_kappa
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ)
    (hq : RealizableProfile depot required q) :
    minimumValue? depot required y q =
      some (kappa depot required y q hq) := by
  classical
  have hne : (cutValues depot required y q).Nonempty :=
    (cutValues_nonempty_iff depot required y q).mpr hq
  rw [minimumValue?, dif_pos hne]
  congr 1
  apply le_antisymm
  · obtain ⟨S, hdepot, hprofile, hvalue⟩ :=
      kappa_attained depot required y q hq
    have hmem :
        kappa depot required y q hq ∈
          cutValues depot required y q :=
      (mem_cutValues depot required y q
        (kappa depot required y q hq)).mpr
          ⟨S, hdepot, hprofile, hvalue⟩
    exact Finset.min'_le _ _ hmem
  · have hmem :=
      Finset.min'_mem (cutValues depot required y q) hne
    obtain ⟨S, hdepot, hprofile, hvalue⟩ :=
      (mem_cutValues depot required y q
        ((cutValues depot required y q).min' hne)).mp hmem
    calc
      kappa depot required y q hq ≤ outCutFlow S y :=
        kappa_le_cut depot required y q hq S hdepot hprofile
      _ = (cutValues depot required y q).min' hne := hvalue

/-- none 精确表示轮廓不可实现。 -/
theorem minimumValue_eq_none_iff
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) :
    minimumValue? depot required y q = none ↔
      ¬ RealizableProfile depot required q := by
  constructor
  · intro hnone hq
    have hs := minimumValue_eq_kappa depot required y q hq
    rw [hnone] at hs
    cases hs
  · intro hnot
    have hempty : ¬ (cutValues depot required y q).Nonempty := by
      intro hne
      exact hnot
        ((cutValues_nonempty_iff depot required y q).mp hne)
    simp only [minimumValue?, dif_neg hempty]

/-- 返回 some k 时，有达到 k 的合法实现子集，
且所有合法实现子集的割值都不小于 k。 -/
theorem minimumValue_some_spec
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (k : ℕ)
    (hresult : minimumValue? depot required y q = some k) :
    ∃ S : Finset (VisitCopy depot required),
      none ∉ S ∧
      visitProfile depot required S = q ∧
      outCutFlow S y = k ∧
      ∀ R : Finset (VisitCopy depot required),
        none ∉ R →
        visitProfile depot required R = q →
        k ≤ outCutFlow R y := by
  classical
  have hne : (cutValues depot required y q).Nonempty := by
    by_contra hempty
    simp [minimumValue?, hempty] at hresult
  have hq : RealizableProfile depot required q :=
    (cutValues_nonempty_iff depot required y q).mp hne
  have hk : k = kappa depot required y q hq :=
    Option.some.inj
      (hresult.symm.trans
        (minimumValue_eq_kappa depot required y q hq))
  obtain ⟨S, hdepot, hprofile, hvalue⟩ :=
    kappa_attained depot required y q hq
  refine ⟨S, hdepot, hprofile, hvalue.trans hk.symm, ?_⟩
  intro R hR hprofileR
  rw [hk]
  exact kappa_le_cut depot required y q hq R hR hprofileR

/-- 可执行地返回全部最优见证子集，无须任意选择一个。 -/
def minimizingSubsets
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) :
    Finset (Finset (VisitCopy depot required)) :=
  match minimumValue? depot required y q with
  | none => ∅
  | some k =>
      (candidateSubsets depot required q).filter
        (fun S => outCutFlow S y = k)

theorem mem_minimizingSubsets
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (k : ℕ)
    (hresult : minimumValue? depot required y q = some k)
    (S : Finset (VisitCopy depot required)) :
    S ∈ minimizingSubsets depot required y q ↔
      none ∉ S ∧
      visitProfile depot required S = q ∧
      outCutFlow S y = k := by
  simp only [minimizingSubsets, hresult, Finset.mem_filter,
    mem_candidateSubsets, and_assoc]

theorem minimizingSubsets_nonempty
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ)
    (hq : RealizableProfile depot required q) :
    (minimizingSubsets depot required y q).Nonempty := by
  have hresult := minimumValue_eq_kappa depot required y q hq
  obtain ⟨S, hdepot, hprofile, hvalue, _⟩ :=
    minimumValue_some_spec depot required y q
      (kappa depot required y q hq) hresult
  refine ⟨S, ?_⟩
  exact
    (mem_minimizingSubsets depot required y q
      (kappa depot required y q hq) hresult S).mpr
        ⟨hdepot, hprofile, hvalue⟩

namespace FourNode

open FixedFlowObstruction CopyLiftObstruction.FourNode
open CopyProfileExample

/-- 已有理论值与新枚举器接口连接。 -/
theorem enumerated_badProfile_eq_one :
    minimumValue? (0 : Node) required witnessFlow badProfile =
      some 1 := by
  rw [minimumValue_eq_kappa
    (0 : Node) required witnessFlow badProfile badProfile_realizable,
    badProfile_kappa_eq_one]

/-- 基地计数非零的轮廓不可实现。 -/
theorem enumerated_invalidProfile_eq_none :
    minimumValue? (0 : Node) required witnessFlow
      (fun _ : Node => 1) = none := by
  apply
    (minimumValue_eq_none_iff
      (0 : Node) required witnessFlow (fun _ : Node => 1)).mpr
  intro hq
  have hz :=
    (bounds_of_realizableProfile
      (0 : Node) required (fun _ : Node => 1) hq).1
  norm_num at hz

-- 预期：some 1
#eval minimumValue? (0 : Node) required witnessFlow badProfile

-- 预期：some 0。零轮廓由空子集实现，不能返回 none。
#eval minimumValue? (0 : Node) required witnessFlow
  (fun _ : Node => 0)

-- 预期：none。基地计数不能为 1。
#eval minimumValue? (0 : Node) required witnessFlow
  (fun _ : Node => 1)

end FourNode
end UAVProof.CopyProfileEnumeration

#print axioms UAVProof.CopyProfileEnumeration.mem_candidateSubsets
#print axioms UAVProof.CopyProfileEnumeration.cutValues_nonempty_iff
#print axioms UAVProof.CopyProfileEnumeration.minimumValue_eq_kappa
#print axioms UAVProof.CopyProfileEnumeration.minimumValue_eq_none_iff
#print axioms UAVProof.CopyProfileEnumeration.minimumValue_some_spec
#print axioms UAVProof.CopyProfileEnumeration.mem_minimizingSubsets
#print axioms UAVProof.CopyProfileEnumeration.minimizingSubsets_nonempty
#print axioms UAVProof.CopyProfileEnumeration.FourNode.enumerated_badProfile_eq_one
#print axioms UAVProof.CopyProfileEnumeration.FourNode.enumerated_invalidProfile_eq_none
