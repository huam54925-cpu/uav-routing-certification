import LeanCompletion.UAV.CopyProfileEnumeration

/-!
# 固定副本流的全部有界轮廓割检查器

* 用有限类型枚举全部有界轮廓；
* 对每个轮廓调用精确最小割枚举器；
* violatingProfiles 返回全部失败轮廓；
* checkAll 返回全部容量割是否通过；
* 证明 checkAll = true ↔ AllBoundedProfileCuts；
* 失败轮廓具有可计算的最优子集见证。

这里只检查容量割。完整服务提升还要求 IsStructuralCopyLift。
不搜索副本流，也不宣称多项式复杂度。
-/

namespace UAVProof.CopyProfileChecker

open VisitCopyLift CopyLiftObstruction
open CopyProfileService CopyProfileMinimum
open CopyProfileRealizability CopyProfileDecomposition
open CopyProfileEnumeration

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 非基地节点的计数分别取 0,...,required v。
基地计数由解码固定为零。 -/
abbrev BoundedProfile (depot : V) (required : V → ℕ) :=
  (v : {v : V // v ≠ depot}) → Fin (required v.val + 1)

/-- 把有限编码解码为物理节点上的自然数轮廓。 -/
def decodeProfile
    (depot : V) (required : V → ℕ)
    (p : BoundedProfile depot required) : V → ℕ :=
  fun v =>
    if h : v = depot then
      0
    else
      (p ⟨v, h⟩).val

theorem decodeProfile_depot
    (depot : V) (required : V → ℕ)
    (p : BoundedProfile depot required) :
    decodeProfile depot required p depot = 0 := by
  simp [decodeProfile]

theorem decodeProfile_bound
    (depot : V) (required : V → ℕ)
    (p : BoundedProfile depot required)
    (v : V) (hv : v ≠ depot) :
    decodeProfile depot required p v ≤ required v := by
  simpa [decodeProfile, hv] using
    (Nat.le_of_lt_succ (p ⟨v, hv⟩).isLt)

theorem decodedProfile_realizable
    (depot : V) (required : V → ℕ)
    (p : BoundedProfile depot required) :
    RealizableProfile depot required
      (decodeProfile depot required p) := by
  exact realizableProfile_of_bounds
    depot required (decodeProfile depot required p)
    (decodeProfile_depot depot required p)
    (decodeProfile_bound depot required p)

/-- 将满足范围约束的轮廓编码为有限类型的元素。 -/
def encodeProfile
    (depot : V) (required : V → ℕ)
    (q : V → ℕ)
    (hbound : ∀ v, v ≠ depot → q v ≤ required v) :
    BoundedProfile depot required :=
  fun v =>
    ⟨q v.val, Nat.lt_succ_of_le (hbound v.val v.property)⟩

/-- 每个有界轮廓都被有限枚举覆盖。 -/
theorem decode_encodeProfile
    (depot : V) (required : V → ℕ)
    (q : V → ℕ)
    (hzero : q depot = 0)
    (hbound : ∀ v, v ≠ depot → q v ≤ required v) :
    decodeProfile depot required
      (encodeProfile depot required q hbound) = q := by
  funext v
  by_cases hv : v = depot
  · subst v
    simp [decodeProfile, hzero]
  · simp [decodeProfile, encodeProfile, hv]

/-- 检查单个有界轮廓。
none 分支保守返回 false；正确性证明保证该分支不会发生。 -/
def profilePasses
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ)
    (p : BoundedProfile depot required) : Bool :=
  match minimumValue? depot required y
      (decodeProfile depot required p) with
  | none => false
  | some k =>
      decide
        (Int.ceil
          (profileWork service (decodeProfile depot required p) / T)
            ≤ (k : ℤ))

/-- 单轮廓布尔检查与数学最小割不等式等价。 -/
theorem profilePasses_eq_true_iff
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ)
    (p : BoundedProfile depot required) :
    profilePasses depot required y service T p = true ↔
      Int.ceil
        (profileWork service (decodeProfile depot required p) / T) ≤
      (kappa depot required y
        (decodeProfile depot required p)
        (decodedProfile_realizable depot required p) : ℤ) := by
  unfold profilePasses
  rw [minimumValue_eq_kappa
    depot required y
    (decodeProfile depot required p)
    (decodedProfile_realizable depot required p)]
  simp

/-- 全部失败轮廓的有限集合。 -/
def violatingProfiles
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    Finset (BoundedProfile depot required) :=
  Finset.univ.filter
    (fun p => profilePasses depot required y service T p = false)

/-- 全部轮廓容量割是否通过。 -/
def checkAll
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) : Bool :=
  decide (violatingProfiles depot required y service T = ∅)

/-- 主定理：布尔检查精确对应全部有界轮廓割。 -/
theorem checkAll_eq_true_iff
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    checkAll depot required y service T = true ↔
      AllBoundedProfileCuts depot required y service T := by
  classical
  constructor
  · intro hcheck
    have hempty :
        violatingProfiles depot required y service T = ∅ :=
      of_decide_eq_true hcheck
    intro q hzero hbound
    let p : BoundedProfile depot required :=
      encodeProfile depot required q hbound
    have hp : decodeProfile depot required p = q :=
      decode_encodeProfile depot required q hzero hbound
    have hpass :
        profilePasses depot required y service T p = true := by
      cases h : profilePasses depot required y service T p with
      | false =>
          have hm :
              p ∈ violatingProfiles depot required y service T := by
            simp [violatingProfiles, h]
          rw [hempty] at hm
          simp at hm
      | true =>
          rfl
    have hle :=
      (profilePasses_eq_true_iff
        depot required y service T p).mp hpass
    simpa only [hp] using hle
  · intro hcuts
    have hempty :
        violatingProfiles depot required y service T = ∅ := by
      ext p
      constructor
      · intro hp
        have hfalse :=
          (Finset.mem_filter.mp hp).2
        have hle :=
          hcuts
            (decodeProfile depot required p)
            (decodeProfile_depot depot required p)
            (decodeProfile_bound depot required p)
        have htrue :
            profilePasses depot required y service T p = true :=
          (profilePasses_eq_true_iff
            depot required y service T p).mpr hle
        rw [htrue] at hfalse
        cases hfalse
      · intro hp
        simp at hp
    simp [checkAll, hempty]

/-- 检查失败当且仅当返回的失败轮廓集合非空。 -/
theorem checkAll_eq_false_iff
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    checkAll depot required y service T = false ↔
      (violatingProfiles depot required y service T).Nonempty := by
  simp [checkAll, Finset.nonempty_iff_ne_empty]

/-- 每个失败轮廓都拥有一个可计算最优子集中的违规见证。 -/
theorem violatingProfile_has_counterexample
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ)
    (p : BoundedProfile depot required)
    (hp : p ∈ violatingProfiles depot required y service T) :
    ∃ S : Finset (VisitCopy depot required),
      S ∈ minimizingSubsets depot required y
        (decodeProfile depot required p) ∧
      none ∉ S ∧
      visitProfile depot required S =
        decodeProfile depot required p ∧
      (outCutFlow S y : ℤ) <
        Int.ceil
          (profileWork service (decodeProfile depot required p) / T) := by
  classical
  have hfalse := (Finset.mem_filter.mp hp).2
  have hnot :
      ¬ Int.ceil
          (profileWork service (decodeProfile depot required p) / T) ≤
        (kappa depot required y
          (decodeProfile depot required p)
          (decodedProfile_realizable depot required p) : ℤ) := by
    intro hle
    have htrue :=
      (profilePasses_eq_true_iff
        depot required y service T p).mpr hle
    rw [htrue] at hfalse
    cases hfalse

  have hresult :=
    minimumValue_eq_kappa
      depot required y
      (decodeProfile depot required p)
      (decodedProfile_realizable depot required p)

  obtain ⟨S, hS⟩ :=
    minimizingSubsets_nonempty
      depot required y
      (decodeProfile depot required p)
      (decodedProfile_realizable depot required p)

  obtain ⟨hdepot, hprofile, hvalue⟩ :=
    (mem_minimizingSubsets
      depot required y
      (decodeProfile depot required p)
      (kappa depot required y
        (decodeProfile depot required p)
        (decodedProfile_realizable depot required p))
      hresult S).mp hS

  refine ⟨S, hS, hdepot, hprofile, ?_⟩
  rw [hvalue]
  exact lt_of_not_ge hnot

/-- 接回服务提升接口：容量检查通过还须配合结构条件。 -/
theorem serviceCopyLift_iff_structural_check
    (depot : V) (required : V → ℕ)
    (x : V → V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    IsServiceCopyLift depot required x service T y ↔
      IsStructuralCopyLift depot required x y ∧
        checkAll depot required y service T = true := by
  rw [checkAll_eq_true_iff]
  exact serviceCopyLift_iff_structural_bounded_profile_cuts
    depot required x y service T

namespace FourNode

open FixedFlowObstruction CopyLiftObstruction.FourNode
open CopyProfileExample

/-- 既有预算 3 的结构提升不能通过全部容量割检查。 -/
theorem witness_check_not_true :
    ¬ checkAll
      (0 : Node) required witnessFlow service capacity = true := by
  intro h
  exact witness_not_all_bounded_profile_cuts
    ((checkAll_eq_true_iff
      (0 : Node) required witnessFlow service capacity).mp h)

/-- 将否定 true 转成明确的 false 结果。 -/
theorem witness_check_eq_false :
    checkAll
      (0 : Node) required witnessFlow service capacity = false := by
  cases h : checkAll
      (0 : Node) required witnessFlow service capacity with
  | false =>
      rfl
  | true =>
      exact (witness_check_not_true h).elim

/-- 失败轮廓确实存在，不只是布尔结果为 false。 -/
theorem witness_violatingProfiles_nonempty :
    (violatingProfiles
      (0 : Node) required witnessFlow service capacity).Nonempty := by
  exact
    (checkAll_eq_false_iff
      (0 : Node) required witnessFlow service capacity).mp
        witness_check_eq_false

-- 预期：false。原服务预算为 3。
#eval checkAll
  (0 : Node) required witnessFlow service capacity

-- 预期：true。把同一提升的服务预算放宽到 4。
-- 这是运行检查；不把这条 #eval 本身当成 Lean 定理。
#eval checkAll
  (0 : Node) required witnessFlow service (4 : ℚ)

end FourNode
end UAVProof.CopyProfileChecker

#print axioms UAVProof.CopyProfileChecker.decode_encodeProfile
#print axioms UAVProof.CopyProfileChecker.profilePasses_eq_true_iff
#print axioms UAVProof.CopyProfileChecker.checkAll_eq_true_iff
#print axioms UAVProof.CopyProfileChecker.checkAll_eq_false_iff
#print axioms UAVProof.CopyProfileChecker.violatingProfile_has_counterexample
#print axioms UAVProof.CopyProfileChecker.serviceCopyLift_iff_structural_check
#print axioms UAVProof.CopyProfileChecker.FourNode.witness_check_eq_false
#print axioms UAVProof.CopyProfileChecker.FourNode.witness_violatingProfiles_nonempty
