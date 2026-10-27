import LeanCompletion.UAV.CopyProfileMinimum
import Mathlib.Data.Finset.Card

/-!
# 可实现轮廓的精确取值范围

主定理：
  RealizableProfile depot required q ↔
    q depot = 0 ∧ ∀ v, v ≠ depot → q v ≤ required v

构造：在每个非基地节点的副本中选取编号小于 q(v) 的副本。

2026-10-27 用户报告的本地验证及证据范围见
仓库 docs/COPY_PROFILE_DECOMPOSITION_STATUS.md。
-/

namespace UAVProof.CopyProfileRealizability

open VisitCopyLift CopyFiberCompression
open CopyProfileService CopyProfileMinimum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 副本的局部编号；基地编号设为零，仅用于统一定义。 -/
def copyIndex (depot : V) (required : V → ℕ) :
    VisitCopy depot required → ℕ
  | none => 0
  | some a => a.2.val

/-- 投影到 v 且编号小于 n 的全部副本。 -/
def copiesBelow
    (depot : V) (required : V → ℕ)
    (v : V) (n : ℕ) : Finset (VisitCopy depot required) :=
  Finset.univ.filter (fun c =>
    project depot required c = v ∧
      copyIndex depot required c < n)

/-- 非基地节点的前 n 个副本恰有 n 个。 -/
theorem copiesBelow_card
    (depot : V) (required : V → ℕ)
    (v : V) (hv : v ≠ depot)
    (n : ℕ) (hn : n ≤ required v) :
    (copiesBelow depot required v n).card = n := by
  classical
  let f : Fin n → VisitCopy depot required :=
    fun i =>
      some ⟨⟨v, hv⟩, ⟨i.val, lt_of_lt_of_le i.isLt hn⟩⟩

  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have h := congrArg (copyIndex depot required) hij
    exact h

  have hset :
      copiesBelow depot required v n = Finset.univ.image f := by
    ext c
    constructor
    · intro hc
      obtain ⟨hp, hi⟩ := (Finset.mem_filter.mp hc).2
      cases c with
      | none =>
          have h : depot = v := hp
          exact (hv h.symm).elim
      | some a =>
          rcases a with ⟨⟨w, hw⟩, i⟩
          change w = v at hp
          subst w
          refine Finset.mem_image.mpr
            ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
          rfl
    · intro hc
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, rfl, i.isLt⟩

  rw [hset]
  simpa using
    (Finset.card_image_of_injective
      (Finset.univ : Finset (Fin n)) hf)

/-- 任意子集在非基地节点 v 处选取的副本数不超过需求。 -/
theorem visitProfile_le_required
    (depot : V) (required : V → ℕ)
    (S : Finset (VisitCopy depot required))
    (v : V) (hv : v ≠ depot) :
    visitProfile depot required S v ≤ required v := by
  classical
  have hsub :
      S.filter (fun c => project depot required c = v) ⊆
        copiesBelow depot required v (required v) := by
    intro c hc
    have hp := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hp, ?_⟩
    cases c with
    | none =>
        have h : depot = v := hp
        exact (hv h.symm).elim
    | some a =>
        rcases a with ⟨⟨w, hw⟩, i⟩
        change w = v at hp
        subst w
        exact i.isLt

  change
    (S.filter (fun c => project depot required c = v)).card ≤
      required v
  calc
    (S.filter (fun c => project depot required c = v)).card ≤
        (copiesBelow depot required v (required v)).card :=
      Finset.card_le_card hsub
    _ = required v :=
      copiesBelow_card depot required v hv (required v) le_rfl

/-- 按轮廓 q 选取每个任务节点的前 q(v) 个副本。 -/
def canonicalSet
    (depot : V) (required : V → ℕ) (q : V → ℕ) :
    Finset (VisitCopy depot required) :=
  Finset.univ.filter (fun c =>
    c ≠ none ∧
      copyIndex depot required c < q (project depot required c))

theorem canonicalSet_depot_free
    (depot : V) (required : V → ℕ) (q : V → ℕ) :
    (none : VisitCopy depot required) ∉
      canonicalSet depot required q := by
  simp [canonicalSet]

/-- 在非基地节点处，规范集合的纤维就是对应的编号前缀。 -/
theorem canonicalSet_fibre
    (depot : V) (required : V → ℕ) (q : V → ℕ)
    (v : V) (hv : v ≠ depot) :
    (canonicalSet depot required q).filter
        (fun c => project depot required c = v) =
      copiesBelow depot required v (q v) := by
  classical
  ext c
  simp only [canonicalSet, copiesBelow, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, hi⟩, hp⟩
    refine ⟨hp, ?_⟩
    rw [hp] at hi
    exact hi
  · rintro ⟨hp, hi⟩
    refine ⟨⟨?_, ?_⟩, hp⟩
    · intro hc
      subst c
      have h : depot = v := hp
      exact hv h.symm
    · rw [hp]
      exact hi

/-- 满足整数范围约束时，规范集合精确实现 q。 -/
theorem canonicalSet_profile
    (depot : V) (required : V → ℕ) (q : V → ℕ)
    (hzero : q depot = 0)
    (hbound : ∀ v, v ≠ depot → q v ≤ required v) :
    visitProfile depot required (canonicalSet depot required q) = q := by
  classical
  funext v
  by_cases hv : v = depot
  · subst v
    rw [visitProfile_depot_eq_zero depot required
      (canonicalSet depot required q)
      (canonicalSet_depot_free depot required q)]
    exact hzero.symm
  · change
      ((canonicalSet depot required q).filter
        (fun c => project depot required c = v)).card = q v
    rw [canonicalSet_fibre depot required q v hv]
    exact copiesBelow_card depot required v hv (q v) (hbound v hv)

/-- 可实现性蕴含基地计数为零及逐点需求上界。 -/
theorem bounds_of_realizableProfile
    (depot : V) (required : V → ℕ) (q : V → ℕ)
    (hq : RealizableProfile depot required q) :
    q depot = 0 ∧ ∀ v, v ≠ depot → q v ≤ required v := by
  obtain ⟨S, hS, hprofile⟩ := hq
  constructor
  · rw [← hprofile]
    exact visitProfile_depot_eq_zero depot required S hS
  · intro v hv
    rw [← hprofile]
    exact visitProfile_le_required depot required S v hv

/-- 逐点整数范围约束足以构造实现子集。 -/
theorem realizableProfile_of_bounds
    (depot : V) (required : V → ℕ) (q : V → ℕ)
    (hzero : q depot = 0)
    (hbound : ∀ v, v ≠ depot → q v ≤ required v) :
    RealizableProfile depot required q := by
  exact ⟨canonicalSet depot required q,
    canonicalSet_depot_free depot required q,
    canonicalSet_profile depot required q hzero hbound⟩

/-- 主定理：可实现轮廓恰为明确的有限整数盒子。 -/
theorem realizableProfile_iff_bounds
    (depot : V) (required : V → ℕ) (q : V → ℕ) :
    RealizableProfile depot required q ↔
      q depot = 0 ∧ ∀ v, v ≠ depot → q v ≤ required v := by
  constructor
  · exact bounds_of_realizableProfile depot required q
  · rintro ⟨hzero, hbound⟩
    exact realizableProfile_of_bounds depot required q hzero hbound

end UAVProof.CopyProfileRealizability

#print axioms UAVProof.CopyProfileRealizability.copiesBelow_card
#print axioms UAVProof.CopyProfileRealizability.visitProfile_le_required
#print axioms UAVProof.CopyProfileRealizability.canonicalSet_profile
#print axioms UAVProof.CopyProfileRealizability.realizableProfile_iff_bounds
