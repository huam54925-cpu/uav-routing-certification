import LeanCompletion.UAV.TreeBudgetBinaryCodec
import LeanCompletion.UAV.TreeBudgetParentArray

/-! A checked executable binary-input frontend. Invalid shapes, root/parent
indices, cycles and nonpositive denominators are rejected. Proof-only tree
interpretation is kept out of the decoder's executable data. -/
namespace UAVProof.TreeBudgetBinaryInput
open TreeBudgetBinaryCodec TreeBudgetParentArray

structure Input where
  n : ℕ
  parents : ParentArray n
  valid : Valid parents
  H : Vector ℕ n
  numerators : Vector ℤ n
  denominators : Vector ℕ n
  budgetNumerator : ℤ
  budgetDenominator : ℕ
  positive : ∀ v : Fin n, 0 < denominators[v]
  budgetPositive : 0 < budgetDenominator

def decodeRaw (I : RawInput) : Option Input :=
  if hs : Shape I then
    match decodeParents I.root I.parents with
    | none => none
    | some P =>
      if hp : denominatorsPositiveB I.denominators I.budgetDenominator = true then
        let hpos := (denominatorsPositiveB_eq_true _ _).mp hp
        some {
          n := I.parents.length
          parents := P.val
          valid := P.property
          H := ⟨I.multiplicities.toArray, by simpa only [List.size_toArray] using hs.2.1.trans hs.1.symm⟩
          numerators := ⟨I.numerators.toArray, by simpa only [List.size_toArray] using hs.2.2.1.trans hs.1.symm⟩
          denominators := ⟨I.denominators.toArray, by simpa only [List.size_toArray] using hs.2.2.2.trans hs.1.symm⟩
          budgetNumerator := I.budgetNumerator
          budgetDenominator := I.budgetDenominator
          positive := by
            intro v
            have hlen : I.denominators.length = I.parents.length := hs.2.2.2.trans hs.1.symm
            have hv : v.val < I.denominators.length := by rw [hlen]; exact v.isLt
            have hx : 0 < I.denominators[v.val] := hpos.2 _ (List.getElem_mem hv)
            simpa using hx
          budgetPositive := hpos.1 }
      else none
  else none

def parse (bits : Bits) : Option Input := (parseInput bits).bind decodeRaw

theorem parse_encode (I : RawInput) (hs : Shape I) :
    parse (encodeInput I) = decodeRaw I := by
  simp [parse, parseInput_encode I hs]

theorem decodeRaw_shape (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    Shape I := by
  by_contra hs
  simp [decodeRaw, hs] at h

theorem decodeRaw_fields (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    J.n = I.n ∧ J.parents.root.val = I.root ∧
      J.H.toList = I.multiplicities ∧ J.numerators.toList = I.numerators ∧
      J.denominators.toList = I.denominators ∧
      J.budgetNumerator = I.budgetNumerator ∧ J.budgetDenominator = I.budgetDenominator := by
  unfold decodeRaw at h
  split at h
  · rename_i hs
    split at h
    · cases h
    · rename_i P he
      have hroot := (decodeParents_spec I.root I.parents P he).1
      split at h
      · cases Option.some.inj h
        refine ⟨hs.1, hroot, ?_, ?_, ?_, rfl, rfl⟩ <;> simp
      · cases h
  · cases h

theorem decodeRaw_invalid_shape (I : RawInput) (h : ¬ Shape I) : decodeRaw I = none := by
  simp [decodeRaw, h]

theorem decodeRaw_parent_values (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    (J.parents.parents.toList.map Fin.val) = I.parents := by
  unfold decodeRaw at h
  split at h
  · split at h
    · cases h
    · rename_i P he
      have hp := (decodeParents_spec I.root I.parents P he).2
      split at h
      · cases Option.some.inj h
        apply List.ext_getElem
        · simp
        · intro i hi hj
          simpa using hp ⟨i, hj⟩
      · cases h
  · cases h

theorem decodeRaw_invalid_parent (I : RawInput)
    (h : decodeParents I.root I.parents = none) : decodeRaw I = none := by
  simp [decodeRaw, h]

theorem decodeRaw_zero_budget_denominator (I : RawInput) (h : I.budgetDenominator = 0) :
    decodeRaw I = none := by
  simp [decodeRaw, denominatorsPositiveB, h]
  split <;> simp

theorem parse_trailing_rejected (I : RawInput) (hs : Shape I) (tail : Bits)
    (ht : tail ≠ []) : parse (encodeInput I ++ tail) = none := by
  simp [parse, parseInput_rejects_trailing I hs tail ht]

end UAVProof.TreeBudgetBinaryInput
