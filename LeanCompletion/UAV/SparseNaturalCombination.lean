import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-! Finite nonnegative integer combinations. This proof layer does not enumerate
the generators at runtime and makes no claim about finding a sparse solution. -/
namespace UAVProof.SparseNaturalCombination

open Finset
variable {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D]

def support (z : A → ℕ) : Finset A := univ.filter (fun p => 0 < z p)

@[simp] theorem mem_support (z : A → ℕ) (p : A) : p ∈ support z ↔ 0 < z p := by
  simp [support]

def Feasible (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ) : Prop :=
  ∀ v, ∑ p, z p * a p v = b v

theorem exists_minimizer {X : Type*} (P : X → Prop) (f : X → ℕ)
    (h : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → f x ≤ f y := by
  classical
  have hex : ∃ n, ∃ x, P x ∧ f x = n := by obtain ⟨x, hx⟩ := h; exact ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, he⟩ := Nat.find_spec hex
  exact ⟨x, hx, fun y hy => he ▸ Nat.find_min' hex ⟨y, hy, rfl⟩⟩

/-- Exchange equal sums of disjoint supported subsets, eliminating a minimum
multiplicity. All conservation equations are proved before cancelling in ℕ. -/
theorem exchange (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z) (S U : Finset A)
    (hS : S ⊆ support z) (hU : U ⊆ support z) (hdis : Disjoint S U)
    (hne : S.Nonempty) (he : ∀ v, ∑ p ∈ S, a p v = ∑ p ∈ U, a p v) :
    ∃ z', Feasible a b z' ∧ (support z').card < (support z).card := by
  classical
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image z hne
  let δ := z p
  have hδ : 0 < δ := (mem_support z p).mp (hS hp)
  let z' : A → ℕ := fun q => if q ∈ S then z q - δ else if q ∈ U then z q + δ else z q
  have hid (q : A) : z' q + (if q ∈ S then δ else 0) =
      z q + (if q ∈ U then δ else 0) := by
    by_cases hs : q ∈ S
    · have hu : q ∉ U := fun hu => Finset.disjoint_left.mp hdis hs hu
      have hd := hmin q hs
      simp only [z', hs, hu, if_true, if_false, add_zero]
      omega
    · by_cases hu : q ∈ U <;> simp [z', hs, hu]
  have hf : Feasible a b z' := by
    intro v
    have hs := congrArg (fun f : A → ℕ => ∑ q, f q * a q v) (funext hid)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul] at hs
    simp only [← Finset.sum_filter, Finset.filter_univ_mem, ← Finset.mul_sum] at hs
    rw [he v, hz v] at hs
    omega
  have hsub : support z' ⊆ support z := by
    intro q hq
    by_cases hs : q ∈ S
    · exact hS hs
    · by_cases hu : q ∈ U
      · exact hU hu
      · simpa [support, z', hs, hu] using hq
  have hnot : p ∉ support z' := by simp [z', hp, δ]
  refine ⟨z', hf, Finset.card_lt_card ?_⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hS hp)⟩

theorem minimal_subset_sum_injective (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z)
    (hmin : ∀ z', Feasible a b z' → (support z).card ≤ (support z').card)
    (total : D) (htotal : ∀ p, a p total = 1) :
    Set.InjOn (fun S : Finset A => fun v => ∑ p ∈ S, a p v) (↑(support z).powerset) := by
  classical
  intro S hS U hU heq
  have hs : S ⊆ support z := Finset.mem_powerset.mp hS
  have hu : U ⊆ support z := Finset.mem_powerset.mp hU
  have he (v : D) : ∑ p ∈ S, a p v = ∑ p ∈ U, a p v := congrFun heq v
  have hc : S.card = U.card := by simpa [htotal] using he total
  by_contra hne
  have hn : (S \ U).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hd (v : D) : ∑ p ∈ S \ U, a p v = ∑ p ∈ U \ S, a p v := by
    have hsplit (X Y : Finset A) :
        (∑ p ∈ X \ Y, a p v) + (∑ p ∈ X ∩ Y, a p v) = ∑ p ∈ X, a p v := by
      rw [← Finset.sum_union (by
        apply Finset.disjoint_left.mpr
        intro p hp hq
        exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mp hq).2),
        Finset.sdiff_union_inter]
    have h1 := hsplit S U
    have h2 := hsplit U S
    rw [Finset.inter_comm U S] at h2
    have h3 := he v
    omega
  obtain ⟨z', hz', hlt⟩ := exchange a b z hz (S \ U) (U \ S)
    (fun p hp => hs (Finset.mem_sdiff.mp hp).1)
    (fun p hp => hu (Finset.mem_sdiff.mp hp).1)
    (by apply Finset.disjoint_left.mpr; intro p hp hq
        exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1) hn hd
  exact (hmin z' hz').not_gt hlt

theorem subset_sum_le (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z) (S : Finset A) (hS : S ⊆ support z) (v : D) :
    (∑ p ∈ S, a p v) ≤ b v := by
  calc
    _ ≤ ∑ p ∈ S, z p * a p v := Finset.sum_le_sum (fun p hp => by
      have hp' : 1 ≤ z p := (mem_support z p).mp (hS hp)
      simpa using Nat.mul_le_mul_right (a p v) hp')
    _ ≤ ∑ p, z p * a p v := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = b v := hz v

theorem minimal_box_bound (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z)
    (hmin : ∀ z', Feasible a b z' → (support z).card ≤ (support z').card)
    (total : D) (htotal : ∀ p, a p total = 1) :
    2 ^ (support z).card ≤ ∏ v, (b v + 1) := by
  classical
  let f : {S // S ∈ (support z).powerset} → ((v : D) → Fin (b v + 1)) :=
    fun S v => ⟨∑ p ∈ S.val, a p v,
      Nat.lt_succ_of_le (subset_sum_le a b z hz S.val (Finset.mem_powerset.mp S.property) v)⟩
  have hi : Function.Injective f := by
    intro S U he
    apply Subtype.ext
    apply minimal_subset_sum_injective a b z hz hmin total htotal S.property U.property
    funext v
    exact congrArg Fin.val (congrFun he v)
  have hc := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe, Finset.card_powerset, Fintype.card_pi, Fintype.card_fin] using hc

theorem box_le_bits (b : D → ℕ) : ∏ v, (b v + 1) ≤ 2 ^ (∑ v, Nat.size (b v)) := by
  classical
  calc
    _ ≤ ∏ v, 2 ^ Nat.size (b v) := Finset.prod_le_prod' (fun v _ => Nat.lt_size_self (b v))
    _ = _ := (Finset.prod_pow_eq_pow_sum ..)

theorem minimal_bits_bound (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z)
    (hmin : ∀ z', Feasible a b z' → (support z).card ≤ (support z').card)
    (total : D) (htotal : ∀ p, a p total = 1) :
    (support z).card ≤ ∑ v, Nat.size (b v) := by
  have h := (minimal_box_bound a b z hz hmin total htotal).trans (box_le_bits b)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

/-- Replace one copy of each of two distinct supported generators by two copies
of a third. The third generator may already be in the support. -/
theorem replace_pair (a : A → D → ℕ) (b : D → ℕ) (z : A → ℕ)
    (hz : Feasible a b z) (p q r : A) (hpq : p ≠ q) (hp : 0 < z p) (hq : 0 < z q)
    (he : ∀ v, a p v + a q v = 2 * a r v) (e : A → ℕ)
    (hlt : 2 * e r < e p + e q) :
    ∃ z', Feasible a b z' ∧ (∑ t, z' t * e t) < ∑ t, z t * e t := by
  classical
  let z' : A → ℕ := fun t => (if t = p ∨ t = q then z t - 1 else z t) +
    if t = r then 2 else 0
  have hid (t : A) : z' t + (if t = p then 1 else 0) + (if t = q then 1 else 0) =
      z t + (if t = r then 2 else 0) := by
    by_cases htp : t = p
    · subst t; simp only [z', true_or, if_true, hpq, if_false, add_zero]; omega
    · by_cases htq : t = q
      · subst t; simp only [z', or_true, if_true, htp, if_false, add_zero]; omega
      · simp [z', htp, htq]
  have hsum (f : A → ℕ) : (∑ t, z' t * f t) + f p + f q =
      (∑ t, z t * f t) + 2 * f r := by
    have hs := congrArg (fun g : A → ℕ => ∑ t, g t * f t) (funext hid)
    simpa [add_mul, Finset.sum_add_distrib, ite_mul] using hs
  refine ⟨z', ?_, ?_⟩
  · intro v
    have hs := hsum (fun t => a t v)
    rw [hz v] at hs
    have hv := he v
    omega
  · have hs := hsum e
    omega

theorem exists_key_injective {K : Type*} (a : A → D → ℕ) (b : D → ℕ)
    (key : A → K) (e : A → ℕ)
    (hmid : ∀ p q, p ≠ q → key p = key q →
      ∃ r, (∀ v, a p v + a q v = 2 * a r v) ∧ 2 * e r < e p + e q)
    (hex : ∃ z, Feasible a b z) :
    ∃ z, Feasible a b z ∧ Set.InjOn key (↑(support z)) := by
  classical
  obtain ⟨z, hz, hmin⟩ := exists_minimizer (Feasible a b) (fun z => ∑ p, z p * e p) hex
  refine ⟨z, hz, ?_⟩
  intro p hp q hq he
  by_contra hpq
  obtain ⟨r, hr, hlt⟩ := hmid p q hpq he
  obtain ⟨z', hz', hlt'⟩ := replace_pair a b z hz p q r hpq
    ((mem_support z p).mp hp) ((mem_support z q).mp hq) hr e hlt
  exact (hmin z' hz').not_gt hlt'

theorem exists_key_bound {K : Type*} [Fintype K] (a : A → D → ℕ) (b : D → ℕ)
    (key : A → K) (e : A → ℕ)
    (hmid : ∀ p q, p ≠ q → key p = key q →
      ∃ r, (∀ v, a p v + a q v = 2 * a r v) ∧ 2 * e r < e p + e q)
    (hex : ∃ z, Feasible a b z) :
    ∃ z, Feasible a b z ∧ (support z).card ≤ Fintype.card K := by
  obtain ⟨z, hz, hi⟩ := exists_key_injective a b key e hmid hex
  refine ⟨z, hz, ?_⟩
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective (fun p : support z => key p.val)
    (fun p q he => Subtype.ext (hi p.property q.property he))

end UAVProof.SparseNaturalCombination
