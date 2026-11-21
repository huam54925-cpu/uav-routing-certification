import LeanCompletion.UAV.TreeBudgetRowCheckSpec
import LeanCompletion.UAV.TreeBudgetBinaryExecutionBounds
import LeanCompletion.UAV.TreeBudgetSparseVerifier

/-! Physical widths of both signed accumulators, including padded zero bits.
The multiplier consumes the row coordinate in its first argument. -/
namespace UAVProof.A4RowCheckSpec
open TreeBudgetBinaryCodec TreeBudgetWeightedTM2 TreeBudgetParentArray
open TreeBudgetVectorChecker TreeBudgetSparseVerifier
set_option maxHeartbeats 4000000

def countWidth (es : List Term) : ℕ := (es.map fun e => e.1.bits.length).sum

theorem wordStep_width (e : Term) (pos neg : Bits) (B : ℕ)
    (hp : pos.length≤B) (hn : neg.length≤B) (ha : e.2.natAbs.bits.length≤B) :
    (wordStep e pos neg).1.length ≤ B+e.1.bits.length ∧
      (wordStep e pos neg).2.length ≤ B+e.1.bits.length := by
  have hpos := weighted_length e.1.bits e.2.natAbs.bits pos
  have hneg := weighted_length e.1.bits e.2.natAbs.bits neg
  unfold wordStep
  split_ifs <;> simp only <;> constructor <;> omega

theorem wordFold_width (es : List Term) (pos neg : Bits) (B : ℕ)
    (hp : pos.length≤B) (hn : neg.length≤B)
    (ha : ∀ e∈es, e.2.natAbs.bits.length≤B) :
    (wordFold es pos neg).1.length ≤ B+countWidth es ∧
      (wordFold es pos neg).2.length ≤ B+countWidth es := by
  induction es generalizing pos neg B with
  | nil => simpa [wordFold,countWidth] using And.intro hp hn
  | cons e es ih =>
    obtain ⟨hpos,hneg⟩ := wordStep_width e pos neg B hp hn (ha e (by simp))
    have h := ih (wordStep e pos neg).1 (wordStep e pos neg).2
      (B+e.1.bits.length) hpos hneg (by intro t ht; have := ha t (by simp [ht]); omega)
    simpa [wordFold,countWidth,Nat.add_assoc] using h

theorem initial_width (budget : ℤ) :
    (initial budget).1.length≤budget.natAbs.bits.length ∧
      (initial budget).2.length≤budget.natAbs.bits.length := by
  cases budget <;> simp [initial]

theorem countWidth_flatMap {α : Type} (xs : List α) (f : α → List Term) :
    countWidth (xs.flatMap f)=(xs.map fun x => countWidth (f x)).sum := by
  induction xs <;> simp_all [countWidth,List.map_append,List.sum_append]

theorem allTerms_countWidth {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) :
    countWidth (allTerms P A p)=2*∑ v : Fin n, p[v].bits.length := by
  rw [allTerms,countWidth_flatMap]
  simp [allVertexTerms,countWidth,List.map_ofFn,
    Function.comp_def,List.sum_ofFn,Finset.sum_add_distrib,two_mul]

theorem allTerms_fee_width {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (B : ℕ) (ha : ∀ v : Fin n, A[v].natAbs.bits.length≤B) :
    ∀ e∈allTerms P A p, e.2.natAbs.bits.length≤B := by
  intro e he
  obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
  simp only [allVertexTerms,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact ha v
  · split_ifs <;> simp_all

theorem row_accumulator_width {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (budget : ℤ) (p : Vector ℕ n) (B : ℕ)
    (ha : ∀ v : Fin n, A[v].natAbs.bits.length≤B)
    (hb : budget.natAbs.bits.length≤B) :
    (wordFold (allTerms P A p) (initial budget).1 (initial budget).2).1.length ≤
      B+2*∑ v : Fin n, p[v].bits.length ∧
    (wordFold (allTerms P A p) (initial budget).1 (initial budget).2).2.length ≤
      B+2*∑ v : Fin n, p[v].bits.length := by
  have hi := initial_width budget
  simpa only [allTerms_countWidth] using wordFold_width
    (allTerms P A p) (initial budget).1 (initial budget).2 B
    (hi.1.trans hb) (hi.2.trans hb) (allTerms_fee_width P A p B ha)

/-- Widths of normalized scaled fees are controlled by the raw instance,
without a separately supplied numeric bound. -/
theorem scaled_width (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    (∀ v : Fin I.data.n,
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)[v].natAbs.bits.length
        ≤ 2*x.length+1) ∧
    (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator).natAbs.bits.length
      ≤ 2*x.length+1 := by
  obtain ⟨raw,hx,_,hd⟩ := parseInstance_canonical x I hi
  have hl : (encodeInput raw).length≤x.length := by
    simp only [hx,encodeSpecified,List.length_append]; omega
  constructor
  · intro v
    have h := TreeBudgetBinaryExecutionBounds.scaled_fee_width raw I.data hd v
    rw [Nat.size_eq_bits_len]
    omega
  · have h := TreeBudgetBinaryExecutionBounds.scaled_budget_width raw I.data hd
    rw [Nat.size_eq_bits_len]
    omega

theorem encoded_ints_length (xs : List ℤ) (B : ℕ)
    (h : ∀ a∈xs, a.natAbs.bits.length≤B) :
    (xs.flatMap encodeInt).length≤xs.length*(2*B+2) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [List.flatMap_cons,List.length_append,encodeInt_length,
      List.length_cons,Nat.size_eq_bits_len] at *
    nlinarith

theorem row_payload_length {n : ℕ} (p : Vector ℕ n) :
    (p.toList.flatMap encodeNat).length=2*(∑ v : Fin n, p[v].bits.length)+n := by
  have he : p.toList=List.ofFn (fun v : Fin n => p[v]) := by
    simpa only [Vector.toList_ofFn] using
      congrArg Vector.toList (Vector.ofFn_getElem (xs := p)).symm
  rw [sum_size_encodeNat,he]
  simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Nat.size_eq_bits_len,
    Function.comp_def]

/-- Even a zero coefficient can add padding, so both physical calls are
accounted for at every term. -/
def natCountWidth (es : List NatTerm) : ℕ := (es.map fun e => e.1.bits.length).sum

theorem natStep_width (e : NatTerm) (pos neg : Bits) (B : ℕ)
    (hp : pos.length≤B) (hn : neg.length≤B)
    (hap : e.2.1.bits.length≤B) (han : e.2.2.bits.length≤B) :
    (natStep e pos neg).1.length≤B+e.1.bits.length ∧
      (natStep e pos neg).2.length≤B+e.1.bits.length := by
  have hpos := weighted_length e.1.bits e.2.1.bits pos
  have hneg := weighted_length e.1.bits e.2.2.bits neg
  simp only [natStep]
  constructor <;> omega

theorem natFold_width (es : List NatTerm) (pos neg : Bits) (B : ℕ)
    (hp : pos.length≤B) (hn : neg.length≤B)
    (ha : ∀ e∈es, e.2.1.bits.length≤B ∧ e.2.2.bits.length≤B) :
    (natFold es pos neg).1.length≤B+natCountWidth es ∧
      (natFold es pos neg).2.length≤B+natCountWidth es := by
  induction es generalizing pos neg B with
  | nil => simpa [natFold,natCountWidth] using And.intro hp hn
  | cons e es ih =>
    obtain ⟨hep,hen⟩ := ha e (by simp)
    obtain ⟨hpos,hneg⟩ := natStep_width e pos neg B hp hn hep hen
    have h := ih (natStep e pos neg).1 (natStep e pos neg).2
      (B+e.1.bits.length) hpos hneg (by
        intro t ht
        have := ha t (by simp [ht])
        constructor <;> omega)
    simpa [natFold,natCountWidth,Nat.add_assoc] using h

theorem natCountWidth_flatMap {α : Type} (xs : List α) (f : α → List NatTerm) :
    natCountWidth (xs.flatMap f)=(xs.map fun x => natCountWidth (f x)).sum := by
  induction xs <;> simp_all [natCountWidth,List.map_append,List.sum_append]

theorem tableTerms_countWidth {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n) :
    natCountWidth (tableTerms P Ap An p)=2*∑ v : Fin n, p[v].bits.length := by
  rw [tableTerms,natCountWidth_flatMap]
  simp [tableVertexTerms,natCountWidth,List.map_ofFn,
    Function.comp_def,List.sum_ofFn,Finset.sum_add_distrib,two_mul]

theorem tableTerms_fee_width {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (B : ℕ) (ha : ∀ v : Fin n, Ap[v].bits.length≤B ∧ An[v].bits.length≤B) :
    ∀ e∈tableTerms P Ap An p, e.2.1.bits.length≤B ∧ e.2.2.bits.length≤B := by
  intro e he
  obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
  simp only [tableVertexTerms,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact ha v
  · split_ifs <;> simp_all

theorem table_accumulator_width {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (budget : ℤ) (B : ℕ)
    (ha : ∀ v : Fin n, Ap[v].bits.length≤B ∧ An[v].bits.length≤B)
    (hb : budget.natAbs.bits.length≤B) :
    (natFold (tableTerms P Ap An p) (initial budget).1 (initial budget).2).1.length≤
      B+2*∑ v : Fin n, p[v].bits.length ∧
    (natFold (tableTerms P Ap An p) (initial budget).1 (initial budget).2).2.length≤
      B+2*∑ v : Fin n, p[v].bits.length := by
  have hi := initial_width budget
  simpa only [tableTerms_countWidth] using natFold_width
    (tableTerms P Ap An p) (initial budget).1 (initial budget).2 B
    (hi.1.trans hb) (hi.2.trans hb) (tableTerms_fee_width P Ap An p B ha)

theorem machineVertexTerms_countWidth {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (v : Fin n) : natCountWidth (machineVertexTerms P Ap An p v)≤2*p[v].bits.length := by
  unfold machineVertexTerms
  split_ifs <;> simp [natCountWidth,two_mul]

theorem machineTerms_countWidth {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n) :
    natCountWidth (machineTerms P Ap An p)≤2*∑ v : Fin n, p[v].bits.length := by
  rw [machineTerms,natCountWidth_flatMap,List.map_ofFn,List.sum_ofFn,Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => machineVertexTerms_countWidth P Ap An p v

theorem machineTerms_fee_width {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (B : ℕ) (ha : ∀ v : Fin n, Ap[v].bits.length≤B ∧ An[v].bits.length≤B) :
    ∀ e∈machineTerms P Ap An p, e.2.1.bits.length≤B ∧ e.2.2.bits.length≤B := by
  intro e he
  obtain ⟨v,_,he⟩ := List.mem_flatMap.mp he
  by_cases h : P.parents[v]≠P.root ∧ 0<p[v]
  · simp only [machineVertexTerms,if_pos h,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact ha v
    · exact ha P.parents[v]
  · simp only [machineVertexTerms,if_neg h,List.append_nil,List.mem_cons,
      List.not_mem_nil,or_false] at he
    subst e
    exact ha v

theorem machine_accumulator_width {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (budget : ℤ) (B : ℕ)
    (ha : ∀ v : Fin n, Ap[v].bits.length≤B ∧ An[v].bits.length≤B)
    (hb : budget.natAbs.bits.length≤B) :
    (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).1.length≤
      B+2*∑ v : Fin n, p[v].bits.length ∧
    (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).2.length≤
      B+2*∑ v : Fin n, p[v].bits.length := by
  have hi := initial_width budget
  have h := natFold_width
    (machineTerms P Ap An p) (initial budget).1 (initial budget).2 B
    (hi.1.trans hb) (hi.2.trans hb) (machineTerms_fee_width P Ap An p B ha)
  have hw := machineTerms_countWidth P Ap An p
  constructor <;> omega

theorem machine_accumulator_wire_width {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (budget : ℤ) (B W : ℕ)
    (ha : ∀ v : Fin n, Ap[v].bits.length≤B ∧ An[v].bits.length≤B)
    (hb : budget.natAbs.bits.length≤B) (hw : (p.toList.flatMap encodeNat).length≤W) :
    (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).1.length≤B+W ∧
    (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).2.length≤B+W := by
  have h := machine_accumulator_width P Ap An p budget B ha hb
  rw [row_payload_length] at hw
  constructor <;> omega

end UAVProof.A4RowCheckSpec
