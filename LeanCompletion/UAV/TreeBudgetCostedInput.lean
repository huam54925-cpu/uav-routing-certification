import LeanCompletion.UAV.TreeBudgetBinaryInput
import LeanCompletion.UAV.TreeBudgetCostedCandidates

/-! Binary-cost validation of materialized parent arrays and raw input fields.
The validator follows at most n links per vertex; scalar operations execute the
binary primitive loops. Address interpretation is applied by the caller. -/
namespace UAVProof.TreeBudgetCostedInput
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetBinaryCodec
open TreeBudgetBinaryInput TreeBudgetParentArray TreeBudgetCostedCandidates

variable {n : ℕ}

def followCost (P : ParentArray n) : ℕ → Fin n → Costed (Fin n)
  | 0, v => ⟨v, 1, 0⟩
  | k + 1, v =>
      let copied := addNatD P.parents[v].val 0
      let down := subNatD (k + 1) 1
      let tail := followCost P k ⟨copied.value, by simpa only [copied, addNatD_value, Nat.add_zero] using P.parents[v].isLt⟩
      ⟨tail.value, copied.steps + down.steps + tail.steps + 3,
        copied.allocations + down.allocations + tail.allocations⟩

@[simp] theorem followCost_value (P : ParentArray n) (k : ℕ) (v : Fin n) :
    (followCost P k v).value = follow P k v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [followCost, follow, ih, parent]

theorem followCost_work (P : ParentArray n) (k : ℕ) (v : Fin n) (B : ℕ)
    (hB : 1 ≤ B) (hn : n.size ≤ B) (hk : k ≤ n) :
    work (followCost P k v) ≤ k * (256 * (B + 1)) + 1 := by
  induction k generalizing v with
  | zero => simp [followCost, work]
  | succ k ih =>
    have hp : P.parents[v].val.size ≤ B :=
      (Nat.size_le_size (Nat.le_of_lt P.parents[v].isLt)).trans hn
    have hkw : (k + 1).size ≤ B := (Nat.size_le_size hk).trans hn
    have h1 : Nat.size 1 ≤ B := by simpa using hB
    have hs := (dynamic_steps P.parents[v].val 0 B hp (by simp)).2.2.2
    have ha := (dynamic_allocations P.parents[v].val 0 B hp (by simp)).2.2.2
    have hd := (dynamic_steps (k + 1) 1 B hkw h1).2.2.1
    have had := (dynamic_allocations (k + 1) 1 B hkw h1).2.2.1
    have ht := ih P.parents[v] (by omega)
    simp only [followCost, addNatD_value, Nat.add_zero, work] at *
    nlinarith

def checkVerticesCost (P : ParentArray n) : List (Fin n) → Costed Bool
  | [] => ⟨true, 1, 0⟩
  | v :: vs =>
      let endPoint := followCost P n v
      let equal := eqNatD endPoint.value.val P.root.val
      let tail := checkVerticesCost P vs
      ⟨equal.value && tail.value,
        endPoint.steps + equal.steps + tail.steps + 2,
        endPoint.allocations + equal.allocations + tail.allocations⟩

@[simp] theorem checkVerticesCost_value (P : ParentArray n) (vs : List (Fin n)) :
    (checkVerticesCost P vs).value = vs.all (fun v => decide (follow P n v = P.root)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [checkVerticesCost, ih, Fin.ext_iff]

theorem checkVerticesCost_work (P : ParentArray n) (vs : List (Fin n)) (B : ℕ)
    (hB : 1 ≤ B) (hn : n.size ≤ B) :
    work (checkVerticesCost P vs) ≤ vs.length * (512 * (n + 1) * (B + 1)) + 1 := by
  induction vs with
  | nil => simp [checkVerticesCost, work]
  | cons v vs ih =>
    have hfollow := followCost_work P n v B hB hn (by rfl)
    have he : (followCost P n v).value.val.size ≤ B :=
      (Nat.size_le_size (Nat.le_of_lt (followCost P n v).value.isLt)).trans hn
    have hr : P.root.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt P.root.isLt)).trans hn
    have hs := (dynamic_steps (followCost P n v).value.val P.root.val B he hr).1
    have ha := (dynamic_allocations (followCost P n v).value.val P.root.val B he hr).1
    simp only [checkVerticesCost, work, List.length_cons] at *
    nlinarith

def validateCost (P : ParentArray n) : Costed Bool :=
  let root := eqNatD P.parents[P.root].val P.root.val
  let visited := checkVerticesCost P (List.finRange n)
  let indices := rangeFrom 0 n
  ⟨root.value && visited.value, root.steps + visited.steps + indices.steps + 2,
    root.allocations + visited.allocations + indices.allocations⟩

@[simp] theorem validateCost_value (P : ParentArray n) :
    (validateCost P).value = validateB P := by
  simp [validateCost, validateB, parent, Fin.ext_iff]

theorem validateCost_work (P : ParentArray n) (B : ℕ) (hB : 1 ≤ B) (hn : n.size ≤ B) :
    work (validateCost P) ≤ 1024 * (n + 1) ^ 2 * (B + 1) := by
  have hp : P.parents[P.root].val.size ≤ B :=
    (Nat.size_le_size (Nat.le_of_lt P.parents[P.root].isLt)).trans hn
  have hr : P.root.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt P.root.isLt)).trans hn
  have hs := (dynamic_steps P.parents[P.root].val P.root.val B hp hr).1
  have ha := (dynamic_allocations P.parents[P.root].val P.root.val B hp hr).1
  have hv := checkVerticesCost_work P (List.finRange n) B hB hn
  have hi := rangeFrom_work 0 n n B (by omega) hn hB
  simp only [List.length_finRange, work] at hv hi
  simp only [validateCost, work]
  nlinarith

def lengthCost {α : Type} : List α → Costed ℕ
  | [] => ⟨0, 1, 0⟩
  | _ :: xs =>
      let tail := lengthCost xs
      let out := addNatD tail.value 1
      ⟨out.value, tail.steps + out.steps + 1, tail.allocations + out.allocations⟩

@[simp] theorem lengthCost_value {α : Type} (xs : List α) :
    (lengthCost xs).value = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lengthCost, ih]

theorem lengthCost_work {α : Type} (xs : List α) (B : ℕ) (hB : 1 ≤ B)
    (h : xs.length.size ≤ B) : work (lengthCost xs) ≤ xs.length * (80 * (B + 1)) + 1 := by
  induction xs with
  | nil => simp [lengthCost, work]
  | cons x xs ih =>
    have ht : xs.length.size ≤ B := (Nat.size_le_size (by simp)).trans h
    have h1 : Nat.size 1 ≤ B := by simpa using hB
    have hs := (dynamic_steps xs.length 1 B ht h1).2.2.2
    have ha := (dynamic_allocations xs.length 1 B ht h1).2.2.2
    have hi := ih ht
    simp only [lengthCost, lengthCost_value, work, List.length_cons] at *
    nlinarith

def ltCost (a b : ℕ) : Costed Bool :=
  let next := addNatD a 1
  let out := leNatD next.value b
  ⟨out.value, next.steps + out.steps + 1, next.allocations + out.allocations⟩

@[simp] theorem ltCost_value (a b : ℕ) : (ltCost a b).value = decide (a < b) := by
  simp only [ltCost, addNatD_value, leNatD_value, Nat.add_one_le_iff]

def shapeCost (I : RawInput) : Costed Bool :=
  let lengths := collect [lengthCost I.parents, lengthCost I.multiplicities,
    lengthCost I.numerators, lengthCost I.denominators]
  let tests := collect (lengths.value.map fun k => eqNatD k I.n)
  let out := allBits tests.value
  ⟨out.value, lengths.steps + tests.steps + out.steps,
    lengths.allocations + tests.allocations + out.allocations⟩

@[simp] theorem shapeCost_value (I : RawInput) : (shapeCost I).value = decide (Shape I) := by
  simp [shapeCost, Shape]

def positiveCost (ds : List ℕ) (budget : ℕ) : Costed Bool :=
  let tests := collect ((budget :: ds).map (ltCost 0))
  let out := allBits tests.value
  ⟨out.value, tests.steps + out.steps, tests.allocations + out.allocations⟩

@[simp] theorem positiveCost_value (ds : List ℕ) (budget : ℕ) :
    (positiveCost ds budget).value = denominatorsPositiveB ds budget := by
  simp [positiveCost, denominatorsPositiveB, List.all_map, Function.comp_def]

def indicesInRangeCost (indices : List ℕ) (bound : ℕ) : Costed Bool :=
  let tests := collect (indices.map fun v => ltCost v bound)
  let out := allBits tests.value
  ⟨out.value, tests.steps + out.steps, tests.allocations + out.allocations⟩

@[simp] theorem indicesInRangeCost_value (indices : List ℕ) (bound : ℕ) :
    (indicesInRangeCost indices bound).value = decide (∀ v ∈ indices, v < bound) := by
  apply Bool.eq_iff_iff.mpr
  simp [indicesInRangeCost, List.all_map, Function.comp_def]

def decodeParentsCost (root : ℕ) (parents : List ℕ) :
    Costed (Option {P : ParentArray parents.length // Valid P}) :=
  let len := lengthCost parents
  let rootTest := ltCost root len.value
  charge (len.steps + rootTest.steps + 1) (len.allocations + rootTest.allocations) (
    if hr : rootTest.value = true then
      let rangeTest := indicesInRangeCost parents len.value
      charge (rangeTest.steps + 1) rangeTest.allocations (
        if hp : rangeTest.value = true then
          let hr' : root < parents.length := by simpa only [rootTest, len, ltCost_value, lengthCost_value,
            decide_eq_true_eq] using hr
          let hp' : ∀ v ∈ parents, v < parents.length := by
            simpa only [rangeTest, len, indicesInRangeCost_value, lengthCost_value, decide_eq_true_eq] using hp
          let copied := copyCells parents
          let data := copied.value.toArray
          let indices := rangeFrom 0 parents.length
          let P : ParentArray parents.length :=
            ⟨⟨root, hr'⟩, Vector.ofFn fun i =>
              ⟨data[i.val]'(by simpa only [data, copied, copyCells_value, List.size_toArray] using i.isLt),
                by simpa only [data, copied, copyCells_value, List.getElem_toArray] using
                  hp' _ (List.getElem_mem i.isLt)⟩⟩
          let checked := validateCost P
          charge (copied.steps + indices.steps + checked.steps + 1)
            (copied.allocations + indices.allocations + checked.allocations) (
            if hP : checked.value = true then
              TreeBudgetBitMachine.pure (some ⟨P, (validateB_eq_true P).mp (by simpa only [checked, validateCost_value] using hP)⟩)
            else TreeBudgetBitMachine.pure none)
        else TreeBudgetBitMachine.pure none)
    else TreeBudgetBitMachine.pure none)

@[simp] theorem decodeParentsCost_value (root : ℕ) (parents : List ℕ) :
    (decodeParentsCost root parents).value = decodeParents root parents := by
  simp only [decodeParentsCost, ltCost_value, lengthCost_value,
    indicesInRangeCost_value, decide_eq_true_eq, copyCells_value, List.getElem_toArray, Fin.getElem_fin,
    charge, TreeBudgetBitMachine.pure, decodeParents]
  split <;> rename_i hr
  · split <;> rename_i hp
    · simp only [validateCost_value]
      split <;> rfl
    · rfl
  · rfl

def decodeRawCost (I : RawInput) : Costed (Option Input) :=
  let shape := shapeCost I
  charge (shape.steps + 1) shape.allocations (
    if hs : shape.value = true then
      let hs' : Shape I := by simpa only [shape, shapeCost_value, decide_eq_true_eq] using hs
      let parents := decodeParentsCost I.root I.parents
      charge (parents.steps + 1) parents.allocations (
        match parents.value with
        | none => TreeBudgetBitMachine.pure none
        | some P =>
          let positive := positiveCost I.denominators I.budgetDenominator
          charge (positive.steps + 1) positive.allocations (
            if hp : positive.value = true then
              let hpos := (denominatorsPositiveB_eq_true _ _).mp
                (show denominatorsPositiveB I.denominators I.budgetDenominator = true by
                  simpa only [positive, positiveCost_value] using hp)
              let cs := copyCells I.multiplicities
              let cn := copyCells I.numerators
              let cd := copyCells I.denominators
              charge (cs.steps + cn.steps + cd.steps + 1) (cs.allocations + cn.allocations + cd.allocations)
                (TreeBudgetBitMachine.pure (some {
                  n := I.parents.length
                  parents := P.val
                  valid := P.property
                  H := ⟨I.multiplicities.toArray, by simpa only [List.size_toArray] using hs'.2.1.trans hs'.1.symm⟩
                  numerators := ⟨I.numerators.toArray, by simpa only [List.size_toArray] using hs'.2.2.1.trans hs'.1.symm⟩
                  denominators := ⟨I.denominators.toArray, by simpa only [List.size_toArray] using hs'.2.2.2.trans hs'.1.symm⟩
                  budgetNumerator := I.budgetNumerator
                  budgetDenominator := I.budgetDenominator
                  positive := by
                    intro v
                    have hlen : I.denominators.length = I.parents.length := hs'.2.2.2.trans hs'.1.symm
                    have hv : v.val < I.denominators.length := by rw [hlen]; exact v.isLt
                    have hx : 0 < I.denominators[v.val] := hpos.2 _ (List.getElem_mem hv)
                    simpa using hx
                  budgetPositive := hpos.1 }))
            else TreeBudgetBitMachine.pure none))
    else TreeBudgetBitMachine.pure none)

@[simp] theorem decodeRawCost_value (I : RawInput) :
    (decodeRawCost I).value = decodeRaw I := by
  simp only [decodeRawCost, shapeCost_value, decide_eq_true_eq, charge, TreeBudgetBitMachine.pure,
    decodeRaw, decodeParentsCost_value]
  split
  · cases hp : decodeParents I.root I.parents with
    | none => rfl
    | some P =>
      simp only [positiveCost_value]
      split <;> rfl
  · rfl

theorem ltCost_work (a b B : ℕ) (hB : 1 ≤ B) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    work (ltCost a b) ≤ 256 * (B + 2) := by
  have h1 : Nat.size 1 ≤ B := by simpa using hB
  have hnext := sum_size a 1 B ha h1
  have hs := (dynamic_steps a 1 B ha h1).2.2.2
  have has := (dynamic_allocations a 1 B ha h1).2.2.2
  have ht := (dynamic_steps (a + 1) b (B + 1) hnext (Nat.le_succ_of_le hb)).2.1
  have hat := (dynamic_allocations (a + 1) b (B + 1) hnext (Nat.le_succ_of_le hb)).2.1
  simp only [ltCost, addNatD_value, work]
  omega

theorem indicesInRangeCost_work (xs : List ℕ) (bound B : ℕ) (hB : 1 ≤ B)
    (hb : bound.size ≤ B) (hx : ∀ x ∈ xs, x.size ≤ B) :
    work (indicesInRangeCost xs bound) ≤ 512 * (xs.length + 1) * (B + 2) := by
  have hc := collect_work (xs.map fun v => ltCost v bound) (256 * (B + 2)) (by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact ltCost_work v bound B hB (hx v hv) hb)
  simp only [List.length_map, work] at hc
  simp only [indicesInRangeCost, work, allBits_steps, allBits_allocations,
    collect_value, List.length_map]
  nlinarith

theorem positiveCost_work (xs : List ℕ) (budget B : ℕ) (hB : 1 ≤ B)
    (hb : budget.size ≤ B) (hx : ∀ x ∈ xs, x.size ≤ B) :
    work (positiveCost xs budget) ≤ 512 * (xs.length + 2) * (B + 2) := by
  have hc := collect_work ((budget :: xs).map (ltCost 0)) (256 * (B + 2)) (by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    have hw : v.size ≤ B := by rcases List.mem_cons.mp hv with rfl | hv; exact hb; exact hx v hv
    exact ltCost_work 0 v B hB (by simp) hw)
  simp only [List.length_map, List.length_cons, work] at hc
  simp only [positiveCost, work, allBits_steps, allBits_allocations,
    collect_value, List.length_map, List.length_cons]
  nlinarith

theorem shapeCost_work (I : RawInput) (hs : Shape I) (B : ℕ)
    (hB : 1 ≤ B) (hn : I.n.size ≤ B) :
    work (shapeCost I) ≤ 2048 * (I.n + 1) * (B + 2) := by
  have h₁ := lengthCost_work I.parents B hB (by simpa [hs.1] using hn)
  have h₂ := lengthCost_work I.multiplicities B hB (by simpa [hs.2.1] using hn)
  have h₃ := lengthCost_work I.numerators B hB (by simpa [hs.2.2.1] using hn)
  have h₄ := lengthCost_work I.denominators B hB (by simpa [hs.2.2.2] using hn)
  have he := (dynamic_steps I.n I.n B hn hn).1
  have hae := (dynamic_allocations I.n I.n B hn hn).1
  simp only [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, work] at h₁ h₂ h₃ h₄
  simp only [shapeCost, work, collect, List.map_cons, List.map_nil,
    lengthCost_value, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, allBits_steps,
    allBits_allocations, List.length_cons, List.length_nil]
  nlinarith

theorem decodeParentsCost_work (root : ℕ) (parents : List ℕ) (B : ℕ)
    (hB : 1 ≤ B) (hlen : parents.length.size ≤ B) (hrw : root.size ≤ B)
    (hpw : ∀ p ∈ parents, p.size ≤ B) :
    work (decodeParentsCost root parents) ≤ 4096 * (parents.length + 1) ^ 2 * (B + 2) := by
  have hl := lengthCost_work parents B hB hlen
  have hr := ltCost_work root parents.length B hB hrw hlen
  have hp := indicesInRangeCost_work parents parents.length B hB hlen hpw
  have hindices := rangeFrom_work 0 parents.length parents.length B (by omega) hlen hB
  have hv (hr : root < parents.length) (hp : ∀ v ∈ parents, v < parents.length) :=
    validateCost_work
      (⟨⟨root, hr⟩, Vector.ofFn fun i => ⟨parents[i], hp _ (List.getElem_mem i.isLt)⟩⟩ :
        ParentArray parents.length) B hB hlen
  simp only [decodeParentsCost, ltCost_value, lengthCost_value,
    indicesInRangeCost_value, decide_eq_true_eq, copyCells_value, List.getElem_toArray, Fin.getElem_fin]
  split_ifs with hr' hp' hv'
  all_goals simp only [charge, TreeBudgetBitMachine.pure, work, copyCells_steps, copyCells_allocations]
  all_goals first
    | (have hvbound := hv hr' hp'; simp only [Fin.getElem_fin, work] at hvbound; unfold work at hl hr hp hindices; nlinarith)
    | (unfold work at hl hr hp hindices; nlinarith)

theorem decodeRawCost_work (I : RawInput) (hs : Shape I) (B : ℕ)
    (hB : 1 ≤ B) (hn : I.n.size ≤ B) (hr : I.root.size ≤ B)
    (hp : ∀ p ∈ I.parents, p.size ≤ B)
    (hd : ∀ d ∈ I.denominators, d.size ≤ B)
    (hT : I.budgetDenominator.size ≤ B) :
    work (decodeRawCost I) ≤ 16384 * (I.n + 1) ^ 2 * (B + 2) := by
  have hshape := shapeCost_work I hs B hB hn
  have hparents := decodeParentsCost_work I.root I.parents B hB (by simpa [hs.1] using hn) hr hp
  have hpositive := positiveCost_work I.denominators I.budgetDenominator B hB hT hd
  simp only [hs.1, hs.2.2.2, work] at hparents hpositive
  unfold work at hshape
  simp only [decodeRawCost, shapeCost_value, decide_eq_true_eq, dif_pos hs]
  split
  · simp only [charge, TreeBudgetBitMachine.pure, work]
    nlinarith
  · split_ifs
    all_goals simp only [charge, TreeBudgetBitMachine.pure, work, copyCells_steps, copyCells_allocations,
      hs.2.1, hs.2.2.1, hs.2.2.2]
    all_goals nlinarith

/-- The checked frontend is polynomial in the actual encoded input length,
including inputs rejected for bad indices, cycles or zero denominators. -/
theorem decodeRawCost_work_encoded (I : RawInput) (hs : Shape I) :
    work (decodeRawCost I) ≤ 16384 * ((encodeInput I).length + 1) ^ 2 *
      ((encodeInput I).length + 3) := by
  have he := inputWeight_le_length I
  dsimp [inputWeight] at he
  have hn := vertexCount_le_length I hs
  have hp : ∀ p ∈ I.parents, p.size ≤ (encodeInput I).length + 1 := by
    intro p hp
    have hm := List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩ : p.size ∈ I.parents.map Nat.size)
    omega
  have hd : ∀ d ∈ I.denominators, d.size ≤ (encodeInput I).length + 1 := by
    intro d hd
    have hm := List.le_sum_of_mem (List.mem_map.mpr ⟨d, hd, rfl⟩ : d.size ∈ I.denominators.map Nat.size)
    omega
  have h := decodeRawCost_work I hs ((encodeInput I).length + 1) (by omega)
    (by omega) (by omega) hp hd (by omega)
  apply h.trans
  gcongr <;> omega

theorem decodeRawCost_work_parsed (bits : Bits) (I : RawInput)
    (h : parseInput bits = some I) :
    work (decodeRawCost I) ≤ 16384 * (bits.length + 1) ^ 2 * (bits.length + 3) := by
  obtain ⟨rfl, hs⟩ := parseInput_canonical bits I h
  exact decodeRawCost_work_encoded I hs

end UAVProof.TreeBudgetCostedInput
