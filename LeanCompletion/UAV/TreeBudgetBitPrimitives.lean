import LeanCompletion.UAV.TreeBudgetBinaryArithmetic
import LeanCompletion.UAV.TreeBudgetVector

/-! Dynamic-width binary-word primitives. Width measurement traverses the
canonical word once and uses a unary cursor count; that count is control data,
not an uncharged binary addition. The common padded width is obtained by
concatenating two unary cursor counts, whose traversal is charged explicitly. -/
namespace UAVProof.TreeBudgetBitPrimitives
open TreeBudgetBitMachine TreeBudgetBinaryArithmetic

def widthNat (a : ℕ) : Costed ℕ :=
  if a = 0 then ⟨0, 1, 0⟩ else
    let out := widthNat (a / 2)
    ⟨out.value + 1, out.steps + 3, out.allocations + 1⟩
termination_by a

theorem widthNat_spec (a : ℕ) :
    (widthNat a).value = a.size ∧ (widthNat a).steps = 3 * a.size + 1 ∧
      (widthNat a).allocations = a.size := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hz : a = 0
    · subst a; simp [widthNat]
    · have ha : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have hh := ih (a / 2) ha
      have hs : a.size = (a / 2).size + 1 := by
        have hb : Nat.bit (Nat.bodd a) (Nat.div2 a) ≠ 0 := by simpa using hz
        have ht := Nat.size_bit hb
        rw [Nat.bit_bodd_div2, Nat.div2_val] at ht
        exact ht
      have he : widthNat a = ⟨(widthNat (a / 2)).value + 1,
          (widthNat (a / 2)).steps + 3, (widthNat (a / 2)).allocations + 1⟩ := by
        rw [widthNat, if_neg hz]
      simp only [he, hh.1, hh.2.1, hh.2.2, hs]
      simp only [true_and, and_true]
      ring

def binary {α : Type} (op : ℕ → ℕ → ℕ → Costed α) (a b : ℕ) : Costed α :=
  let wa := widthNat a
  let wb := widthNat b
  let out := op (wa.value + wb.value) a b
  ⟨out.value, wa.steps + wb.steps + wa.value + 1 + out.steps,
    wa.allocations + wb.allocations + wa.value + out.allocations⟩

def eqNatD (a b : ℕ) := binary eqNat a b
def leNatD (a b : ℕ) := binary leNat a b
def subNatD (a b : ℕ) := binary subNat a b
def addNatD (a b : ℕ) := binary addNat a b
def zeroNatD (a : ℕ) := eqNatD a 0
def mulNatD (a b : ℕ) := binary mulNat a b

theorem input_lt_width_left (a b : ℕ) : a < 2 ^ (a.size + b.size) :=
  Nat.size_le.mp (by omega)

theorem input_lt_width_right (a b : ℕ) : b < 2 ^ (a.size + b.size) :=
  Nat.size_le.mp (by omega)

@[simp] theorem eqNatD_value (a b : ℕ) : (eqNatD a b).value = decide (a = b) := by
  simp only [eqNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1]
  exact eqNat_value _ _ _ (input_lt_width_left a b) (input_lt_width_right a b)

@[simp] theorem leNatD_value (a b : ℕ) : (leNatD a b).value = decide (a ≤ b) := by
  simp only [leNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1]
  exact leNat_value _ _ _ (input_lt_width_left a b) (input_lt_width_right a b)

@[simp] theorem subNatD_value (a b : ℕ) : (subNatD a b).value = a - b := by
  simp only [subNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1]
  exact subNat_value _ _ _ (input_lt_width_left a b) (input_lt_width_right a b)

@[simp] theorem addNatD_value (a b : ℕ) : (addNatD a b).value = a + b := by
  simp only [addNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1]
  exact addNat_value _ _ _ (input_lt_width_left a b) (input_lt_width_right a b)

@[simp] theorem zeroNatD_value (a : ℕ) : (zeroNatD a).value = decide (a = 0) :=
  eqNatD_value a 0

@[simp] theorem mulNatD_value (a b : ℕ) : (mulNatD a b).value = a * b := by
  simp only [mulNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1]
  exact mulNat_value _ _ _ (input_lt_width_left a b) (input_lt_width_right a b)

theorem mulNatD_steps (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (mulNatD a b).steps ≤ 200 * (B + 1) ^ 2 := by
  have h := mulNat_steps_le (a.size + b.size) a b
  have hw : (a.size + b.size + 1) ^ 2 ≤ (2 * B + 1) ^ 2 := by gcongr; omega
  simp only [mulNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1,
    (widthNat_spec a).2.1, (widthNat_spec b).2.1]
  nlinarith

theorem mulNatD_allocations (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (mulNatD a b).allocations ≤ 40 * (B + 1) ^ 2 := by
  have h := mulNat_allocations_le (a.size + b.size) a b
  have hw : (a.size + b.size + 1) ^ 2 ≤ (2 * B + 1) ^ 2 := by gcongr; omega
  simp only [mulNatD, binary, (widthNat_spec a).1, (widthNat_spec b).1,
    (widthNat_spec a).2.2, (widthNat_spec b).2.2]
  nlinarith

theorem dynamic_steps (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (eqNatD a b).steps ≤ 64 * (B + 1) ∧
    (leNatD a b).steps ≤ 64 * (B + 1) ∧
    (subNatD a b).steps ≤ 64 * (B + 1) ∧
    (addNatD a b).steps ≤ 64 * (B + 1) := by
  simp only [eqNatD, leNatD, subNatD, addNatD, binary, (widthNat_spec a).1,
    (widthNat_spec b).1, (widthNat_spec a).2.1, (widthNat_spec b).2.1,
    eqNat, leNat, subNat, addNat, subBorrow_steps, addCarry_steps]
  omega

theorem dynamic_allocations (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (eqNatD a b).allocations ≤ 8 * (B + 1) ∧
    (leNatD a b).allocations ≤ 8 * (B + 1) ∧
    (subNatD a b).allocations ≤ 8 * (B + 1) ∧
    (addNatD a b).allocations ≤ 8 * (B + 1) := by
  simp only [eqNatD, leNatD, subNatD, addNatD, binary, (widthNat_spec a).1,
    (widthNat_spec b).1, (widthNat_spec a).2.2, (widthNat_spec b).2.2,
    eqNat, leNat, subNat, addNat, subBorrow_allocations, addCarry_allocations]
  omega

/-- Interpret a sign and an unsigned word. Negation changes only the sign cell. -/
def signedDiff (a b : ℕ) : Costed ℤ :=
  let cmp := leNatD b a
  if cmp.value then
    let out := subNatD a b
    ⟨(out.value : ℤ), cmp.steps + out.steps + 1, cmp.allocations + out.allocations + 1⟩
  else
    let out := subNatD b a
    ⟨-(out.value : ℤ), cmp.steps + out.steps + 1, cmp.allocations + out.allocations + 1⟩

@[simp] theorem signedDiff_value (a b : ℕ) : (signedDiff a b).value = (a : ℤ) - b := by
  simp only [signedDiff, leNatD_value, subNatD_value]
  split_ifs <;> simp_all <;> omega

def addIntD (a b : ℤ) : Costed ℤ :=
  let pos := addNatD a.toNat b.toNat
  let neg := addNatD (-a).toNat (-b).toNat
  let out := signedDiff pos.value neg.value
  ⟨out.value, pos.steps + neg.steps + out.steps + 2,
    pos.allocations + neg.allocations + out.allocations + 2⟩

@[simp] theorem addIntD_value (a b : ℤ) : (addIntD a b).value = a + b := by
  simp only [addIntD, signedDiff_value, addNatD_value]
  omega

def mulIntD (a b : ℤ) : Costed ℤ :=
  let out := mulNatD a.natAbs b.natAbs
  ⟨if decide (a < 0) != decide (b < 0) then -(out.value : ℤ) else (out.value : ℤ),
    out.steps + 3, out.allocations + 1⟩

@[simp] theorem mulIntD_value (a b : ℤ) : (mulIntD a b).value = a * b := by
  cases a <;> cases b <;> rename_i a b
  all_goals
    have ha : ¬ (a : ℤ) < 0 := by omega
    have hb : ¬ (b : ℤ) < 0 := by omega
    have hna : Int.negSucc a < 0 := by omega
    have hnb : Int.negSucc b < 0 := by omega
    simp only [mulIntD, mulNatD_value, Int.natAbs_negSucc, Int.natAbs_natCast,
      Int.ofNat_eq_natCast, ha, hb, hna, hnb, decide_true, decide_false,
      bne_self_eq_false, Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    simp [Int.negSucc_eq]
    <;> ring

def leIntD (a b : ℤ) : Costed Bool :=
  if a < 0 then
    if b < 0 then charge 2 0 (leNatD b.natAbs a.natAbs) else ⟨true, 2, 0⟩
  else
    if b < 0 then ⟨false, 2, 0⟩ else charge 2 0 (leNatD a.natAbs b.natAbs)

@[simp] theorem leIntD_value (a b : ℤ) : (leIntD a b).value = decide (a ≤ b) := by
  simp only [leIntD, charge, leNatD_value]
  split_ifs <;> simp_all <;> omega

theorem signedDiff_bounds (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (signedDiff a b).steps ≤ 256 * (B + 1) ∧
    (signedDiff a b).allocations ≤ 32 * (B + 1) := by
  have hab := dynamic_steps a b B ha hb
  have hba := dynamic_steps b a B hb ha
  have hab' := dynamic_allocations a b B ha hb
  have hba' := dynamic_allocations b a B hb ha
  simp only [signedDiff]
  split_ifs <;> dsimp only <;> constructor <;> omega

theorem part_size (a : ℤ) (B : ℕ) (ha : a.natAbs.size ≤ B) : a.toNat.size ≤ B := by
  cases a <;> simp_all

theorem sum_size (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (a + b).size ≤ B + 1 := by
  apply Nat.size_le.mpr
  have ha' := Nat.size_le.mp ha
  have hb' := Nat.size_le.mp hb
  rw [pow_succ]
  omega

theorem addIntD_bounds (a b : ℤ) (B : ℕ)
    (ha : a.natAbs.size ≤ B) (hb : b.natAbs.size ≤ B) :
    (addIntD a b).steps ≤ 768 * (B + 1) ∧
    (addIntD a b).allocations ≤ 96 * (B + 1) := by
  have hap := part_size a B ha
  have hbp := part_size b B hb
  have han := part_size (-a) B (by simpa using ha)
  have hbn := part_size (-b) B (by simpa using hb)
  have hp := (dynamic_steps a.toNat b.toNat B hap hbp).2.2.2
  have hn := (dynamic_steps (-a).toNat (-b).toNat B han hbn).2.2.2
  have hp' := (dynamic_allocations a.toNat b.toNat B hap hbp).2.2.2
  have hn' := (dynamic_allocations (-a).toNat (-b).toNat B han hbn).2.2.2
  have hd := signedDiff_bounds (a.toNat + b.toNat) ((-a).toNat + (-b).toNat) (B + 1)
    (sum_size _ _ _ hap hbp) (sum_size _ _ _ han hbn)
  simp only [addIntD, addNatD_value]
  constructor <;> omega

theorem mulIntD_bounds (a b : ℤ) (B : ℕ)
    (ha : a.natAbs.size ≤ B) (hb : b.natAbs.size ≤ B) :
    (mulIntD a b).steps ≤ 256 * (B + 1) ^ 2 ∧
    (mulIntD a b).allocations ≤ 64 * (B + 1) ^ 2 := by
  have hs := mulNatD_steps a.natAbs b.natAbs B ha hb
  have hm := mulNatD_allocations a.natAbs b.natAbs B ha hb
  simp only [mulIntD]
  constructor <;> nlinarith

theorem leIntD_bounds (a b : ℤ) (B : ℕ)
    (ha : a.natAbs.size ≤ B) (hb : b.natAbs.size ≤ B) :
    (leIntD a b).steps ≤ 128 * (B + 1) ∧
    (leIntD a b).allocations ≤ 8 * (B + 1) := by
  have hab := (dynamic_steps a.natAbs b.natAbs B ha hb).2.1
  have hba := (dynamic_steps b.natAbs a.natAbs B hb ha).2.1
  have hab' := (dynamic_allocations a.natAbs b.natAbs B ha hb).2.1
  have hba' := (dynamic_allocations b.natAbs a.natAbs B hb ha).2.1
  simp only [leIntD, charge]
  split_ifs <;> dsimp only <;> constructor <;> omega

def collect {α : Type} : List (Costed α) → Costed (List α)
  | [] => ⟨[], 1, 0⟩
  | a :: xs =>
    let out := collect xs
    ⟨a.value :: out.value, a.steps + out.steps + 1, a.allocations + out.allocations + 1⟩

@[simp] theorem collect_value {α : Type} (xs : List (Costed α)) :
    (collect xs).value = xs.map Costed.value := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [collect, ih]

theorem collect_steps {α : Type} (xs : List (Costed α)) (B : ℕ)
    (h : ∀ x ∈ xs, x.steps ≤ B) : (collect xs).steps ≤ xs.length * (B + 1) + 1 := by
  induction xs with
  | nil => simp [collect]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [collect, List.length_cons]
    nlinarith

theorem collect_allocations {α : Type} (xs : List (Costed α)) (B : ℕ)
    (h : ∀ x ∈ xs, x.allocations ≤ B) :
    (collect xs).allocations ≤ xs.length * (B + 1) := by
  induction xs with
  | nil => simp [collect]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [collect, List.length_cons]
    nlinarith

/-- Materialize one array cell per list entry. Lists and vectors are semantic
views here; this loop specifies the writes into the newly allocated array. -/
def copyCells {α : Type} : List α → Costed (List α)
  | [] => ⟨[], 1, 0⟩
  | a :: xs =>
    let out := copyCells xs
    ⟨a :: out.value, out.steps + 1, out.allocations + 1⟩

@[simp] theorem copyCells_value {α : Type} (xs : List α) :
    (copyCells xs).value = xs := by induction xs <;> simp [copyCells, *]

@[simp] theorem copyCells_steps {α : Type} (xs : List α) :
    (copyCells xs).steps = xs.length + 1 := by
  induction xs <;> simp [copyCells, *, Nat.add_assoc]

@[simp] theorem copyCells_allocations {α : Type} (xs : List α) :
    (copyCells xs).allocations = xs.length := by induction xs <;> simp [copyCells, *]

def vectorize {α : Type} {n : ℕ} (xs : Vector (Costed α) n) : Costed (Vector α n) :=
  let out := collect xs.toList
  let arr := copyCells out.value
  ⟨⟨arr.value.toArray, by simp [arr, out]⟩,
    out.steps + arr.steps, out.allocations + arr.allocations⟩

@[simp] theorem vectorize_value {α : Type} {n : ℕ} (xs : Vector (Costed α) n) :
    (vectorize xs).value = xs.map Costed.value := by
  apply Vector.ext
  intro i hi
  simp [vectorize]

def allBits : List Bool → Costed Bool
  | [] => ⟨true, 1, 0⟩
  | b :: bs =>
    let out := allBits bs
    ⟨b && out.value, out.steps + 1, out.allocations⟩

@[simp] theorem allBits_value (xs : List Bool) : (allBits xs).value = xs.all id := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [allBits, ih]

@[simp] theorem allBits_steps (xs : List Bool) : (allBits xs).steps = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [allBits, ih]

def guardV {n : ℕ} (p q : Vector ℕ n) : Costed Bool :=
  let flags := vectorize (p.zipWith leNatD q)
  let out := allBits flags.value.toList
  ⟨out.value, flags.steps + out.steps + 2 * n, flags.allocations⟩

def eqV {n : ℕ} (p q : Vector ℕ n) : Costed Bool :=
  let flags := vectorize (p.zipWith eqNatD q)
  let out := allBits flags.value.toList
  ⟨out.value, flags.steps + out.steps + 2 * n, flags.allocations⟩

def subV {n : ℕ} (p q : Vector ℕ n) : Costed (Vector ℕ n) :=
  let out := vectorize (p.zipWith subNatD q)
  ⟨out.value, out.steps + 2 * n, out.allocations⟩

def zeroV {n : ℕ} (p : Vector ℕ n) : Costed Bool :=
  let flags := vectorize (p.map zeroNatD)
  let out := allBits flags.value.toList
  ⟨out.value, flags.steps + out.steps + n, flags.allocations⟩

@[simp] theorem guardV_value {n : ℕ} (p q : Vector ℕ n) :
    (guardV p q).value = TreeBudgetVector.leB p q := by
  simp only [guardV, allBits_value, Vector.all_toList, vectorize_value,
    Vector.map_zipWith, leNatD_value, TreeBudgetVector.leB]

@[simp] theorem eqV_value {n : ℕ} (p q : Vector ℕ n) :
    (eqV p q).value = TreeBudgetVector.eqB p q := by
  simp only [eqV, allBits_value, Vector.all_toList, vectorize_value,
    Vector.map_zipWith, eqNatD_value, TreeBudgetVector.eqB]

@[simp] theorem subV_value {n : ℕ} (p q : Vector ℕ n) :
    (subV p q).value = TreeBudgetVector.sub p q := by
  simp only [subV, vectorize_value, Vector.map_zipWith, subNatD_value]
  rfl

@[simp] theorem zeroV_value {n : ℕ} (p : Vector ℕ n) :
    (zeroV p).value = TreeBudgetVector.isZero p := by
  simp only [zeroV, allBits_value, Vector.all_toList, vectorize_value,
    Vector.map_map, Function.comp_def, zeroNatD_value, TreeBudgetVector.isZero, Vector.all_map]
  rfl

def keyEqV {n : ℕ} (p q : ℕ × Vector ℕ n) : Costed Bool :=
  let counts := eqNatD p.1 q.1
  let rows := eqV p.2 q.2
  ⟨counts.value && rows.value, counts.steps + rows.steps + 1,
    counts.allocations + rows.allocations⟩

theorem keyEqV_value {n : ℕ} (p q : ℕ × Vector ℕ n) :
    (keyEqV p q).value = (decide (p.1 = q.1) && TreeBudgetVector.eqB p.2 q.2) := by
  simp only [keyEqV, eqNatD_value, eqV_value]

theorem vectorize_steps {α : Type} {n : ℕ} (xs : Vector (Costed α) n) (B : ℕ)
    (h : ∀ i : Fin n, xs[i].steps ≤ B) :
    (vectorize xs).steps ≤ n * (B + 2) + 2 := by
  have hh := collect_steps xs.toList B (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact h ⟨i, hi⟩)
  simp only [Vector.length_toList] at hh
  simp only [vectorize, copyCells_steps, collect_value, List.length_map,
    Vector.length_toList]
  nlinarith

theorem vectorize_allocations {α : Type} {n : ℕ} (xs : Vector (Costed α) n) (B : ℕ)
    (h : ∀ i : Fin n, xs[i].allocations ≤ B) :
    (vectorize xs).allocations ≤ n * (B + 2) := by
  have hh := collect_allocations xs.toList B (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact h ⟨i, hi⟩)
  simp only [Vector.length_toList] at hh
  simp only [vectorize, copyCells_allocations, collect_value, List.length_map,
    Vector.length_toList]
  nlinarith

theorem guardV_steps {n : ℕ} (p q : Vector ℕ n) (B : ℕ)
    (hp : ∀ i : Fin n, p[i].size ≤ B) (hq : ∀ i : Fin n, q[i].size ≤ B) :
    (guardV p q).steps ≤ 128 * (n + 1) * (B + 1) := by
  have h := vectorize_steps (p.zipWith leNatD q) (64 * (B + 1)) (by
    intro i
    simpa using (dynamic_steps p[i] q[i] B (hp i) (hq i)).2.1)
  simp only [guardV, allBits_steps, Vector.length_toList]
  nlinarith

theorem eqV_steps {n : ℕ} (p q : Vector ℕ n) (B : ℕ)
    (hp : ∀ i : Fin n, p[i].size ≤ B) (hq : ∀ i : Fin n, q[i].size ≤ B) :
    (eqV p q).steps ≤ 128 * (n + 1) * (B + 1) := by
  have h := vectorize_steps (p.zipWith eqNatD q) (64 * (B + 1)) (by
    intro i
    simpa using (dynamic_steps p[i] q[i] B (hp i) (hq i)).1)
  simp only [eqV, allBits_steps, Vector.length_toList]
  nlinarith

theorem subV_steps {n : ℕ} (p q : Vector ℕ n) (B : ℕ)
    (hp : ∀ i : Fin n, p[i].size ≤ B) (hq : ∀ i : Fin n, q[i].size ≤ B) :
    (subV p q).steps ≤ 128 * (n + 1) * (B + 1) := by
  have h := vectorize_steps (p.zipWith subNatD q) (64 * (B + 1)) (by
    intro i
    simpa using (dynamic_steps p[i] q[i] B (hp i) (hq i)).2.2.1)
  simp only [subV]
  nlinarith

theorem zeroV_steps {n : ℕ} (p : Vector ℕ n) (B : ℕ)
    (hp : ∀ i : Fin n, p[i].size ≤ B) :
    (zeroV p).steps ≤ 128 * (n + 1) * (B + 1) := by
  have h := vectorize_steps (p.map zeroNatD) (64 * (B + 1)) (by
    intro i
    simpa [zeroNatD] using (dynamic_steps p[i] 0 B (hp i) (by simp)).1)
  simp only [zeroV, allBits_steps, Vector.length_toList]
  nlinarith

theorem keyEqV_steps {n : ℕ} (p q : ℕ × Vector ℕ n) (B : ℕ)
    (hp : p.1.size ≤ B) (hq : q.1.size ≤ B)
    (hpr : ∀ i : Fin n, p.2[i].size ≤ B) (hqr : ∀ i : Fin n, q.2[i].size ≤ B) :
    (keyEqV p q).steps ≤ 256 * (n + 1) * (B + 1) := by
  have hc := (dynamic_steps p.1 q.1 B hp hq).1
  have hr := eqV_steps p.2 q.2 B hpr hqr
  simp only [keyEqV]
  nlinarith

theorem vector_allocations {n : ℕ} (p q : Vector ℕ n) (B : ℕ)
    (hp : ∀ i : Fin n, p[i].size ≤ B) (hq : ∀ i : Fin n, q[i].size ≤ B) :
    (guardV p q).allocations ≤ 16 * (n + 1) * (B + 1) ∧
    (eqV p q).allocations ≤ 16 * (n + 1) * (B + 1) ∧
    (subV p q).allocations ≤ 16 * (n + 1) * (B + 1) := by
  have hg := vectorize_allocations (p.zipWith leNatD q) (8 * (B + 1)) (by
    intro i; simpa using (dynamic_allocations p[i] q[i] B (hp i) (hq i)).2.1)
  have he := vectorize_allocations (p.zipWith eqNatD q) (8 * (B + 1)) (by
    intro i; simpa using (dynamic_allocations p[i] q[i] B (hp i) (hq i)).1)
  have hs := vectorize_allocations (p.zipWith subNatD q) (8 * (B + 1)) (by
    intro i; simpa using (dynamic_allocations p[i] q[i] B (hp i) (hq i)).2.2.1)
  simp only [guardV, eqV, subV]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem dynamic_allocations_le_steps (a b : ℕ) :
    (eqNatD a b).allocations ≤ (eqNatD a b).steps ∧
    (leNatD a b).allocations ≤ (leNatD a b).steps ∧
    (subNatD a b).allocations ≤ (subNatD a b).steps ∧
    (addNatD a b).allocations ≤ (addNatD a b).steps := by
  simp only [eqNatD, leNatD, subNatD, addNatD, binary, (widthNat_spec a).1,
    (widthNat_spec b).1, (widthNat_spec a).2.1, (widthNat_spec b).2.1,
    (widthNat_spec a).2.2, (widthNat_spec b).2.2,
    eqNat, leNat, subNat, addNat, subBorrow_allocations, addCarry_allocations,
    subBorrow_steps, addCarry_steps]
  omega

theorem collect_allocations_le_steps {α : Type} (xs : List (Costed α))
    (h : ∀ x ∈ xs, x.allocations ≤ x.steps) :
    (collect xs).allocations ≤ (collect xs).steps := by
  induction xs with
  | nil => simp [collect]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [collect]
    omega

theorem vectorize_allocations_le_steps {α : Type} {n : ℕ} (xs : Vector (Costed α) n)
    (h : ∀ i : Fin n, xs[i].allocations ≤ xs[i].steps) :
    (vectorize xs).allocations ≤ (vectorize xs).steps := by
  have hc := collect_allocations_le_steps xs.toList (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact h ⟨i, hi⟩)
  simp only [vectorize, copyCells_steps, copyCells_allocations, collect_value,
    List.length_map, Vector.length_toList]
  omega

theorem vector_allocations_le_steps {n : ℕ} (p q : Vector ℕ n) :
    (guardV p q).allocations ≤ (guardV p q).steps ∧
    (eqV p q).allocations ≤ (eqV p q).steps ∧
    (subV p q).allocations ≤ (subV p q).steps ∧
    (zeroV p).allocations ≤ (zeroV p).steps := by
  have hg := vectorize_allocations_le_steps (p.zipWith leNatD q) (by
    intro i; simpa using (dynamic_allocations_le_steps p[i] q[i]).2.1)
  have he := vectorize_allocations_le_steps (p.zipWith eqNatD q) (by
    intro i; simpa using (dynamic_allocations_le_steps p[i] q[i]).1)
  have hs := vectorize_allocations_le_steps (p.zipWith subNatD q) (by
    intro i; simpa using (dynamic_allocations_le_steps p[i] q[i]).2.2.1)
  have hz := vectorize_allocations_le_steps (p.map zeroNatD) (by
    intro i; simpa [zeroNatD] using (dynamic_allocations_le_steps p[i] 0).1)
  simp only [guardV, eqV, subV, zeroV]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem keyEqV_allocations_le_steps {n : ℕ} (p q : ℕ × Vector ℕ n) :
    (keyEqV p q).allocations ≤ (keyEqV p q).steps := by
  have hc := (dynamic_allocations_le_steps p.1 q.1).1
  have hr := (vector_allocations_le_steps p.2 q.2).2.1
  simp only [keyEqV]
  omega

theorem mulNatD_allocations_le_steps (a b : ℕ) :
    (mulNatD a b).allocations ≤ (mulNatD a b).steps := by
  have h := mulLoop_allocations_le_steps (a.size + b.size) (a.size + b.size) a b
  simp only [mulNatD, binary, mulNat, (widthNat_spec a).1, (widthNat_spec b).1,
    (widthNat_spec a).2.1, (widthNat_spec b).2.1,
    (widthNat_spec a).2.2, (widthNat_spec b).2.2]
  omega

theorem signedDiff_allocations_le_steps (a b : ℕ) :
    (signedDiff a b).allocations ≤ (signedDiff a b).steps := by
  have hab := dynamic_allocations_le_steps a b
  have hba := dynamic_allocations_le_steps b a
  simp only [signedDiff]
  split_ifs <;> dsimp only <;> omega

theorem signed_allocations_le_steps (a b : ℤ) :
    (addIntD a b).allocations ≤ (addIntD a b).steps ∧
    (mulIntD a b).allocations ≤ (mulIntD a b).steps ∧
    (leIntD a b).allocations ≤ (leIntD a b).steps := by
  have hp := (dynamic_allocations_le_steps a.toNat b.toNat).2.2.2
  have hn := (dynamic_allocations_le_steps (-a).toNat (-b).toNat).2.2.2
  have hd := signedDiff_allocations_le_steps
    (addNatD a.toNat b.toNat).value (addNatD (-a).toNat (-b).toNat).value
  have hm := mulNatD_allocations_le_steps a.natAbs b.natAbs
  have hab := (dynamic_allocations_le_steps a.natAbs b.natAbs).2.1
  have hba := (dynamic_allocations_le_steps b.natAbs a.natAbs).2.1
  constructor
  · simp only [addIntD]; omega
  constructor
  · simp only [mulIntD]; omega
  · simp only [leIntD, charge]
    split_ifs <;> dsimp only <;> omega

end UAVProof.TreeBudgetBitPrimitives
