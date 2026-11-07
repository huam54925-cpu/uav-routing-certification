import LeanCompletion.UAV.TreeBudgetBitPrimitives
import LeanCompletion.UAV.TreeBudgetVectorCandidates
import LeanCompletion.UAV.TreeBudgetCandidateCount
import LeanCompletion.UAV.TreeBudgetParentArray

/-! Materialized candidate construction with binary scalar loops. The suffix
table is built once per dimension and reused by reference. This hoisting preserves
the exact ordered list of the existing vector enumerator. Pointer-list rebuilding
and scalar copying are explicit below; address interpretation is a later layer. -/
namespace UAVProof.TreeBudgetCostedCandidates
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetVectorCandidates
open TreeBudgetVector

def work {α : Type} (out : Costed α) := out.steps + out.allocations

def rangeFrom : ℕ → ℕ → Costed (List ℕ)
  | _, 0 => ⟨[], 1, 0⟩
  | start, count + 1 =>
      let next := addNatD start 1
      let down := subNatD (count + 1) 1
      let tail := rangeFrom next.value count
      ⟨start :: tail.value, next.steps + down.steps + tail.steps + 2,
        next.allocations + down.allocations + tail.allocations + 1⟩

@[simp] theorem rangeFrom_value (start count : ℕ) :
    (rangeFrom start count).value = List.range' start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [rangeFrom, List.range'_succ, ih]

theorem rangeFrom_work (start count U B : ℕ) (h : start + count ≤ U)
    (hw : U.size ≤ B) (hB : 1 ≤ B) :
    work (rangeFrom start count) ≤ count * (256 * (B + 1)) + 1 := by
  induction count generalizing start with
  | zero => simp [rangeFrom, work]
  | succ count ih =>
    have hs : start.size ≤ B := (Nat.size_le_size (by omega : start ≤ U)).trans hw
    have hc : (count + 1).size ≤ B := (Nat.size_le_size (by omega : count + 1 ≤ U)).trans hw
    have h1 : Nat.size 1 ≤ B := by simpa using hB
    have ha := (dynamic_steps start 1 B hs h1).2.2.2
    have hb := (dynamic_steps (count + 1) 1 B hc h1).2.2.1
    have haa := (dynamic_allocations start 1 B hs h1).2.2.2
    have hba := (dynamic_allocations (count + 1) 1 B hc h1).2.2.1
    have ht := ih (start + 1) (by omega)
    simp only [rangeFrom, addNatD_value, work] at *
    nlinarith

def copyVector {n : ℕ} (p : Vector ℕ n) : Costed (Vector ℕ n) :=
  vectorize (p.map fun x => addNatD x 0)

@[simp] theorem copyVector_value {n : ℕ} (p : Vector ℕ n) :
    (copyVector p).value = p := by
  apply Vector.ext
  intro i hi
  simp [copyVector]

theorem copyVector_work {n : ℕ} (p : Vector ℕ n) (B : ℕ)
    (h : ∀ i : Fin n, p[i].size ≤ B) :
    work (copyVector p) ≤ 128 * (n + 1) * (B + 1) := by
  have hs := vectorize_steps (p.map fun x => addNatD x 0) (64 * (B + 1)) (by
    intro i
    simpa using (dynamic_steps p[i] 0 B (h i) (by simp)).2.2.2)
  have ha := vectorize_allocations (p.map fun x => addNatD x 0) (8 * (B + 1)) (by
    intro i
    simpa using (dynamic_allocations p[i] 0 B (h i) (by simp)).2.2.2)
  simp only [copyVector, work]
  nlinarith

def consCost {n : ℕ} (a : ℕ) (p : Vector ℕ n) : Costed (Vector ℕ (n + 1)) :=
  copyVector (consV a p)

@[simp] theorem consCost_value {n : ℕ} (a : ℕ) (p : Vector ℕ n) :
    (consCost a p).value = consV a p := copyVector_value _

def prependRows {n : ℕ} (a : ℕ) : List (Vector ℕ n) → Costed (List (Vector ℕ (n + 1)))
  | [] => ⟨[], 1, 0⟩
  | p :: ps =>
      let row := consCost a p
      let tail := prependRows a ps
      ⟨row.value :: tail.value, row.steps + tail.steps + 2,
        row.allocations + tail.allocations + 1⟩

@[simp] theorem prependRows_value {n : ℕ} (a : ℕ) (ps : List (Vector ℕ n)) :
    (prependRows a ps).value = ps.map (consV a) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [prependRows, ih]

theorem prependRows_work {n : ℕ} (a : ℕ) (ps : List (Vector ℕ n)) (K : ℕ)
    (h : ∀ p ∈ ps, work (consCost a p) ≤ K) :
    work (prependRows a ps) ≤ ps.length * (K + 3) + 1 := by
  induction ps with
  | nil => simp [prependRows, work]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    simp only [prependRows, List.length_cons, work] at *
    nlinarith

/-- Copy the traversed list spine, sharing vector payloads. -/
def appendCost {α : Type} : List α → List α → Costed (List α)
  | [], ys => ⟨ys, 1, 0⟩
  | x :: xs, ys =>
      let tail := appendCost xs ys
      ⟨x :: tail.value, tail.steps + 2, tail.allocations + 1⟩

@[simp] theorem appendCost_value {α : Type} (xs ys : List α) :
    (appendCost xs ys).value = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendCost, ih]

theorem appendCost_work {α : Type} (xs ys : List α) :
    work (appendCost xs ys) = 3 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [appendCost, List.length_cons, work] at *; omega

def extendRows {n : ℕ} : List ℕ → List (Vector ℕ n) → Costed (List (Vector ℕ (n + 1)))
  | [], _ => ⟨[], 1, 0⟩
  | a :: heads, tails =>
      let block := prependRows a tails
      let rest := extendRows heads tails
      let joined := appendCost block.value rest.value
      ⟨joined.value, block.steps + rest.steps + joined.steps + 2,
        block.allocations + rest.allocations + joined.allocations⟩

@[simp] theorem extendRows_value {n : ℕ} (heads : List ℕ) (tails : List (Vector ℕ n)) :
    (extendRows heads tails).value = heads.flatMap (fun a => tails.map (consV a)) := by
  induction heads with
  | nil => rfl
  | cons a heads ih => simp [extendRows, ih]

theorem extendRows_work {n : ℕ} (heads : List ℕ) (tails : List (Vector ℕ n)) (K : ℕ)
    (h : ∀ a ∈ heads, ∀ p ∈ tails, work (consCost a p) ≤ K) :
    work (extendRows heads tails) ≤ heads.length * (tails.length * (K + 6) + 4) + 1 := by
  induction heads with
  | nil => simp [extendRows, work]
  | cons a heads ih =>
    have hb := prependRows_work a tails K (h a (by simp))
    have hr := ih (fun a ha => h a (by simp [ha]))
    have hj := appendCost_work (prependRows a tails).value (extendRows heads tails).value
    simp only [prependRows_value, List.length_map] at hj
    simp only [extendRows, work, List.length_cons, prependRows_value] at *
    nlinarith

def boundedCost : (n : ℕ) → Vector ℕ n → Costed (List (Vector ℕ n))
  | 0, _ => ⟨[emptyV], 1, 1⟩
  | n + 1, b =>
      let count := addNatD b[0] 1
      let heads := rangeFrom 0 count.value
      let copied := copyVector (tailV b)
      let tails := boundedCost n copied.value
      let out := extendRows heads.value tails.value
      ⟨out.value, count.steps + heads.steps + copied.steps + tails.steps + out.steps + 2,
        count.allocations + heads.allocations + copied.allocations + tails.allocations + out.allocations⟩

theorem boundedCost_value (n : ℕ) (b : Vector ℕ n) :
    (boundedCost n b).value = boundedVectorsV n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [boundedCost, addNatD_value, rangeFrom_value, copyVector_value,
      extendRows_value, ih, boundedVectorsV]
    rw [List.range_eq_range']

theorem boundedVectorsV_length (n : ℕ) (b : Vector ℕ n) :
    (boundedVectorsV n b).length = ∏ i : Fin n, (b[i] + 1) := by
  have h := congrArg List.length (map_decode_boundedVectorsV n b)
  simpa only [List.length_map, TreeBudgetCandidateCount.boundedVectors_length,
    decode] using h

theorem boundedVectorsV_pos (n : ℕ) (b : Vector ℕ n) :
    1 ≤ (boundedVectorsV n b).length := by
  rw [boundedVectorsV_length]
  exact Finset.one_le_prod (fun _ _ => Nat.succ_le_succ (Nat.zero_le _))

theorem boundedVectorsV_mem {n : ℕ} (b p : Vector ℕ n)
    (h : p ∈ boundedVectorsV n b) : ∀ i : Fin n, p[i] ≤ b[i] := by
  have hm : decode p ∈ TreeBudgetFiniteSearch.boundedVectors n (decode b) := by
    rw [← map_decode_boundedVectorsV]
    exact List.mem_map.mpr ⟨p, h, rfl⟩
  exact (TreeBudgetFiniteSearch.mem_boundedVectors n (decode b) (decode p)).mp hm

theorem boundedCost_work (n : ℕ) (b : Vector ℕ n) (B : ℕ) (hB : 1 ≤ B)
    (hw : ∀ i : Fin n, (b[i] + 1).size ≤ B) :
    work (boundedCost n b) ≤
      1024 * (n + 1) ^ 2 * (B + 1) * (boundedVectorsV n b).length := by
  induction n with
  | zero => simp [boundedCost, boundedVectorsV, work]; omega
  | succ n ih =>
    have hb : b[0].size ≤ B := (Nat.size_le_size (Nat.le_add_right _ 1)).trans (hw 0)
    have h1 : Nat.size 1 ≤ B := by simpa using hB
    have hcs := (dynamic_steps b[0] 1 B hb h1).2.2.2
    have hca := (dynamic_allocations b[0] 1 B hb h1).2.2.2
    have hr := rangeFrom_work 0 (b[0] + 1) (b[0] + 1) B (by omega) (hw 0) hB
    have hc := copyVector_work (tailV b) B (fun i =>
      (Nat.size_le_size (Nat.le_add_right _ 1)).trans (by simpa [tailV] using hw i.succ))
    have ht := ih (tailV b) (fun i => by simpa [tailV] using hw i.succ)
    have ho := extendRows_work (List.range' 0 (b[0] + 1))
      (boundedVectorsV n (tailV b)) (128 * (n + 2) * (B + 1)) (by
        intro a ha p hp
        apply copyVector_work
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hal : a ≤ b[0] := by simpa using ha
          simpa [consCost, consV] using (Nat.size_le_size hal).trans hb
        · have hpl := boundedVectorsV_mem (tailV b) p hp j
          have hbs : (tailV b)[j].size ≤ B :=
            (Nat.size_le_size (Nat.le_add_right _ 1)).trans
              (by simpa [tailV] using hw j.succ)
          simpa [consCost, consV, decode] using (Nat.size_le_size hpl).trans hbs)
    have hpos := boundedVectorsV_pos n (tailV b)
    have hlen : (boundedVectorsV (n + 1) b).length =
        (b[0] + 1) * (boundedVectorsV n (tailV b)).length := by
      simp [boundedVectorsV, List.length_flatMap]
    simp only [List.length_range'] at ho
    have ht' : work (boundedCost n (tailV b)) ≤
        1024 * (n + 1) ^ 2 * (B + 1) *
          ((b[0] + 1) * (boundedVectorsV n (tailV b)).length) :=
      ht.trans (Nat.mul_le_mul_left _ (by nlinarith))
    rw [hlen]
    simp only [boundedCost, addNatD_value, rangeFrom_value, copyVector_value,
      boundedCost_value, work] at *
    nlinarith [Nat.mul_le_mul_left (b[0] + 1) hpos]

/-- Stable filtering evaluates the concrete predicate once per list position. -/
def filterCost {α : Type} (test : α → Costed Bool) : List α → Costed (List α)
  | [] => ⟨[], 1, 0⟩
  | x :: xs =>
      let flag := test x
      let tail := filterCost test xs
      ⟨if flag.value then x :: tail.value else tail.value,
        flag.steps + tail.steps + 2,
        flag.allocations + tail.allocations + if flag.value then 1 else 0⟩

theorem filterCost_value {α : Type} (test : α → Costed Bool) (xs : List α) :
    (filterCost test xs).value = xs.filter (fun x => (test x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filterCost, ih, List.filter_cons]

theorem filterCost_work {α : Type} (test : α → Costed Bool) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, work (test x) ≤ K) :
    work (filterCost test xs) ≤ xs.length * (K + 3) + 1 := by
  induction xs with
  | nil => simp [filterCost, work]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [filterCost, work, List.length_cons] at *
    split_ifs <;> nlinarith

open TreeBudgetParentArray TreeBudgetIntegerCost TreeBudgetVectorChecker

def sumNatCost : List ℕ → Costed ℕ
  | [] => ⟨0, 1, 0⟩
  | x :: xs =>
      let tail := sumNatCost xs
      let out := addNatD x tail.value
      ⟨out.value, tail.steps + out.steps + 1, tail.allocations + out.allocations⟩

@[simp] theorem sumNatCost_value (xs : List ℕ) : (sumNatCost xs).value = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumNatCost, ih]

def sumIntCost : List ℤ → Costed ℤ
  | [] => ⟨0, 1, 0⟩
  | x :: xs =>
      let tail := sumIntCost xs
      let out := addIntD x tail.value
      ⟨out.value, tail.steps + out.steps + 1, tail.allocations + out.allocations⟩

@[simp] theorem sumIntCost_value (xs : List ℤ) : (sumIntCost xs).value = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumIntCost, ih]

theorem sumNatCost_work (xs : List ℕ) (B : ℕ) (h : xs.sum.size ≤ B) :
    work (sumNatCost xs) ≤ xs.length * (80 * (B + 1)) + 1 := by
  induction xs with
  | nil => simp [sumNatCost, work]
  | cons x xs ih =>
    have hx : x.size ≤ B := (Nat.size_le_size (by simp)).trans h
    have ht : xs.sum.size ≤ B := (Nat.size_le_size (by simp)).trans h
    have hs := (dynamic_steps x xs.sum B hx ht).2.2.2
    have ha := (dynamic_allocations x xs.sum B hx ht).2.2.2
    have hi := ih ht
    simp only [sumNatCost, sumNatCost_value, work, List.length_cons] at *
    nlinarith

theorem natAbs_sum_le (xs : List ℤ) : xs.sum.natAbs ≤ (xs.map Int.natAbs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa using (Int.natAbs_add_le x xs.sum).trans (Nat.add_le_add_left ih x.natAbs)

theorem sumIntCost_work (xs : List ℤ) (B : ℕ) (h : (xs.map Int.natAbs).sum.size ≤ B) :
    work (sumIntCost xs) ≤ xs.length * (900 * (B + 1)) + 1 := by
  induction xs with
  | nil => simp [sumIntCost, work]
  | cons x xs ih =>
    have hx : x.natAbs.size ≤ B := (Nat.size_le_size (by simp)).trans h
    have ht : (xs.map Int.natAbs).sum.size ≤ B := (Nat.size_le_size (by simp)).trans h
    have hv : xs.sum.natAbs.size ≤ B := (Nat.size_le_size (natAbs_sum_le xs)).trans ht
    have hs := addIntD_bounds x xs.sum B hx hv
    have hi := ih ht
    simp only [sumIntCost, sumIntCost_value, work, List.length_cons] at *
    nlinarith

def rootTerm {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (v : Fin n) : Costed ℕ :=
  let isRoot := eqNatD v.val P.root.val
  let isChild := eqNatD P.parents[v].val P.root.val
  let copy := addNatD p[v] 0
  ⟨if !isRoot.value && isChild.value then copy.value else 0,
    isRoot.steps + isChild.steps + copy.steps + 3,
    isRoot.allocations + isChild.allocations + copy.allocations⟩

@[simp] theorem rootTerm_value {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (v : Fin n) :
    (rootTerm P p v).value = if v ≠ P.root ∧ P.parents[v] = P.root then p[v] else 0 := by
  simp [rootTerm, Fin.ext_iff]

def rootCountCost {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) : Costed ℕ :=
  let terms := collect (List.ofFn fun v : Fin n => rootTerm P p v)
  let total := sumNatCost terms.value
  ⟨total.value, terms.steps + total.steps + 1, terms.allocations + total.allocations⟩

theorem rootCountCost_value {n : ℕ} (P : ParentArray n) (hP : Valid P) (p : Vector ℕ n) :
    (rootCountCost P p).value = TreeBudgetPatterns.rootCount (toRootedTree P hP) (decode p) := by
  simp [rootCountCost, TreeBudgetPatterns.rootCount, TreeBudgetPatterns.children,
    Finset.sum_filter, List.map_ofFn, List.sum_ofFn, decode]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> rfl

def costTerm {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) : Costed ℤ :=
  let isRoot := eqNatD v.val P.root.val
  let parentRoot := eqNatD P.parents[v].val P.root.val
  let coef := addIntD A[v] (if parentRoot.value then 0 else A[P.parents[v]])
  let out := mulIntD coef.value (p[v] : ℤ)
  ⟨if isRoot.value then 0 else out.value,
    isRoot.steps + parentRoot.steps + coef.steps + out.steps + 3,
    isRoot.allocations + parentRoot.allocations + coef.allocations + out.allocations⟩

@[simp] theorem costTerm_value {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) :
    (costTerm P A p v).value = if v = P.root then 0 else
      (A[v] + if P.parents[v] = P.root then 0 else A[P.parents[v]]) * (p[v] : ℤ) := by
  simp [costTerm, Fin.ext_iff]

def rowCost {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n) : Costed ℤ :=
  let terms := collect (List.ofFn fun v : Fin n => costTerm P A p v)
  let total := sumIntCost terms.value
  ⟨total.value, terms.steps + total.steps + 1, terms.allocations + total.allocations⟩

theorem rowCost_value {n : ℕ} (P : ParentArray n) (hP : Valid P)
    (A : Vector ℤ n) (p : Vector ℕ n) :
    (rowCost P A p).value = intCost (toRootedTree P hP) (fun v => A[v]) (decode p) := by
  simp [rowCost, intCost, List.map_ofFn, List.sum_ofFn, decode]

def nodeCheck {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n) (v : Fin n) : Costed Bool :=
  let isRoot := eqNatD v.val P.root.val
  let parentRoot := eqNatD P.parents[v].val P.root.val
  let bounded := leNatD p[v] H[v]
  let empty := zeroNatD p[v]
  let parentEmpty := zeroNatD p[P.parents[v]]
  ⟨(isRoot.value || bounded.value) &&
      (isRoot.value || empty.value || parentRoot.value || !parentEmpty.value),
    isRoot.steps + parentRoot.steps + bounded.steps + empty.steps + parentEmpty.steps + 6,
    isRoot.allocations + parentRoot.allocations + bounded.allocations +
      empty.allocations + parentEmpty.allocations⟩

@[simp] theorem nodeCheck_value {n : ℕ} (P : ParentArray n)
    (H p : Vector ℕ n) (v : Fin n) : (nodeCheck P H p v).value =
    (decide (v ≠ P.root → p[v] ≤ H[v]) &&
      decide (v ≠ P.root → 0 < p[v] → P.parents[v] ≠ P.root → 0 < p[P.parents[v]])) := by
  apply Bool.eq_iff_iff.mpr
  simp only [nodeCheck, eqNatD_value, leNatD_value, zeroNatD_value,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Fin.val_inj]
  omega

def rowCheck {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) : Costed Bool :=
  let rootZero := zeroNatD p[P.root]
  let flags := collect (List.ofFn fun v : Fin n => nodeCheck P H p v)
  let all := allBits flags.value
  let roots := rootCountCost P p
  let one := eqNatD roots.value 1
  let total := rowCost P A p
  let affordable := leIntD total.value budget
  ⟨rootZero.value && all.value && one.value && affordable.value,
    rootZero.steps + flags.steps + all.steps + roots.steps + one.steps +
      total.steps + affordable.steps + 4,
    rootZero.allocations + flags.allocations + all.allocations + roots.allocations +
      one.allocations + total.allocations + affordable.allocations⟩

theorem rowCheck_value {n : ℕ} (P : ParentArray n) (hP : Valid P) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) :
    (rowCheck P H A budget p).value = rowValidB (toRootedTree P hP) H A budget p := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowCheck, zeroNatD_value, allBits_value, collect_value,
    rootCountCost_value P hP, eqNatD_value, rowCost_value P hP, leIntD_value,
    rowValidB, List.map_ofFn, Function.comp_def, nodeCheck_value,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const, decode, toRootedTree_root, toRootedTree_parent]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, id_eq,
    Bool.and_eq_true, decide_eq_true_eq, forall_and]
  tauto

def normalizeCost {n : ℕ} (P : ParentArray n) (H : Vector ℕ n) : Costed (Vector ℕ n) :=
  copyVector (H.set P.root.val 0 P.root.isLt)

theorem normalizeCost_value {n : ℕ} (P : ParentArray n) (hP : Valid P) (H : Vector ℕ n) :
    (normalizeCost P H).value = TreeBudgetVector.normalize (toRootedTree P hP) H := by
  simp [normalizeCost, TreeBudgetVector.normalize]

def candidateCost {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) : Costed (List (Vector ℕ n)) :=
  let bounds := normalizeCost P H
  let rows := boundedCost n bounds.value
  let checked := filterCost (rowCheck P H A budget) rows.value
  ⟨checked.value, bounds.steps + rows.steps + checked.steps + 2,
    bounds.allocations + rows.allocations + checked.allocations⟩

theorem candidateCost_value {n : ℕ} (P : ParentArray n) (hP : Valid P) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) :
    (candidateCost P H A budget).value = candidatesV (toRootedTree P hP) H A budget := by
  simp only [candidateCost, normalizeCost_value P hP, boundedCost_value,
    filterCost_value, rowCheck_value P hP, candidatesV]

theorem collect_work {α : Type} (xs : List (Costed α)) (K : ℕ)
    (h : ∀ x ∈ xs, work x ≤ K) : work (collect xs) ≤ xs.length * (K + 2) + 1 := by
  induction xs with
  | nil => simp [collect, work]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [collect, work, List.length_cons] at *
    nlinarith

theorem rootTerm_work {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (v : Fin n)
    (B : ℕ) (hn : n.size ≤ B) (hp : p[v].size ≤ B) :
    work (rootTerm P p v) ≤ 256 * (B + 1) := by
  have hv : v.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt v.isLt)).trans hn
  have hr : P.root.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt P.root.isLt)).trans hn
  have hpa : P.parents[v].val.size ≤ B :=
    (Nat.size_le_size (Nat.le_of_lt P.parents[v].isLt)).trans hn
  have h₁ := (dynamic_steps v.val P.root.val B hv hr).1
  have h₂ := (dynamic_steps P.parents[v].val P.root.val B hpa hr).1
  have h₃ := (dynamic_steps p[v] 0 B hp (by simp)).2.2.2
  have a₁ := (dynamic_allocations v.val P.root.val B hv hr).1
  have a₂ := (dynamic_allocations P.parents[v].val P.root.val B hpa hr).1
  have a₃ := (dynamic_allocations p[v] 0 B hp (by simp)).2.2.2
  simp only [rootTerm, work]
  omega

theorem nodeCheck_work {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n) (v : Fin n)
    (B : ℕ) (hn : n.size ≤ B) (hH : ∀ i : Fin n, H[i].size ≤ B)
    (hp : ∀ i : Fin n, p[i].size ≤ B) :
    work (nodeCheck P H p v) ≤ 512 * (B + 1) := by
  have hv : v.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt v.isLt)).trans hn
  have hr : P.root.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt P.root.isLt)).trans hn
  have hpa : P.parents[v].val.size ≤ B :=
    (Nat.size_le_size (Nat.le_of_lt P.parents[v].isLt)).trans hn
  have h₁ := (dynamic_steps v.val P.root.val B hv hr).1
  have h₂ := (dynamic_steps P.parents[v].val P.root.val B hpa hr).1
  have h₃ := (dynamic_steps p[v] H[v] B (hp v) (hH v)).2.1
  have h₄ := (dynamic_steps p[v] 0 B (hp v) (by simp)).1
  have h₅ := (dynamic_steps p[P.parents[v]] 0 B (hp _) (by simp)).1
  have a₁ := (dynamic_allocations v.val P.root.val B hv hr).1
  have a₂ := (dynamic_allocations P.parents[v].val P.root.val B hpa hr).1
  have a₃ := (dynamic_allocations p[v] H[v] B (hp v) (hH v)).2.1
  have a₄ := (dynamic_allocations p[v] 0 B (hp v) (by simp)).1
  have a₅ := (dynamic_allocations p[P.parents[v]] 0 B (hp _) (by simp)).1
  simp only [nodeCheck, zeroNatD, work]
  omega

theorem costTerm_work {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) (B : ℕ) (hn : n.size ≤ B)
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ B) (hp : p[v].size ≤ B) :
    work (costTerm P A p v) ≤ 2048 * (B + 2) ^ 2 := by
  have hv : v.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt v.isLt)).trans hn
  have hr : P.root.val.size ≤ B := (Nat.size_le_size (Nat.le_of_lt P.root.isLt)).trans hn
  have hpa : P.parents[v].val.size ≤ B :=
    (Nat.size_le_size (Nat.le_of_lt P.parents[v].isLt)).trans hn
  have h₁ := (dynamic_steps v.val P.root.val B hv hr).1
  have h₂ := (dynamic_steps P.parents[v].val P.root.val B hpa hr).1
  have a₁ := (dynamic_allocations v.val P.root.val B hv hr).1
  have a₂ := (dynamic_allocations P.parents[v].val P.root.val B hpa hr).1
  let t : ℤ := if (eqNatD P.parents[v].val P.root.val).value then 0 else A[P.parents[v]]
  have ht : t.natAbs.size ≤ B := by unfold t; split_ifs <;> simp_all
  have hc : (A[v] + t).natAbs.size ≤ B + 1 :=
    (Nat.size_le_size (Int.natAbs_add_le _ _)).trans (sum_size _ _ B (hA v) ht)
  have h₃ := addIntD_bounds A[v] t B (hA v) ht
  have h₄ := mulIntD_bounds (A[v] + t) (p[v] : ℤ) (B + 1) hc (by simpa using Nat.le_succ_of_le hp)
  change _ ≤ _
  simp only [costTerm, addIntD_value, work]
  dsimp only [t] at h₃ h₄
  nlinarith

def rootTerms {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) : List ℕ :=
  List.ofFn fun v : Fin n => if v ≠ P.root ∧ P.parents[v] = P.root then p[v] else 0

def costTerms {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n) : List ℤ :=
  List.ofFn fun v : Fin n => if v = P.root then 0 else
    (A[v] + if P.parents[v] = P.root then 0 else A[P.parents[v]]) * (p[v] : ℤ)

theorem rootCountCost_work {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (B : ℕ)
    (hn : n.size ≤ B) (hp : ∀ i : Fin n, p[i].size ≤ B)
    (hs : (rootTerms P p).sum.size ≤ B) :
    work (rootCountCost P p) ≤ 512 * (n + 1) * (B + 1) := by
  have hc := collect_work (List.ofFn fun v : Fin n => rootTerm P p v) (256 * (B + 1)) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact rootTerm_work P p i B hn (hp i))
  have ht := sumNatCost_work (rootTerms P p) B hs
  simp only [List.length_ofFn] at hc
  simp only [rootTerms, List.length_ofFn] at ht
  simp only [rootCountCost, work, collect_value, List.map_ofFn, Function.comp_def, rootTerm_value]
  unfold work at hc ht
  nlinarith

theorem rowCost_work {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n)
    (B : ℕ) (hn : n.size ≤ B) (hA : ∀ i : Fin n, A[i].natAbs.size ≤ B)
    (hp : ∀ i : Fin n, p[i].size ≤ B)
    (hs : ((costTerms P A p).map Int.natAbs).sum.size ≤ B) :
    work (rowCost P A p) ≤ 4096 * (n + 1) * (B + 2) ^ 2 := by
  have hc := collect_work (List.ofFn fun v : Fin n => costTerm P A p v)
    (2048 * (B + 2) ^ 2) (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact costTerm_work P A p i B hn hA (hp i))
  have ht := sumIntCost_work (costTerms P A p) B hs
  simp only [List.length_ofFn] at hc
  simp only [costTerms, List.length_ofFn] at ht
  simp only [rowCost, work, collect_value, List.map_ofFn, Function.comp_def, costTerm_value]
  unfold work at hc ht
  nlinarith

theorem allBits_allocations (xs : List Bool) : (allBits xs).allocations = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [allBits] using ih

theorem rowCheck_work {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) (B : ℕ)
    (hB : 1 ≤ B) (hn : n.size ≤ B) (hH : ∀ i : Fin n, H[i].size ≤ B)
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ B) (hT : budget.natAbs.size ≤ B)
    (hp : ∀ i : Fin n, p[i].size ≤ B)
    (hr : (rootTerms P p).sum.size ≤ B)
    (hc : ((costTerms P A p).map Int.natAbs).sum.size ≤ B) :
    work (rowCheck P H A budget p) ≤ 8192 * (n + 1) * (B + 2) ^ 2 := by
  have hz := (dynamic_steps p[P.root] 0 B (hp _) (by simp)).1
  have az := (dynamic_allocations p[P.root] 0 B (hp _) (by simp)).1
  have hf := collect_work (List.ofFn fun v : Fin n => nodeCheck P H p v)
    (512 * (B + 1)) (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact nodeCheck_work P H p i B hn hH hp)
  have hroots := rootCountCost_work P p B hn hp hr
  have hcost := rowCost_work P A p B hn hA hp hc
  have hrootvalue : (rootCountCost P p).value = (rootTerms P p).sum := by
    simp [rootCountCost, rootTerms, List.map_ofFn, Function.comp_def]
  have hcostvalue : (rowCost P A p).value = (costTerms P A p).sum := by
    simp [rowCost, costTerms, List.map_ofFn, Function.comp_def]
  have h1 : Nat.size 1 ≤ B := by simpa using hB
  have ho := (dynamic_steps (rootCountCost P p).value 1 B (by rw [hrootvalue]; exact hr) h1).1
  have ao := (dynamic_allocations (rootCountCost P p).value 1 B
    (by rw [hrootvalue]; exact hr) h1).1
  have htotal : (rowCost P A p).value.natAbs.size ≤ B := by
    rw [hcostvalue]
    exact (Nat.size_le_size (natAbs_sum_le _)).trans hc
  have ht := leIntD_bounds (rowCost P A p).value budget B htotal hT
  simp only [List.length_ofFn, work] at hf hroots hcost
  simp only [rowCheck, work, zeroNatD, allBits_steps, allBits_allocations, collect_value,
    List.length_map, List.length_ofFn]
  nlinarith

theorem candidateCost_work {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (B K : ℕ) (hB : 1 ≤ B)
    (hH : ∀ i : Fin n, (H[i] + 1).size ≤ B)
    (hcheck : ∀ p ∈ boundedVectorsV n (H.set P.root.val 0 P.root.isLt),
      work (rowCheck P H A budget p) ≤ K) :
    work (candidateCost P H A budget) ≤
      (2048 * (n + 1) ^ 2 * (B + 1) + K + 8) *
        (boundedVectorsV n (H.set P.root.val 0 P.root.isLt)).length := by
  have hw : ∀ i : Fin n, ((H.set P.root.val 0 P.root.isLt)[i] + 1).size ≤ B := by
    intro i
    change (((H.set P.root.val 0 P.root.isLt)[i.val]'i.isLt) + 1).size ≤ B
    simp only [Vector.getElem_set]
    split_ifs
    · simpa using hB
    · exact hH i
  have hc := copyVector_work (H.set P.root.val 0 P.root.isLt) B
    (fun i => (Nat.size_le_size (Nat.le_add_right _ 1)).trans (hw i))
  have he := boundedCost_work n (H.set P.root.val 0 P.root.isLt) B hB hw
  have hf := filterCost_work (rowCheck P H A budget)
    (boundedVectorsV n (H.set P.root.val 0 P.root.isLt)) K hcheck
  have hp := boundedVectorsV_pos n (H.set P.root.val 0 P.root.isLt)
  have hpoly : 128 * (n + 1) * (B + 1) ≤ 1024 * (n + 1) ^ 2 * (B + 1) := by nlinarith
  have hcopy := hc.trans (hpoly.trans (Nat.le_mul_of_pos_right _ hp))
  simp only [candidateCost, normalizeCost, copyVector_value, boundedCost_value, work] at *
  nlinarith

end UAVProof.TreeBudgetCostedCandidates
