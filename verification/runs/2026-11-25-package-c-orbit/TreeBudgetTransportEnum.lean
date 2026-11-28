import TreeBudgetInsideJoin

/-!
# Package C (Issue #26) — C2 Closure: Zero-Multiplicity Regression & Executable Enumerator

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetInsideJoin` (transitively importing C0/C1 and C2).

Contents:
1. Task 1: Independent zero-multiplicity-in-support regression (`m = 1`,
   `A = B = Finset.univ : Finset Bool`, only `false` occurs; proves uniqueness of
   the legal table `N false false = 1` with all other three cells `0`, and invokes
   `transport_realize_exact`).
2. Task 2: Executable row/table enumerators `rowChoices`, `tableChoices`, `enumTables`,
   exact membership theorem `encodeTable_mem_enumTables_iff_legalTable`, and bridge
   `enumTables_pushforward_iff_exists_perm` connecting enumerated tables to all
   compatible permutations' output histograms.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

section Task1ZeroMultiplicityRegression

/-- `m = 1` with full `Bool` support where `true` has multiplicity `0` on both sides. -/
def exZeroMult_x : Fin 1 → Bool := fun _ => false
def exZeroMult_S : Finset Bool := Finset.univ
def exZeroMult_N (a b : exZeroMult_S) : ℕ :=
  if a.1 = false ∧ b.1 = false then 1 else 0

theorem exZeroMult_legal :
    LegalTable exZeroMult_S exZeroMult_S exZeroMult_x exZeroMult_x
      (fun _ _ => True) exZeroMult_N := by
  refine ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _, ?_, ?_, ?_⟩
  · intro a
    rcases a with ⟨a, _⟩
    cases a <;> decide +revert
  · intro b
    rcases b with ⟨b, _⟩
    cases b <;> decide +revert
  · intro _ _ h
    exact (h trivial).elim

/-- Any legal table on this zero-multiplicity support instance must equal `exZeroMult_N`:
`N false false = 1` and all other three cells are `0`. -/
theorem exZeroMult_unique (N : exZeroMult_S → exZeroMult_S → ℕ)
    (hL : LegalTable exZeroMult_S exZeroMult_S exZeroMult_x exZeroMult_x
      (fun _ _ => True) N) :
    N ⟨false, Finset.mem_univ _⟩ ⟨false, Finset.mem_univ _⟩ = 1 ∧
    N ⟨false, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩ = 0 ∧
    N ⟨true, Finset.mem_univ _⟩ ⟨false, Finset.mem_univ _⟩ = 0 ∧
    N ⟨true, Finset.mem_univ _⟩ ⟨true, Finset.mem_univ _⟩ = 0 := by
  rcases hL with ⟨_, _, hrow, hcol, _⟩
  have hS : (Finset.univ : Finset exZeroMult_S) =
      {⟨false, Finset.mem_univ _⟩, ⟨true, Finset.mem_univ _⟩} := by
    ext ⟨b, _⟩
    cases b <;> simp
  have hrF := hrow ⟨false, Finset.mem_univ _⟩
  have hrT := hrow ⟨true, Finset.mem_univ _⟩
  have hcT := hcol ⟨true, Finset.mem_univ _⟩
  rw [hS, Finset.sum_pair (by decide)] at hrF hrT hcT
  have hcardF : (Finset.univ.filter (fun i : Fin 1 => exZeroMult_x i = false)).card = 1 := by decide
  have hcardT : (Finset.univ.filter (fun i : Fin 1 => exZeroMult_x i = true)).card = 0 := by decide
  rw [hcardF] at hrF
  rw [hcardT] at hrT hcT
  omega

/-- Invoke `transport_realize_exact` to obtain the realizing permutation for the
zero-multiplicity-in-support instance. -/
theorem exZeroMult_realizable :
    ∃ σ : Equiv.Perm (Fin 1),
      (∀ _ : Fin 1, True) ∧
      ∀ (a b : exZeroMult_S),
        inducedTable exZeroMult_x exZeroMult_x σ a.1 b.1 = exZeroMult_N a b :=
  ((transport_realize_exact exZeroMult_S exZeroMult_S exZeroMult_x exZeroMult_x
    (fun _ _ => True) exZeroMult_N).mp exZeroMult_legal).2.2

end Task1ZeroMultiplicityRegression

section Task2ExecutableEnumerator

/-- Executable single-row enumerator: allocates total multiplicity `r` across columns
whose compatibility flags and remaining capacities are given by `cols`. -/
def rowChoices : ℕ → List (Bool × ℕ) → List (List ℕ)
  | r, [] => if r = 0 then [[]] else []
  | r, (ok, cap) :: cols =>
    let hi := if ok then min r cap else 0
    (List.range (hi + 1)).flatMap fun n =>
      (rowChoices (r - n) cols).map (List.cons n)

/-- Exact membership characterization of `rowChoices`. -/
theorem mem_rowChoices_iff (r : ℕ) (cols : List (Bool × ℕ)) (row : List ℕ) :
    row ∈ rowChoices r cols ↔
      row.sum = r ∧
      List.Forall₂ (fun n p => n ≤ p.2 ∧ (p.1 = false → n = 0)) row cols := by
  induction cols generalizing r row with
  | nil =>
    simp only [rowChoices, List.forall₂_nil_right_iff]
    split_ifs with hr
    · subst hr
      simp only [List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨_, rfl⟩; rfl
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hsum hnil
      subst hnil
      exact hr hsum.symm
  | cons p cols ih =>
    rcases p with ⟨ok, cap⟩
    simp only [rowChoices, List.mem_flatMap, List.mem_map, List.mem_range,
      List.forall₂_cons_right_iff]
    constructor
    · rintro ⟨n, hn, tail, htail, rfl⟩
      have hhi : n ≤ if ok then min r cap else 0 := Nat.lt_succ_iff.mp hn
      have hnr : n ≤ r := by
        cases ok <;> simp at hhi <;> omega
      have hncap : n ≤ cap := by
        cases ok <;> simp at hhi <;> omega
      have hnok : ok = false → n = 0 := by
        intro hok; subst hok; simp at hhi; omega
      obtain ⟨htsum, htfor⟩ := (ih (r - n) tail).mp htail
      refine ⟨?_, n, tail, ⟨hncap, hnok⟩, htfor, rfl⟩
      simp only [List.sum_cons]
      omega
    · rintro ⟨hsum, n, tail, ⟨hncap, hnok⟩, htfor, rfl⟩
      simp only [List.sum_cons] at hsum
      have hnr : n ≤ r := by omega
      have hhi : n < (if ok then min r cap else 0) + 1 := by
        cases ok
        · have hn0 : n = 0 := hnok rfl
          simp [hn0]
        · simp; omega
      refine ⟨n, hhi, tail, (ih (r - n) tail).mpr ⟨by omega, htfor⟩, rfl⟩

/-- Executable multi-row transport-table enumerator: fills rows sequentially while
subtracting column usages and accepting only when all remaining column capacities are `0`. -/
def tableChoices {J : Type*} (K : J → J → Bool) (bs : List J) :
    List (J × ℕ) → List ℕ → List (List (List ℕ))
  | [], caps => if caps.all (· == 0) then [[]] else []
  | (a, r) :: rows, caps =>
    let rowSpec := bs.zipWith (fun b c => (K a b, c)) caps
    (rowChoices r rowSpec).flatMap fun row =>
      (tableChoices K bs rows (caps.zipWith (· - ·) row)).map (List.cons row)

/-- Helper: column sum at index `j` of a list of rows. -/
def colSum (M : List (List ℕ)) (j : ℕ) : ℕ :=
  (M.map (fun row => row.getD j 0)).sum

@[simp] theorem colSum_nil (j : ℕ) : colSum [] j = 0 := rfl

@[simp] theorem colSum_cons (row : List ℕ) (M : List (List ℕ)) (j : ℕ) :
    colSum (row :: M) j = row.getD j 0 + colSum M j := by
  simp [colSum]

theorem forall₂_zipWith_spec {J : Type*} (K : J → J → Bool) (a : J)
    (bs : List J) (caps row : List ℕ) (hlen : caps.length = bs.length) :
    List.Forall₂ (fun n p => n ≤ p.2 ∧ (p.1 = false → n = 0))
      row (bs.zipWith (fun b c => (K a b, c)) caps) ↔
    row.length = bs.length ∧
    ∀ j (hj : j < bs.length),
      row.getD j 0 ≤ caps.getD j 0 ∧ (K a bs[j] = false → row.getD j 0 = 0) := by
  induction bs generalizing caps row with
  | nil =>
    cases caps with
    | nil =>
      simp only [List.zipWith_nil_left, List.forall₂_nil_right_iff, List.length_nil]
      constructor
      · rintro rfl; exact ⟨rfl, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
      · rintro ⟨hr0, _⟩; exact List.eq_nil_of_length_eq_zero hr0
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases caps with
    | nil => simp at hlen
    | cons c caps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, List.forall₂_cons_right_iff]
      constructor
      · rintro ⟨n, tail, ⟨hnc, hnok⟩, hfor, rfl⟩
        obtain ⟨htlen, htj⟩ := (ih caps tail hlen).mp hfor
        refine ⟨by simp [htlen], ?_⟩
        intro j hj
        cases j with
        | zero => exact ⟨hnc, hnok⟩
        | succ j =>
          have hj' : j < bs.length := Nat.lt_of_succ_lt_succ hj
          simpa using htj j hj'
      · rintro ⟨hrlen, hrj⟩
        cases row with
        | nil => simp at hrlen
        | cons n tail =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hrlen
          have h0 := hrj 0 (Nat.zero_lt_succ _)
          have htail : ∀ j (hj : j < bs.length),
              tail.getD j 0 ≤ caps.getD j 0 ∧ (K a bs[j] = false → tail.getD j 0 = 0) := by
            intro j hj
            simpa using hrj (j + 1) (Nat.succ_lt_succ hj)
          exact ⟨n, tail, h0, (ih caps tail hlen).mpr ⟨hrlen, htail⟩, rfl⟩

theorem all_beq_zero_iff (caps : List ℕ) :
    caps.all (· == 0) = true ↔ ∀ j, j < caps.length → caps.getD j 0 = 0 := by
  induction caps with
  | nil => simp
  | cons c caps ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, List.length_cons, ih]
    constructor
    · rintro ⟨hc0, hrest⟩ j hj
      cases j with
      | zero => simpa using hc0
      | succ j => simpa using hrest j (Nat.lt_of_succ_lt_succ hj)
    · intro h
      refine ⟨by simpa using h 0 (Nat.zero_lt_succ _), ?_⟩
      intro j hj
      simpa using h (j + 1) (Nat.succ_lt_succ hj)

theorem getD_zipWith_sub (caps row : List ℕ) (j : ℕ)
    (hj1 : j < caps.length) (hj2 : j < row.length) :
    (caps.zipWith (· - ·) row).getD j 0 = caps.getD j 0 - row.getD j 0 := by
  induction caps generalizing row j with
  | nil => exact (Nat.not_lt_zero _ hj1).elim
  | cons c caps ih =>
    cases row with
    | nil => exact (Nat.not_lt_zero _ hj2).elim
    | cons r row =>
      cases j with
      | zero => simp
      | succ j =>
        simpa using ih row j (Nat.lt_of_succ_lt_succ hj1) (Nat.lt_of_succ_lt_succ hj2)

/-- Exact membership characterization of `tableChoices`. -/
theorem mem_tableChoices_iff {J : Type*} (K : J → J → Bool) (bs : List J)
    (rows : List (J × ℕ)) (caps : List ℕ) (hlen : caps.length = bs.length)
    (M : List (List ℕ)) :
    M ∈ tableChoices K bs rows caps ↔
      List.Forall₂ (fun row p =>
        row.length = bs.length ∧
        row.sum = p.2 ∧
        ∀ j (hj : j < bs.length), K p.1 bs[j] = false → row.getD j 0 = 0) M rows ∧
      ∀ j, j < bs.length → colSum M j = caps.getD j 0 := by
  induction rows generalizing caps M with
  | nil =>
    simp only [tableChoices, List.forall₂_nil_right_iff]
    split_ifs with hall
    · have h0 := (all_beq_zero_iff caps).mp hall
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨rfl, fun j hj => (h0 j (hlen ▸ hj)).symm⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hnil hcol
      subst hnil
      apply hall
      rw [all_beq_zero_iff]
      intro j hj
      exact (hcol j (hlen ▸ hj)).symm
  | cons p rows ih =>
    rcases p with ⟨a, r⟩
    simp only [tableChoices, List.mem_flatMap, List.mem_map, List.forall₂_cons_right_iff]
    constructor
    · rintro ⟨row, hrow, rest, hrest, rfl⟩
      obtain ⟨hsum, hfor⟩ := (mem_rowChoices_iff r _ row).mp hrow
      obtain ⟨hrlen, hrj⟩ := (forall₂_zipWith_spec K a bs caps row hlen).mp hfor
      have hlen' : (caps.zipWith (· - ·) row).length = bs.length := by
        simp [List.length_zipWith, hlen, hrlen]
      obtain ⟨hMfor, hMcol⟩ := (ih (caps.zipWith (· - ·) row) hlen' rest).mp hrest
      refine ⟨⟨row, rest, ⟨hrlen, hsum, fun j hj hK => (hrj j hj).2 hK⟩, hMfor, rfl⟩, ?_⟩
      intro j hj
      rw [colSum_cons, hMcol j hj, getD_zipWith_sub caps row j (hlen ▸ hj) (hrlen ▸ hj)]
      have hle := (hrj j hj).1
      omega
    · rintro ⟨⟨row, rest, ⟨hrlen, hsum, hforb⟩, hMfor, rfl⟩, hcol⟩
      have hle : ∀ j (hj : j < bs.length), row.getD j 0 ≤ caps.getD j 0 := by
        intro j hj
        have hc := hcol j hj
        rw [colSum_cons] at hc
        omega
      have hrow : row ∈ rowChoices r (bs.zipWith (fun b c => (K a b, c)) caps) := by
        rw [mem_rowChoices_iff]
        refine ⟨hsum, (forall₂_zipWith_spec K a bs caps row hlen).mpr ⟨hrlen, ?_⟩⟩
        intro j hj
        exact ⟨hle j hj, hforb j hj⟩
      have hlen' : (caps.zipWith (· - ·) row).length = bs.length := by
        simp [List.length_zipWith, hlen, hrlen]
      have hrest : rest ∈ tableChoices K bs rows (caps.zipWith (· - ·) row) := by
        rw [ih (caps.zipWith (· - ·) row) hlen' rest]
        refine ⟨hMfor, ?_⟩
        intro j hj
        rw [getD_zipWith_sub caps row j (hlen ▸ hj) (hrlen ▸ hj)]
        have hc := hcol j hj
        rw [colSum_cons] at hc
        have := hle j hj
        omega
      exact ⟨row, hrow, rest, hrest, rfl⟩

/-- Top-level executable transport-table enumerator reading marginals directly from `x, y`. -/
def enumTables {m : ℕ} {J : Type*} [DecidableEq J]
    (K : J → J → Bool) (as bs : List J) (x y : Fin m → J) : List (List (List ℕ)) :=
  let rows := as.map fun a => (a, (Finset.univ.filter (fun i : Fin m => x i = a)).card)
  let caps := bs.map fun b => (Finset.univ.filter (fun j : Fin m => y j = b)).card
  tableChoices K bs rows caps

/-- Encode a semantic transport table `N : as.toFinset → bs.toFinset → ℕ` along fixed
ordered lists `as, bs`. -/
def encodeTable {J : Type*} [DecidableEq J] (as bs : List J)
    (N : as.toFinset → bs.toFinset → ℕ) : List (List ℕ) :=
  as.attach.map fun a =>
    bs.attach.map fun b =>
      N ⟨a.1, List.mem_toFinset.mpr a.2⟩ ⟨b.1, List.mem_toFinset.mpr b.2⟩

theorem sum_attach_eq_finset_sum {J : Type*} [DecidableEq J] (l : List J) (hl : l.Nodup)
    (f : l.toFinset → ℕ) :
    (l.attach.map (fun x => f ⟨x.1, List.mem_toFinset.mpr x.2⟩)).sum =
      ∑ x : l.toFinset, f x := by
  classical
  have h1 : (∑ x : l.toFinset, f x) =
      ∑ x ∈ l.toFinset.attach, f x := by
    rfl
  rw [h1]
  have hnodup : l.attach.Nodup := List.nodup_attach.mpr hl
  have htoFinset :
      (l.attach.map (fun x => (⟨x.1, List.mem_toFinset.mpr x.2⟩ : l.toFinset))).toFinset =
        l.toFinset.attach := by
    ext ⟨v, hv⟩
    simp [List.mem_toFinset.mp hv]
  have hmapNodup :
      (l.attach.map (fun x => (⟨x.1, List.mem_toFinset.mpr x.2⟩ : l.toFinset))).Nodup := by
    refine hnodup.map ?_
    intro x y h
    exact Subtype.ext (Subtype.mk.inj h)
  rw [← htoFinset, List.sum_toFinset _ hmapNodup, List.map_map]
  rfl

theorem getD_map_attach {J : Type*} [DecidableEq J] (l : List J) (f : {x // x ∈ l} → ℕ)
    (j : ℕ) (hj : j < l.length) :
    (l.attach.map f).getD j 0 = f ⟨l[j], List.getElem_mem hj⟩ := by
  have hj' : j < (l.attach.map f).length := by simp [hj]
  rw [List.getD_eq_getElem _ _ hj']
  simp

/-- Main C2 Enumerator Membership Theorem:
For duplicate-free ordered supports `as, bs` containing the images of `x, y`, the encoded
table `encodeTable as bs N` belongs to `enumTables K as bs x y` iff `N` satisfies `LegalTable`. -/
theorem encodeTable_mem_enumTables_iff_legalTable
    {m : ℕ} {J : Type*} [DecidableEq J]
    (K : J → J → Bool) (as bs : List J) (has : as.Nodup) (hbs : bs.Nodup)
    (x y : Fin m → J)
    (hx : ∀ i, x i ∈ as.toFinset) (hy : ∀ j, y j ∈ bs.toFinset)
    (N : as.toFinset → bs.toFinset → ℕ) :
    encodeTable as bs N ∈ enumTables K as bs x y ↔
      LegalTable as.toFinset bs.toFinset x y (fun a b => K a b = true) N := by
  unfold enumTables
  have hlen : (bs.map fun b => (Finset.univ.filter (fun j : Fin m => y j = b)).card).length =
      bs.length := by simp
  rw [mem_tableChoices_iff K bs _ _ hlen (encodeTable as bs N)]
  have hForall₂ :
      List.Forall₂ (fun row p =>
        row.length = bs.length ∧
        row.sum = p.2 ∧
        ∀ j (hj : j < bs.length), K p.1 bs[j] = false → row.getD j 0 = 0)
        (encodeTable as bs N)
        (as.map fun a => (a, (Finset.univ.filter (fun i : Fin m => x i = a)).card)) ↔
      (∀ a : as.toFinset,
        (∑ b : bs.toFinset, N a b) = (Finset.univ.filter (fun i : Fin m => x i = a.1)).card) ∧
      (∀ (a : as.toFinset) (b : bs.toFinset), ¬ (K a.1 b.1 = true) → N a b = 0) := by
    unfold encodeTable
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    have hattach : ∀ (P : {a // a ∈ as} → J → Prop),
        List.Forall₂ P as.attach as ↔ ∀ a : {a // a ∈ as}, P a a.1 := by
      intro P
      have hsub : as = as.attach.map Subtype.val := by simp
      conv_lhs => rhs; rw [hsub]
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      constructor
      · intro h a; exact h a (List.mem_attach as a)
      · intro h a _; exact h a
    rw [hattach]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro ⟨a, ha⟩
        have ha' : a ∈ as := List.mem_toFinset.mp ha
        have h1 := (h ⟨a, ha'⟩).2.1
        rw [sum_attach_eq_finset_sum bs hbs (fun b => N ⟨a, ha⟩ b)] at h1
        exact h1
      · intro ⟨a, ha⟩ ⟨b, hb⟩ hnotK
        have ha' : a ∈ as := List.mem_toFinset.mp ha
        have hb' : b ∈ bs := List.mem_toFinset.mp hb
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
        have hKfalse : K a bs[j] = false := Bool.eq_false_iff.mpr hnotK
        have h2 := (h ⟨a, ha'⟩).2.2 j hj hKfalse
        rw [getD_map_attach bs _ j hj] at h2
        exact h2
    · rintro ⟨hrow, hforb⟩ ⟨a, ha⟩
      refine ⟨by simp, ?_, ?_⟩
      · rw [sum_attach_eq_finset_sum bs hbs (fun b => N ⟨a, List.mem_toFinset.mpr ha⟩ b)]
        exact hrow ⟨a, List.mem_toFinset.mpr ha⟩
      · intro j hj hKfalse
        rw [getD_map_attach bs _ j hj]
        apply hforb ⟨a, List.mem_toFinset.mpr ha⟩
          ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩
        simp [hKfalse]
  have hCol :
      (∀ j, j < bs.length →
        colSum (encodeTable as bs N) j =
          (bs.map fun b => (Finset.univ.filter (fun i : Fin m => y i = b)).card).getD j 0) ↔
      (∀ b : bs.toFinset,
        (∑ a : as.toFinset, N a b) = (Finset.univ.filter (fun i : Fin m => y i = b.1)).card) := by
    have hcolAt : ∀ j (hj : j < bs.length),
        colSum (encodeTable as bs N) j =
          ∑ a : as.toFinset, N a ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩ := by
      intro j hj
      unfold colSum encodeTable
      rw [List.map_map]
      have hmap :
          (as.attach.map ((fun row => row.getD j 0) ∘
            fun a => bs.attach.map fun b =>
              N ⟨a.1, List.mem_toFinset.mpr a.2⟩ ⟨b.1, List.mem_toFinset.mpr b.2⟩)) =
          as.attach.map (fun a =>
            N ⟨a.1, List.mem_toFinset.mpr a.2⟩ ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩) := by
        apply List.map_congr_left
        intro a _
        exact getD_map_attach bs _ j hj
      rw [hmap]
      exact sum_attach_eq_finset_sum as has
        (fun a => N a ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩)
    constructor
    · intro h ⟨b, hb⟩
      have hb' : b ∈ bs := List.mem_toFinset.mp hb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
      have h1 := h j hj
      rw [hcolAt j hj] at h1
      have hj' : j < (bs.map fun b => (Finset.univ.filter (fun i : Fin m => y i = b)).card).length := by
        simp [hj]
      rw [List.getD_eq_getElem _ _ hj'] at h1
      simpa using h1
    · intro h j hj
      rw [hcolAt j hj]
      have hj' : j < (bs.map fun b => (Finset.univ.filter (fun i : Fin m => y i = b)).card).length := by
        simp [hj]
      rw [List.getD_eq_getElem _ _ hj']
      simpa using h ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩
  rw [hForall₂, hCol]
  unfold LegalTable
  tauto

/-- Computable Boolean version of `K_in` on `JointType`. -/
def K_in_bool (a b : JointType) : Bool :=
  !b.1 || a.1

theorem K_in_bool_iff (a b : JointType) :
    K_in_bool a b = true ↔ K_in a b := by
  unfold K_in_bool K_in
  cases a.1 <;> cases b.1 <;> decide

/-- End-to-end bridge connecting the executable table enumerator `enumTables` to all
compatible permutations and their merged output histograms. -/
theorem enumTables_pushforward_iff_exists_perm
    {m : ℕ} (as bs : List JointType) (has : as.Nodup) (hbs : bs.Nodup)
    (x y : Fin m → JointType)
    (hx : ∀ i, x i ∈ as.toFinset) (hy : ∀ j, y j ∈ bs.toFinset)
    (h : Multiset JointType) :
    (∃ N : as.toFinset → bs.toFinset → ℕ,
      encodeTable as bs N ∈ enumTables K_in_bool as bs x y ∧
      tablePushforwardHist N = h) ↔
    (∃ σ : Equiv.Perm (Fin m),
      (∀ i, K_in (x i) (y (σ i))) ∧
      (Finset.univ : Finset (Fin m)).val.map (fun i => g_in (x i) (y (σ i))) = h) := by
  have hKeq : (fun a b => K_in_bool a b = true) = K_in := by
    funext a b; exact propext (K_in_bool_iff a b)
  constructor
  · rintro ⟨N, hmem, hpush⟩
    have hLeg : LegalTable as.toFinset bs.toFinset x y K_in N := by
      rw [← hKeq]
      exact (encodeTable_mem_enumTables_iff_legalTable K_in_bool as bs has hbs x y hx hy N).mp hmem
    rcases ((transport_realize_exact as.toFinset bs.toFinset x y K_in N).mp hLeg).2.2
      with ⟨σ, hK, hN⟩
    refine ⟨σ, hK, ?_⟩
    rw [merged_hist_eq_tablePushforwardHist as.toFinset bs.toFinset x y σ N hx hy hN, hpush]
  · rintro ⟨σ, hK, hhist⟩
    let N : as.toFinset → bs.toFinset → ℕ := fun a b => inducedTable x y σ a.1 b.1
    have hLeg : LegalTable as.toFinset bs.toFinset x y K_in N :=
      legalTable_of_perm as.toFinset bs.toFinset x y K_in hx hy σ hK
    have hmem : encodeTable as bs N ∈ enumTables K_in_bool as bs x y := by
      rw [encodeTable_mem_enumTables_iff_legalTable K_in_bool as bs has hbs x y hx hy N, hKeq]
      exact hLeg
    refine ⟨N, hmem, ?_⟩
    rw [← merged_hist_eq_tablePushforwardHist as.toFinset bs.toFinset x y σ N hx hy (fun _ _ => rfl),
      hhist]

end Task2ExecutableEnumerator

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.exZeroMult_legal
#print axioms UAVProof.TreeBudgetOrbitPrototype.exZeroMult_unique
#print axioms UAVProof.TreeBudgetOrbitPrototype.exZeroMult_realizable
#print axioms UAVProof.TreeBudgetOrbitPrototype.encodeTable_mem_enumTables_iff_legalTable
#print axioms UAVProof.TreeBudgetOrbitPrototype.enumTables_pushforward_iff_exists_perm
