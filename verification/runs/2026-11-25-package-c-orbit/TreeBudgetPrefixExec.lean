import TreeBudgetHistJoinExec

/-!
# Package C (Issue #26) — C3 Executable Multi-Child Prefix Fold (Fixed `q`)

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetHistJoinExec`.

Contents:
1. Executable definitions `seedEntries`, `advanceExec`, and `prefixFoldExec`.
2. Seed validity and denotation: `validHistEntries_seedEntries`, `denoteHist_seedEntries`.
3. Generalized fold equivalence `exists_mem_foldl_advanceExec_iff` and main theorem
   `exists_mem_prefixFoldExec_iff_prefixReach`:
   `(∃ out ∈ prefixFoldExec tables us seed, denoteHist out = h) ↔ PrefixReach R H s v q us h`.
4. Three verification examples:
   - empty child list returns `[seed]`;
   - encountering a child with empty candidate table `[]` yields `[]`;
   - 4-vertex signed-cost example in both `[2, 3]` and `[3, 2]` orders yields exactly
     the two active-route cost multisets `{-1, 7}` and `{2, 4}` under `denoteHist`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

section ExecFoldDefinitions

/-- Initialize the parent-side histogram entries once from `(w, q)`. -/
def seedEntries {m : ℕ} (w : ℚ) (q : Fin m → ℕ) : HistEntries :=
  (List.ofFn q).foldr (fun (n : ℕ) acc => addEntry (decide (0 < n), w * (n : ℚ)) 1 acc) []

/-- Combine all current candidate histograms `prev` with all child candidates `child`. -/
def advanceExec (prev child : List HistEntries) : List HistEntries :=
  prev.flatMap fun p => child.flatMap fun c => histJoinExec p c

/-- Executable left-to-right multi-child fold starting from `[seed]`. -/
def prefixFoldExec {V : Type*} (tables : V → List HistEntries) (us : List V)
    (seed : HistEntries) : List HistEntries :=
  us.foldl (fun prev u => advanceExec prev (tables u)) [seed]

end ExecFoldDefinitions

section SeedLemmas

theorem validHistEntries_foldr_addEntry (w : ℚ) (l : List ℕ) :
    ValidHistEntries
      (l.foldr (fun (n : ℕ) acc => addEntry (decide (0 < n), w * (n : ℚ)) 1 acc) []) := by
  induction l with
  | nil =>
    exact ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩
  | cons n ns ih =>
    simpa only [List.foldr_cons] using
      validHistEntries_addEntry (decide (0 < n), w * (n : ℚ)) 1 _ ih

/-- `seedEntries w q` always has distinct keys and strictly positive multiplicities. -/
theorem validHistEntries_seedEntries {m : ℕ} (w : ℚ) (q : Fin m → ℕ) :
    ValidHistEntries (seedEntries w q) :=
  validHistEntries_foldr_addEntry w (List.ofFn q)

theorem denoteHist_foldr_addEntry (w : ℚ) (l : List ℕ) :
    denoteHist (l.foldr (fun (n : ℕ) acc => addEntry (decide (0 < n), w * (n : ℚ)) 1 acc) []) =
      ↑(l.map fun (n : ℕ) => (decide (0 < n), w * (n : ℚ))) := by
  induction l with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.foldr_cons, denoteHist_addEntry, ih, List.map_cons, Multiset.replicate_one]
    rfl

/-- `seedEntries (linearWeight R s v) q` denotes `prefixSeed R s v q`. -/
theorem denoteHist_seedEntries {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (s : V → ℚ) {m : ℕ} (v : V) (q : Fin m → ℕ) :
    denoteHist (seedEntries (linearWeight R s v) q) = prefixSeed R s v q := by
  unfold seedEntries prefixSeed jointHist
  rw [denoteHist_foldr_addEntry]
  have hofFn :
      (List.ofFn q).map (fun (n : ℕ) => (decide (0 < n), linearWeight R s v * (n : ℚ))) =
        (List.finRange m).map (jointType (parentState R s v q ∅ (fun _ _ _ => 0))) := by
    rw [List.ofFn_eq_map, List.map_map]
    apply List.map_congr_left
    intro i _
    simp [jointType, parentState]
  rw [hofFn]
  have huniv : (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := rfl
  rw [huniv, Multiset.map_coe]

end SeedLemmas

section FoldEquivalence

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem validHistEntries_of_mem_advanceExec (prev child : List HistEntries)
    (out : HistEntries) (hout : out ∈ advanceExec prev child) :
    ValidHistEntries out := by
  unfold advanceExec at hout
  rcases List.mem_flatMap.mp hout with ⟨p, _, hp⟩
  rcases List.mem_flatMap.mp hp with ⟨c, _, hc⟩
  exact validHistEntries_of_mem_histJoinExec p c out hc

theorem exists_mem_advanceExec_iff
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (prev child : List HistEntries) (prevSpec : OrbitHist → Prop) (u : V)
    (hprevV : ∀ p ∈ prev, ValidHistEntries p)
    (hchildV : ∀ c ∈ child, ValidHistEntries c)
    (hprev : ∀ h, (∃ p ∈ prev, denoteHist p = h) ↔ prevSpec h)
    (hchild : ∀ h, (∃ c ∈ child, denoteHist c = h) ↔ ChildHist R H m s u h)
    (h : OrbitHist) :
    (∃ out ∈ advanceExec prev child, denoteHist out = h) ↔
      histAdvance R H m s prevSpec u h := by
  unfold advanceExec histAdvance
  constructor
  · rintro ⟨out, hout, rfl⟩
    rcases List.mem_flatMap.mp hout with ⟨p, hp, h1⟩
    rcases List.mem_flatMap.mp h1 with ⟨c, hc, h2⟩
    refine ⟨denoteHist p, denoteHist c,
      (hprev _).mp ⟨p, hp, rfl⟩,
      (hchild _).mp ⟨c, hc, rfl⟩,
      (exists_mem_histJoinExec_iff_histJoin p c (hprevV p hp) (hchildV c hc) _).mp ⟨out, h2, rfl⟩⟩
  · rintro ⟨pH, cH, hpS, hcS, hjoin⟩
    obtain ⟨p, hp, rfl⟩ := (hprev pH).mpr hpS
    obtain ⟨c, hc, rfl⟩ := (hchild cH).mpr hcS
    obtain ⟨out, hout, rfl⟩ :=
      (exists_mem_histJoinExec_iff_histJoin p c (hprevV p hp) (hchildV c hc) h).mpr hjoin
    refine ⟨out, ?_, rfl⟩
    exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨c, hc, hout⟩⟩

/-- Generalized fold equivalence from an arbitrary valid candidate list `prev`. -/
theorem exists_mem_foldl_advanceExec_iff
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (tables : V → List HistEntries) (us : List V)
    (prev : List HistEntries) (prevSpec : OrbitHist → Prop)
    (hprevV : ∀ p ∈ prev, ValidHistEntries p)
    (hprev : ∀ h, (∃ p ∈ prev, denoteHist p = h) ↔ prevSpec h)
    (htablesV : ∀ u ∈ us, ∀ c ∈ tables u, ValidHistEntries c)
    (htables : ∀ u ∈ us, ∀ h, (∃ c ∈ tables u, denoteHist c = h) ↔ ChildHist R H m s u h)
    (h : OrbitHist) :
    (∃ out ∈ us.foldl (fun acc u => advanceExec acc (tables u)) prev, denoteHist out = h) ↔
      us.foldl (histAdvance R H m s) prevSpec h := by
  induction us generalizing prev prevSpec with
  | nil =>
    exact hprev h
  | cons u us ih =>
    simp only [List.foldl_cons]
    have huV : ∀ c ∈ tables u, ValidHistEntries c := htablesV u (List.mem_cons_self ..)
    have huS : ∀ t, (∃ c ∈ tables u, denoteHist c = t) ↔ ChildHist R H m s u t :=
      htables u (List.mem_cons_self ..)
    exact ih (advanceExec prev (tables u)) (histAdvance R H m s prevSpec u)
      (fun out hout => validHistEntries_of_mem_advanceExec prev (tables u) out hout)
      (fun t => exists_mem_advanceExec_iff R H s prev (tables u) prevSpec u hprevV huV hprev huS t)
      (fun w hw => htablesV w (List.mem_cons_of_mem u hw))
      (fun w hw => htables w (List.mem_cons_of_mem u hw))

/-- Main C3 Multi-Child Executable Fold Theorem (fixed `q`):
Given valid child candidate tables matching `ChildHist` for every `u ∈ us`,
`prefixFoldExec tables us (seedEntries (linearWeight R s v) q)` denotes exactly the
histograms reachable under `PrefixReach R H s v q us`. -/
theorem exists_mem_prefixFoldExec_iff_prefixReach
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (tables : V → List HistEntries) (us : List V)
    (htablesV : ∀ u ∈ us, ∀ c ∈ tables u, ValidHistEntries c)
    (htables : ∀ u ∈ us, ∀ h, (∃ c ∈ tables u, denoteHist c = h) ↔ ChildHist R H m s u h)
    (h : OrbitHist) :
    (∃ out ∈ prefixFoldExec tables us (seedEntries (linearWeight R s v) q), denoteHist out = h) ↔
      PrefixReach R H s v q us h := by
  unfold prefixFoldExec PrefixReach
  apply exists_mem_foldl_advanceExec_iff R H s tables us
    [seedEntries (linearWeight R s v) q] (fun t => prefixSeed R s v q = t)
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact validHistEntries_seedEntries (linearWeight R s v) q
  · intro t
    simp only [List.mem_singleton, exists_eq_left, denoteHist_seedEntries]
  · exact htablesV
  · exact htables

end FoldEquivalence

section VerificationExamples

/-! ### Example 1: Empty child list returns `[seed]` -/

theorem exFold_nil {V : Type*} (tables : V → List HistEntries) (seed : HistEntries) :
    prefixFoldExec tables [] seed = [seed] :=
  rfl

/-! ### Example 2: Encountering a child with empty candidate table `[]` yields `[]` -/

theorem advanceExec_nil_left (child : List HistEntries) :
    advanceExec [] child = [] :=
  rfl

theorem advanceExec_nil_right (prev : List HistEntries) :
    advanceExec prev [] = [] := by
  unfold advanceExec
  induction prev with
  | nil => rfl
  | cons p ps _ => simp

theorem foldl_advanceExec_nil {V : Type*} (tables : V → List HistEntries) (us : List V) :
    us.foldl (fun prev u => advanceExec prev (tables u)) [] = [] := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [List.foldl_cons, advanceExec_nil_left, ih]

theorem exFold_empty_child_returns_nil {V : Type*} (tables : V → List HistEntries)
    (us : List V) (seed : HistEntries) (u : V) (hu : u ∈ us) (hemp : tables u = []) :
    prefixFoldExec tables us seed = [] := by
  unfold prefixFoldExec
  generalize hprev : [seed] = prev
  clear hprev
  induction us generalizing prev with
  | nil => exact (List.not_mem_nil hu).elim
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hu with rfl | hws
    · rw [hemp, advanceExec_nil_right, foldl_advanceExec_nil]
    · exact ih hws (advanceExec prev (tables w))

/-! ### Example 3: 4-vertex signed-cost example in both `[2, 3]` and `[3, 2]` orders
Parent weight `w₁ = 2`, `q = ![1, 1]` (both routes active, base cost `2` counted once);
child `2` contributes `(-3, 0)` (one active route, one inactive);
child `3` contributes `(5, 0)` (one active route, one inactive).
Both orders `[2, 3]` and `[3, 2]` yield the exact same set of denoted histograms:
`{(true, -1), (true, 7)}` and `{(true, 2), (true, 4)}`. -/

def ex4_seed : HistEntries := seedEntries (2 : ℚ) (![1, 1] : Fin 2 → ℕ)

def ex4_tables : Fin 4 → List HistEntries
  | 2 => [[((true, (-3 : ℚ)), 1), ((false, (0 : ℚ)), 1)]]
  | 3 => [[((true, (5 : ℚ)), 1), ((false, (0 : ℚ)), 1)]]
  | _ => []

def ex4_hist_split : OrbitHist :=
  Multiset.replicate 1 (true, (-1 : ℚ)) + Multiset.replicate 1 (true, (7 : ℚ))

def ex4_hist_same : OrbitHist :=
  Multiset.replicate 1 (true, (2 : ℚ)) + Multiset.replicate 1 (true, (4 : ℚ))

theorem ex4_seed_eq : ex4_seed = [((true, (2 : ℚ)), 2)] := by
  simp [ex4_seed, seedEntries, addEntry]

theorem ex4_fold_23_eq :
    prefixFoldExec ex4_tables [2, 3] ex4_seed =
      [[((true, (-1 : ℚ)), 1), ((true, (7 : ℚ)), 1)],
       [((true, (4 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
  rw [ex4_seed_eq]
  have h1 :
      advanceExec [[((true, (2 : ℚ)), 2)]] (ex4_tables 2) =
        [[((true, (-1 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
    unfold advanceExec histJoinExec ex4_tables
    have ht1 :
        histJoinTables [((true, (2 : ℚ)), 2)] [((true, (-3 : ℚ)), 1), ((false, (0 : ℚ)), 1)] =
          [[[1, 1]]] := by decide
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ht1, List.map_cons,
      List.map_nil, tableToEntries, addRowEntries, g_in]
    norm_num
    simp [addEntry]
    norm_num
  have h2 :
      advanceExec [[((true, (-1 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] (ex4_tables 3) =
        [[((true, (-1 : ℚ)), 1), ((true, (7 : ℚ)), 1)],
         [((true, (4 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
    unfold advanceExec histJoinExec ex4_tables
    have ht2 :
        histJoinTables [((true, (-1 : ℚ)), 1), ((true, (2 : ℚ)), 1)]
          [((true, (5 : ℚ)), 1), ((false, (0 : ℚ)), 1)] =
          [[[0, 1], [1, 0]], [[1, 0], [0, 1]]] := by decide
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ht2, List.map_cons,
      List.map_nil, tableToEntries, addRowEntries, g_in]
    norm_num
    simp [addEntry]
    norm_num
  simp only [prefixFoldExec, List.foldl_cons, List.foldl_nil, h1, h2]

theorem ex4_fold_32_eq :
    prefixFoldExec ex4_tables [3, 2] ex4_seed =
      [[((true, (7 : ℚ)), 1), ((true, (-1 : ℚ)), 1)],
       [((true, (4 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
  rw [ex4_seed_eq]
  have h1 :
      advanceExec [[((true, (2 : ℚ)), 2)]] (ex4_tables 3) =
        [[((true, (7 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
    unfold advanceExec histJoinExec ex4_tables
    have ht1 :
        histJoinTables [((true, (2 : ℚ)), 2)] [((true, (5 : ℚ)), 1), ((false, (0 : ℚ)), 1)] =
          [[[1, 1]]] := by decide
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ht1, List.map_cons,
      List.map_nil, tableToEntries, addRowEntries, g_in]
    norm_num
    simp [addEntry]
  have h2 :
      advanceExec [[((true, (7 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] (ex4_tables 2) =
        [[((true, (7 : ℚ)), 1), ((true, (-1 : ℚ)), 1)],
         [((true, (4 : ℚ)), 1), ((true, (2 : ℚ)), 1)]] := by
    unfold advanceExec histJoinExec ex4_tables
    have ht2 :
        histJoinTables [((true, (7 : ℚ)), 1), ((true, (2 : ℚ)), 1)]
          [((true, (-3 : ℚ)), 1), ((false, (0 : ℚ)), 1)] =
          [[[0, 1], [1, 0]], [[1, 0], [0, 1]]] := by decide
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ht2, List.map_cons,
      List.map_nil, tableToEntries, addRowEntries, g_in]
    norm_num
    simp [addEntry]
    norm_num
  simp only [prefixFoldExec, List.foldl_cons, List.foldl_nil, h1, h2]

theorem ex4_both_orders_same_denoted_hists :
    ((prefixFoldExec ex4_tables [2, 3] ex4_seed).map denoteHist).toFinset =
      {ex4_hist_same, ex4_hist_split} ∧
    ((prefixFoldExec ex4_tables [3, 2] ex4_seed).map denoteHist).toFinset =
      {ex4_hist_same, ex4_hist_split} := by
  constructor
  · rw [ex4_fold_23_eq]
    ext h
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
      denoteHist, add_zero, ex4_hist_same, ex4_hist_split]
    constructor <;> rintro (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (add_comm _ _)
    · exact Or.inr (add_comm _ _)
    · exact Or.inl rfl
  · rw [ex4_fold_32_eq]
    ext h
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
      denoteHist, add_zero, ex4_hist_same, ex4_hist_split]
    constructor <;> rintro (rfl | rfl)
    · exact Or.inr (add_comm _ _)
    · exact Or.inl (add_comm _ _)
    · exact Or.inr (add_comm _ _)
    · exact Or.inl (add_comm _ _)

end VerificationExamples

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.validHistEntries_seedEntries
#print axioms UAVProof.TreeBudgetOrbitPrototype.denoteHist_seedEntries
#print axioms UAVProof.TreeBudgetOrbitPrototype.exists_mem_prefixFoldExec_iff_prefixReach
#print axioms UAVProof.TreeBudgetOrbitPrototype.exFold_nil
#print axioms UAVProof.TreeBudgetOrbitPrototype.exFold_empty_child_returns_nil
#print axioms UAVProof.TreeBudgetOrbitPrototype.ex4_both_orders_same_denoted_hists
