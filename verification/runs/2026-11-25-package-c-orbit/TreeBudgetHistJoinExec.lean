import TreeBudgetTransportEnum
import TreeBudgetPrefixReach

/-!
# Package C (Issue #26) — C3 Executable Internal Histogram Join

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetTransportEnum` and `TreeBudgetPrefixReach`.

Contents:
1. Executable representation `HistEntries := List (JointType × ℕ)` with denotation
   `denoteHist` and validity predicate `ValidHistEntries` (distinct types, positive counts).
2. Executable join `histJoinTables` / `histJoinExec` accumulating positive cells `N a b`
   directly into output type `g_in a b` with multiplicity merging (`addEntry`).
3. Membership theorem `exists_mem_histJoinExec_iff_histJoin`: under `ValidHistEntries p`
   and `ValidHistEntries c`, `(∃ out ∈ histJoinExec p c, denoteHist out = h) ↔ HistJoin (denoteHist p) (denoteHist c) h`,
   plus preservation of `ValidHistEntries`.
4. Three executable boundary regressions:
   - double empty input → single empty histogram `[[]]`;
   - all pairings forbidden with positive demand → empty output list `[]`;
   - collision example `p = [(true, 0):1, (true, 1):1]`, `c = [(true, 1):1, (false, 0):1]`
     producing both `{(true, 1):2}` (multiplicity 2 merged!) and `{(true, 0):1, (true, 2):1}`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

section ExecDefinitions

abbrev HistEntries := List (JointType × ℕ)

/-- Semantic `OrbitHist` denoted by a `(JointType × ℕ)` entry list. -/
def denoteHist : HistEntries → OrbitHist
  | [] => 0
  | (t, k) :: rest => Multiset.replicate k t + denoteHist rest

/-- Validity of an entry list: no duplicate joint types, and every multiplicity is positive. -/
def ValidHistEntries (e : HistEntries) : Prop :=
  (e.map Prod.fst).Nodup ∧ ∀ kv ∈ e, 0 < kv.2

/-- Insert `n` copies of `t` into an entry list, merging multiplicities on matching keys
and skipping `n = 0`. -/
def addEntry (t : JointType) (n : ℕ) : HistEntries → HistEntries
  | [] => if n = 0 then [] else [(t, n)]
  | (t', k) :: rest =>
    if t = t' then (t', k + n) :: rest
    else (t', k) :: addEntry t n rest

/-- Accumulate one row of a transport table into an entry list directly by multiplicity. -/
def addRowEntries (a : JointType) : List JointType → List ℕ → HistEntries → HistEntries
  | [], _, acc => acc
  | _, [], acc => acc
  | b :: bs, n :: ns, acc =>
    addRowEntries a bs ns (if n = 0 then acc else addEntry (g_in a b) n acc)

/-- Accumulate all rows of a transport table into an entry list directly by multiplicity. -/
def tableToEntries (bs : List JointType) :
    List JointType → List (List ℕ) → HistEntries → HistEntries
  | [], _, acc => acc
  | _, [], acc => acc
  | a :: as, row :: rows, acc =>
    tableToEntries bs as rows (addRowEntries a bs row acc)

/-- Enumerate all legal raw transport tables for `(p, c)`. -/
def histJoinTables (p c : HistEntries) : List (List (List ℕ)) :=
  tableChoices K_in_bool (c.map Prod.fst) p (c.map Prod.snd)

/-- Executable internal histogram join: maps each enumerated table to its merged entry list. -/
def histJoinExec (p c : HistEntries) : List HistEntries :=
  (histJoinTables p c).map fun M =>
    tableToEntries (c.map Prod.fst) (p.map Prod.fst) M []

end ExecDefinitions

section DenotationAndValidity

@[simp] theorem denoteHist_nil : denoteHist [] = 0 := rfl

@[simp] theorem denoteHist_cons (t : JointType) (k : ℕ) (rest : HistEntries) :
    denoteHist ((t, k) :: rest) = Multiset.replicate k t + denoteHist rest := rfl

theorem denoteHist_addEntry (t : JointType) (n : ℕ) (e : HistEntries) :
    denoteHist (addEntry t n e) = Multiset.replicate n t + denoteHist e := by
  induction e with
  | nil =>
    unfold addEntry
    split_ifs with hn
    · subst hn; simp
    · simp
  | cons kv rest ih =>
    rcases kv with ⟨t', k⟩
    unfold addEntry
    split_ifs with ht
    · subst ht
      simp only [denoteHist_cons, Multiset.replicate_add]
      ac_rfl
    · simp only [denoteHist_cons, ih]
      ac_rfl

theorem mem_map_fst_addEntry (t : JointType) (n : ℕ) (e : HistEntries) (x : JointType) :
    x ∈ (addEntry t n e).map Prod.fst → x = t ∨ x ∈ e.map Prod.fst := by
  induction e with
  | nil =>
    unfold addEntry
    split_ifs <;> simp
  | cons kv rest ih =>
    rcases kv with ⟨t', k⟩
    unfold addEntry
    split_ifs with ht
    · intro hx; exact Or.inr hx
    · simp only [List.map_cons, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · rcases ih hx with rfl | hrest
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hrest)

theorem validHistEntries_addEntry (t : JointType) (n : ℕ) (e : HistEntries)
    (he : ValidHistEntries e) : ValidHistEntries (addEntry t n e) := by
  induction e with
  | nil =>
    unfold addEntry
    split_ifs with hn
    · exact ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩
    · refine ⟨List.nodup_singleton t, ?_⟩
      intro kv hkv
      simp only [List.mem_singleton] at hkv
      subst hkv
      exact Nat.pos_of_ne_zero hn
  | cons kv rest ih =>
    rcases kv with ⟨t', k⟩
    rcases he with ⟨hnodup, hpos⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨ht'not, hrestNodup⟩
    have hrestValid : ValidHistEntries rest :=
      ⟨hrestNodup, fun kv' hkv' => hpos kv' (List.mem_cons_of_mem _ hkv')⟩
    unfold addEntry
    split_ifs with ht
    · refine ⟨by simp [ht'not, hrestNodup], ?_⟩
      intro kv' hkv'
      rcases List.mem_cons.mp hkv' with rfl | hmem
      · have hk : 0 < k := hpos (t', k) (List.mem_cons_self ..)
        omega
      · exact hpos kv' (List.mem_cons_of_mem _ hmem)
    · obtain ⟨hN', hP'⟩ := ih hrestValid
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hN'⟩
        intro hin
        rcases mem_map_fst_addEntry t n rest t' hin with rfl | hmem
        · exact ht rfl
        · exact ht'not hmem
      · intro kv' hkv'
        rcases List.mem_cons.mp hkv' with rfl | hmem
        · exact hpos (t', k) (List.mem_cons_self ..)
        · exact hP' kv' hmem

theorem validHistEntries_addRowEntries (a : JointType) (bs : List JointType)
    (row : List ℕ) (acc : HistEntries) (hacc : ValidHistEntries acc) :
    ValidHistEntries (addRowEntries a bs row acc) := by
  induction bs generalizing row acc with
  | nil => exact hacc
  | cons b bs ih =>
    cases row with
    | nil => exact hacc
    | cons n ns =>
      unfold addRowEntries
      split_ifs
      · exact ih ns acc hacc
      · exact ih ns (addEntry (g_in a b) n acc) (validHistEntries_addEntry (g_in a b) n acc hacc)

theorem validHistEntries_tableToEntries (bs as : List JointType)
    (M : List (List ℕ)) (acc : HistEntries) (hacc : ValidHistEntries acc) :
    ValidHistEntries (tableToEntries bs as M acc) := by
  induction as generalizing M acc with
  | nil => exact hacc
  | cons a as ih =>
    cases M with
    | nil => exact hacc
    | cons row rows =>
      exact ih rows (addRowEntries a bs row acc)
        (validHistEntries_addRowEntries a bs row acc hacc)

/-- Every output entry list emitted by `histJoinExec` has distinct keys and positive counts. -/
theorem validHistEntries_of_mem_histJoinExec (p c out : HistEntries)
    (hout : out ∈ histJoinExec p c) : ValidHistEntries out := by
  unfold histJoinExec at hout
  rcases List.mem_map.mp hout with ⟨M, _, rfl⟩
  exact validHistEntries_tableToEntries (c.map Prod.fst) (p.map Prod.fst) M []
    ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩

theorem denoteHist_toFinset (e : HistEntries) (he : ValidHistEntries e) :
    (denoteHist e).toFinset = (e.map Prod.fst).toFinset := by
  induction e with
  | nil => simp
  | cons kv rest ih =>
    rcases kv with ⟨t, k⟩
    rcases he with ⟨hnodup, hpos⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    have hk : 0 < k := hpos (t, k) (List.mem_cons_self ..)
    have hrest : ValidHistEntries rest :=
      ⟨hnodup.2, fun kv' hkv' => hpos kv' (List.mem_cons_of_mem _ hkv')⟩
    ext x
    simp only [denoteHist_cons, Multiset.mem_toFinset, Multiset.mem_add, Multiset.mem_replicate,
      List.map_cons, List.toFinset_cons, Finset.mem_insert, ← ih hrest, ne_eq,
      Nat.ne_of_gt hk, not_false_eq_true, true_and]

theorem denoteHist_count_eq_zero_of_not_mem (e : HistEntries) (t : JointType)
    (hnot : t ∉ e.map Prod.fst) : (denoteHist e).count t = 0 := by
  induction e with
  | nil => simp
  | cons kv rest ih =>
    rcases kv with ⟨t', k⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [denoteHist_cons, Multiset.count_add, Multiset.count_replicate,
      if_neg (Ne.symm hnot.1), zero_add]
    exact ih hnot.2

theorem denoteHist_count_of_mem (e : HistEntries) (hnodup : (e.map Prod.fst).Nodup)
    (kv : JointType × ℕ) (hmem : kv ∈ e) :
    (denoteHist e).count kv.1 = kv.2 := by
  induction e with
  | nil => exact (List.not_mem_nil hmem).elim
  | cons kv' rest ih =>
    rcases kv' with ⟨t', k'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp only [denoteHist_cons, Multiset.count_add, Multiset.count_replicate_self,
        denoteHist_count_eq_zero_of_not_mem rest t' hnodup.1, add_zero]
    · have hne : t' ≠ kv.1 := fun h => hnodup.1 (h ▸ List.mem_map.mpr ⟨kv, hrest, rfl⟩)
      simp only [denoteHist_cons, Multiset.count_add, Multiset.count_replicate,
        if_neg hne, zero_add]
      exact ih hnodup.2 hrest

theorem denoteHist_count_getElem (e : HistEntries) (hnodup : (e.map Prod.fst).Nodup)
    (j : ℕ) (hj : j < e.length) :
    (denoteHist e).count (e[j]).1 = (e[j]).2 :=
  denoteHist_count_of_mem e hnodup e[j] (List.getElem_mem hj)

end DenotationAndValidity

section PushforwardAndMembership

theorem count_denoteHist_addRowEntries (a : JointType) (bs : List JointType)
    (row : List ℕ) (acc : HistEntries) (hlen : row.length = bs.length) (t : JointType) :
    (denoteHist (addRowEntries a bs row acc)).count t =
      (List.zipWith (fun b n => if g_in a b = t then n else 0) bs row).sum +
        (denoteHist acc).count t := by
  induction bs generalizing row acc with
  | nil =>
    cases row with
    | nil => simp [addRowEntries]
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases row with
    | nil => simp at hlen
    | cons n ns =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      unfold addRowEntries
      rw [ih ns _ hlen]
      simp only [List.zipWith_cons_cons, List.sum_cons]
      by_cases hn : n = 0
      · subst hn; simp
      · simp only [if_neg hn, denoteHist_addEntry, Multiset.count_add, Multiset.count_replicate]
        by_cases hg : g_in a b = t
        · simp [hg]; omega
        · simp [hg]

theorem count_denoteHist_tableToEntries (bs as : List JointType)
    (M : List (List ℕ)) (acc : HistEntries)
    (hlenM : M.length = as.length)
    (hlenRow : ∀ row ∈ M, row.length = bs.length) (t : JointType) :
    (denoteHist (tableToEntries bs as M acc)).count t =
      (List.zipWith (fun a row =>
        (List.zipWith (fun b n => if g_in a b = t then n else 0) bs row).sum) as M).sum +
        (denoteHist acc).count t := by
  induction as generalizing M acc with
  | nil =>
    cases M with
    | nil => simp [tableToEntries]
    | cons _ _ => simp at hlenM
  | cons a as ih =>
    cases M with
    | nil => simp at hlenM
    | cons row rows =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenM
      have hrow : row.length = bs.length := hlenRow row (List.mem_cons_self ..)
      have hrows : ∀ r ∈ rows, r.length = bs.length :=
        fun r hr => hlenRow r (List.mem_cons_of_mem _ hr)
      unfold tableToEntries
      rw [ih rows (addRowEntries a bs row acc) hlenM hrows,
        count_denoteHist_addRowEntries a bs row acc hrow t]
      simp only [List.zipWith_cons_cons, List.sum_cons]
      omega

theorem zipWith_attach_sum {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (f : l.toFinset → ℕ) (g : α → ℕ → ℕ) :
    (List.zipWith g l (l.attach.map fun x => f ⟨x.1, List.mem_toFinset.mpr x.2⟩)).sum =
      ∑ x : l.toFinset, g x.1 (f x) := by
  have hzip :
      List.zipWith g l (l.attach.map fun x => f ⟨x.1, List.mem_toFinset.mpr x.2⟩) =
        l.attach.map fun x => g x.1 (f ⟨x.1, List.mem_toFinset.mpr x.2⟩) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp
  rw [hzip]
  exact sum_attach_eq_finset_sum l hl (fun x => g x.1 (f x))

theorem denoteHist_tableToEntries_encodeTable
    (as bs : List JointType) (has : as.Nodup) (hbs : bs.Nodup)
    (N : as.toFinset → bs.toFinset → ℕ) :
    denoteHist (tableToEntries bs as (encodeTable as bs N) []) =
      tablePushforwardHist N := by
  rw [Multiset.ext]
  intro t
  have hlenM : (encodeTable as bs N).length = as.length := by simp [encodeTable]
  have hlenRow : ∀ row ∈ encodeTable as bs N, row.length = bs.length := by
    intro row hrow
    unfold encodeTable at hrow
    rcases List.mem_map.mp hrow with ⟨a, _, rfl⟩
    simp
  rw [count_denoteHist_tableToEntries bs as (encodeTable as bs N) [] hlenM hlenRow t,
    denoteHist_nil, Multiset.count_zero, add_zero, count_tablePushforwardHist]
  unfold encodeTable
  have hzipA :
      List.zipWith (fun a row =>
        (List.zipWith (fun b n => if g_in a b = t then n else 0) bs row).sum)
        as
        (as.attach.map fun a => bs.attach.map fun b =>
          N ⟨a.1, List.mem_toFinset.mpr a.2⟩ ⟨b.1, List.mem_toFinset.mpr b.2⟩) =
      as.attach.map fun a =>
        ∑ b : bs.toFinset, if g_in a.1 b.1 = t then N ⟨a.1, List.mem_toFinset.mpr a.2⟩ b else 0 := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      have hiAs : i < as.length := by simpa using hi2
      simp only [List.getElem_zipWith, List.getElem_map, List.getElem_attach]
      exact zipWith_attach_sum bs hbs
        (fun b => N ⟨as[i], List.mem_toFinset.mpr (List.getElem_mem hiAs)⟩ b)
        (fun b n => if g_in as[i] b = t then n else 0)
  rw [hzipA]
  exact sum_attach_eq_finset_sum as has
    (fun a => ∑ b : bs.toFinset, if g_in a.1 b.1 = t then N a b else 0)

/-- Decode a raw matrix `M` back to a table `N : as.toFinset → bs.toFinset → ℕ`. -/
def decodeTable (as bs : List JointType) (M : List (List ℕ)) :
    as.toFinset → bs.toFinset → ℕ :=
  fun a b => (M.getD (as.idxOf a.1) []).getD (bs.idxOf b.1) 0

theorem encodeTable_decodeTable (as bs : List JointType) (has : as.Nodup) (hbs : bs.Nodup)
    (M : List (List ℕ)) (hlenM : M.length = as.length)
    (hlenRow : ∀ row ∈ M, row.length = bs.length) :
    encodeTable as bs (decodeTable as bs M) = M := by
  apply List.ext_getElem
  · simp [encodeTable, hlenM]
  · intro i hi1 hi2
    have hiAs : i < as.length := by simpa [encodeTable] using hi1
    simp only [encodeTable, List.getElem_map, List.getElem_attach]
    apply List.ext_getElem
    · simp [hlenRow M[i] (List.getElem_mem hi2)]
    · intro j hj1 hj2
      have hjBs : j < bs.length := by simpa using hj1
      simp only [List.getElem_map, List.getElem_attach, decodeTable]
      have hI : as.idxOf as[i] = i := has.idxOf_getElem i hiAs
      have hJ : bs.idxOf bs[j] = j := hbs.idxOf_getElem j hjBs
      calc
        (M.getD (as.idxOf as[i]) []).getD (bs.idxOf bs[j]) 0
            = (M.getD i []).getD j 0 := by simp [hI, hJ]
        _ = M[i][j] := by rw [List.getD_eq_getElem _ _ hi2, List.getD_eq_getElem _ _ hj2]

/-- Auxiliary equivalence between `encodeTable ∈ histJoinTables p c` and `HistJoinOn`
over `(p.map Prod.fst).toFinset` and `(c.map Prod.fst).toFinset`. -/
theorem encodeTable_mem_histJoinTables_iff
    (p c : HistEntries) (hp : ValidHistEntries p) (hc : ValidHistEntries c)
    (N : (p.map Prod.fst).toFinset → (c.map Prod.fst).toFinset → ℕ) :
    encodeTable (p.map Prod.fst) (c.map Prod.fst) N ∈ histJoinTables p c ↔
      (∀ a : (p.map Prod.fst).toFinset,
        (∑ b : (c.map Prod.fst).toFinset, N a b) = (denoteHist p).count a.1) ∧
      (∀ b : (c.map Prod.fst).toFinset,
        (∑ a : (p.map Prod.fst).toFinset, N a b) = (denoteHist c).count b.1) ∧
      (∀ (a : (p.map Prod.fst).toFinset) (b : (c.map Prod.fst).toFinset),
        ¬ K_in a.1 b.1 → N a b = 0) := by
  let as := p.map Prod.fst
  let bs := c.map Prod.fst
  have has : as.Nodup := hp.1
  have hbs : bs.Nodup := hc.1
  unfold histJoinTables
  have hlen : (c.map Prod.snd).length = bs.length := by simp [bs]
  rw [mem_tableChoices_iff K_in_bool bs p (c.map Prod.snd) hlen (encodeTable as bs N)]
  have hForall₂ :
      List.Forall₂ (fun row kv =>
        row.length = bs.length ∧
        row.sum = kv.2 ∧
        ∀ j (hj : j < bs.length), K_in_bool kv.1 bs[j] = false → row.getD j 0 = 0)
        (encodeTable as bs N) p ↔
      (∀ a : as.toFinset, (∑ b : bs.toFinset, N a b) = (denoteHist p).count a.1) ∧
      (∀ (a : as.toFinset) (b : bs.toFinset), ¬ K_in a.1 b.1 → N a b = 0) := by
    unfold encodeTable
    have hmapL :
        (as.attach.map fun a => bs.attach.map fun b =>
          N ⟨a.1, List.mem_toFinset.mpr a.2⟩ ⟨b.1, List.mem_toFinset.mpr b.2⟩) =
        p.attach.map fun kv => bs.attach.map fun b =>
          N ⟨kv.1.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨kv.1, kv.2, rfl⟩)⟩
            ⟨b.1, List.mem_toFinset.mpr b.2⟩ := by
      apply List.ext_getElem
      · simp [as]
      · intro i hi1 hi2
        simp [as]
    rw [hmapL, List.forall₂_map_left_iff]
    have hattach : ∀ (P : {kv // kv ∈ p} → JointType × ℕ → Prop),
        List.Forall₂ P p.attach p ↔ ∀ kv : {kv // kv ∈ p}, P kv kv.1 := by
      intro P
      have hsub : p = p.attach.map Subtype.val := by
        apply List.ext_getElem <;> simp
      conv_lhs => rhs; rw [hsub]
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      constructor
      · intro h kv; exact h kv (List.mem_attach p kv)
      · intro h kv _; exact h kv
    rw [hattach]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro ⟨a, ha⟩
        have ha' : a ∈ as := List.mem_toFinset.mp ha
        rcases List.mem_map.mp ha' with ⟨kv, hkv, rfl⟩
        have h1 := (h ⟨kv, hkv⟩).2.1
        rw [sum_attach_eq_finset_sum bs hbs (fun b => N ⟨kv.1, ha⟩ b)] at h1
        rw [h1, denoteHist_count_of_mem p has kv hkv]
      · intro ⟨a, ha⟩ ⟨b, hb⟩ hnotK
        have ha' : a ∈ as := List.mem_toFinset.mp ha
        rcases List.mem_map.mp ha' with ⟨kv, hkv, rfl⟩
        have hb' : b ∈ bs := List.mem_toFinset.mp hb
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
        have hKfalse : K_in_bool kv.1 bs[j] = false :=
          Bool.eq_false_iff.mpr (mt (K_in_bool_iff kv.1 bs[j]).mp hnotK)
        have h2 := (h ⟨kv, hkv⟩).2.2 j hj hKfalse
        rw [getD_map_attach bs _ j hj] at h2
        exact h2
    · rintro ⟨hrow, hforb⟩ ⟨kv, hkv⟩
      have ha : kv.1 ∈ as.toFinset := List.mem_toFinset.mpr (List.mem_map.mpr ⟨kv, hkv, rfl⟩)
      refine ⟨by simp, ?_, ?_⟩
      · rw [sum_attach_eq_finset_sum bs hbs (fun b => N ⟨kv.1, ha⟩ b),
          hrow ⟨kv.1, ha⟩, denoteHist_count_of_mem p has kv hkv]
      · intro j hj hKfalse
        rw [getD_map_attach bs _ j hj]
        apply hforb ⟨kv.1, ha⟩ ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩
        intro hK
        have := (K_in_bool_iff kv.1 bs[j]).mpr hK
        rw [hKfalse] at this
        exact Bool.false_ne_true this
  have hCol :
      (∀ j, j < bs.length →
        colSum (encodeTable as bs N) j = (c.map Prod.snd).getD j 0) ↔
      (∀ b : bs.toFinset, (∑ a : as.toFinset, N a b) = (denoteHist c).count b.1) := by
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
      have hjc : j < c.length := by simpa [bs] using hj
      have h1 := h j hj
      rw [hcolAt j hj] at h1
      have hj' : j < (c.map Prod.snd).length := by simpa using hjc
      rw [List.getD_eq_getElem _ _ hj'] at h1
      have h1' : (∑ a : as.toFinset, N a ⟨bs[j], hb⟩) = (c)[j].2 := by
        simpa [List.getElem_map] using h1
      have hbsj : bs[j] = (c)[j].1 := List.getElem_map Prod.fst (i := j) (h := hj)
      have h2 := denoteHist_count_getElem c hbs j hjc
      rw [h1', ← h2]
      exact congrArg (fun x => (denoteHist c).count x) hbsj.symm
    · intro h j hj
      have hjc : j < c.length := by simpa [bs] using hj
      rw [hcolAt j hj]
      have hj' : j < (c.map Prod.snd).length := by simpa using hjc
      rw [List.getD_eq_getElem _ _ hj']
      simp only [List.getElem_map]
      have h1 := h ⟨bs[j], List.mem_toFinset.mpr (List.getElem_mem hj)⟩
      have hbsj : bs[j] = (c)[j].1 := List.getElem_map Prod.fst (i := j) (h := hj)
      have h2 := denoteHist_count_getElem c hbs j hjc
      exact h1.trans ((congrArg (fun x => (denoteHist c).count x) hbsj).trans h2)
  rw [hForall₂, hCol]
  tauto

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => intro _ ha; exact (List.not_mem_nil ha).elim
  | cons hab _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hR⟩ := ih x hrest
      exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

/-- Main C3 Executable Join Membership Theorem:
Under distinct keys and positive multiplicities on both sides, a target histogram `h` is
denoted by some output of `histJoinExec p c` iff `HistJoin (denoteHist p) (denoteHist c) h`. -/
theorem exists_mem_histJoinExec_iff_histJoin
    (p c : HistEntries) (hp : ValidHistEntries p) (hc : ValidHistEntries c)
    (h : OrbitHist) :
    (∃ out ∈ histJoinExec p c, denoteHist out = h) ↔
      HistJoin (denoteHist p) (denoteHist c) h := by
  unfold HistJoin
  rw [denoteHist_toFinset p hp, denoteHist_toFinset c hc]
  let as := p.map Prod.fst
  let bs := c.map Prod.fst
  constructor
  · rintro ⟨out, hout, rfl⟩
    unfold histJoinExec at hout
    rcases List.mem_map.mp hout with ⟨M, hM, rfl⟩
    have hlen : (c.map Prod.snd).length = bs.length := by simp [bs]
    have hMspec := (mem_tableChoices_iff K_in_bool bs p (c.map Prod.snd) hlen M).mp hM
    have hlenM : M.length = as.length := by
      have := hMspec.1.length_eq
      simpa [as] using this
    have hlenRow : ∀ row ∈ M, row.length = bs.length := by
      intro row hrow
      obtain ⟨kv, _, hspec⟩ := forall₂_mem_left hMspec.1 row hrow
      exact hspec.1
    let N : as.toFinset → bs.toFinset → ℕ := decodeTable as bs M
    have hEnc : encodeTable as bs N = M :=
      encodeTable_decodeTable as bs hp.1 hc.1 M hlenM hlenRow
    have hM' : encodeTable as bs N ∈ histJoinTables p c := hEnc.symm ▸ hM
    obtain ⟨hrow, hcol, hforb⟩ := (encodeTable_mem_histJoinTables_iff p c hp hc N).mp hM'
    refine ⟨N, hrow, hcol, hforb, ?_⟩
    rw [← hEnc, denoteHist_tableToEntries_encodeTable as bs hp.1 hc.1 N]
  · rintro ⟨N, hrow, hcol, hforb, hpush⟩
    have hM : encodeTable as bs N ∈ histJoinTables p c :=
      (encodeTable_mem_histJoinTables_iff p c hp hc N).mpr ⟨hrow, hcol, hforb⟩
    refine ⟨tableToEntries bs as (encodeTable as bs N) [], ?_, ?_⟩
    · exact List.mem_map.mpr ⟨encodeTable as bs N, hM, rfl⟩
    · rw [denoteHist_tableToEntries_encodeTable as bs hp.1 hc.1 N, hpush]

end PushforwardAndMembership

section BoundaryRegressions

/-! ### Boundary 1: Double empty input produces a single empty histogram `[[]]` -/

theorem exExec_double_empty :
    histJoinExec [] [] = [[]] := by
  decide

theorem exExec_double_empty_histJoin :
    HistJoin (denoteHist []) (denoteHist []) 0 := by
  apply (exists_mem_histJoinExec_iff_histJoin [] []
    ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩
    ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩ 0).mp
  refine ⟨[], ?_, rfl⟩
  rw [exExec_double_empty]
  simp

/-! ### Boundary 2: All pairings forbidden with positive demand produces `[]` -/

def exForb_p : HistEntries := [((false, (0 : ℚ)), 1)]
def exForb_c : HistEntries := [((true, (1 : ℚ)), 1)]

theorem exExec_all_forbidden :
    histJoinExec exForb_p exForb_c = [] := by
  decide

theorem exExec_all_forbidden_not_histJoin (h : OrbitHist) :
    ¬ HistJoin (denoteHist exForb_p) (denoteHist exForb_c) h := by
  rw [← exists_mem_histJoinExec_iff_histJoin exForb_p exForb_c
    ⟨by decide, by intro kv hkv; simp [exForb_p] at hkv; subst hkv; omega⟩
    ⟨by decide, by intro kv hkv; simp [exForb_c] at hkv; subst hkv; omega⟩ h]
  rw [exExec_all_forbidden]
  simp

/-! ### Boundary 3: Collision example distinguishing `{1, 1}` (merged multiplicity 2) and `{0, 2}` -/

def exColl_p : HistEntries := [((true, (0 : ℚ)), 1), ((true, (1 : ℚ)), 1)]
def exColl_c : HistEntries := [((true, (1 : ℚ)), 1), ((false, (0 : ℚ)), 1)]

/-- Exact executable output of `histJoinExec exColl_p exColl_c`:
two distinct histograms, one with `(true, 0):1` and `(true, 2):1`, and one with
`(true, 1)` merged to multiplicity `2`. -/
theorem exExec_collision_exact :
    histJoinExec exColl_p exColl_c =
      [[((true, (0 : ℚ)), 1), ((true, (2 : ℚ)), 1)],
       [((true, (1 : ℚ)), 2)]] := by
  have htab : histJoinTables exColl_p exColl_c = [[[0, 1], [1, 0]], [[1, 0], [0, 1]]] := by
    decide
  unfold histJoinExec
  rw [htab]
  simp [exColl_p, exColl_c, tableToEntries, addRowEntries, addEntry, g_in]
  norm_num

theorem exExec_collision_merged_mult_two :
    [((true, (1 : ℚ)), 2)] ∈ histJoinExec exColl_p exColl_c ∧
    [((true, (0 : ℚ)), 1), ((true, (2 : ℚ)), 1)] ∈ histJoinExec exColl_p exColl_c := by
  rw [exExec_collision_exact]
  simp

theorem exExec_collision_both_histJoin :
    HistJoin (denoteHist exColl_p) (denoteHist exColl_c) (Multiset.replicate 2 (true, (1 : ℚ))) ∧
    HistJoin (denoteHist exColl_p) (denoteHist exColl_c)
      (Multiset.replicate 1 (true, (0 : ℚ)) + Multiset.replicate 1 (true, (2 : ℚ))) := by
  have hp : ValidHistEntries exColl_p := by
    refine ⟨by decide, ?_⟩
    intro kv hkv
    simp only [exColl_p, List.mem_cons, List.not_mem_nil, or_false] at hkv
    rcases hkv with rfl | rfl <;> omega
  have hc : ValidHistEntries exColl_c := by
    refine ⟨by decide, ?_⟩
    intro kv hkv
    simp only [exColl_c, List.mem_cons, List.not_mem_nil, or_false] at hkv
    rcases hkv with rfl | rfl <;> omega
  obtain ⟨h1, h2⟩ := exExec_collision_merged_mult_two
  constructor
  · exact (exists_mem_histJoinExec_iff_histJoin exColl_p exColl_c hp hc _).mp
      ⟨[((true, (1 : ℚ)), 2)], h1, by simp [denoteHist]⟩
  · exact (exists_mem_histJoinExec_iff_histJoin exColl_p exColl_c hp hc _).mp
      ⟨[((true, (0 : ℚ)), 1), ((true, (2 : ℚ)), 1)], h2, by simp [denoteHist]⟩

end BoundaryRegressions

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.validHistEntries_of_mem_histJoinExec
#print axioms UAVProof.TreeBudgetOrbitPrototype.exists_mem_histJoinExec_iff_histJoin
#print axioms UAVProof.TreeBudgetOrbitPrototype.exExec_double_empty
#print axioms UAVProof.TreeBudgetOrbitPrototype.exExec_all_forbidden
#print axioms UAVProof.TreeBudgetOrbitPrototype.exExec_collision_exact
#print axioms UAVProof.TreeBudgetOrbitPrototype.exExec_collision_both_histJoin
