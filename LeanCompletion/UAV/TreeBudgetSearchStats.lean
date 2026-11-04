import LeanCompletion.UAV.TreeBudgetMemoSearch

/-! Operation counts for the existing ordered searches. Counts are logical operations,
not elapsed time or bit costs. Instrumentation itself is excluded from timed runs. -/
namespace UAVProof.TreeBudgetSearchStats
open TreeFlowExistence TreeBudgetResidualSearch TreeBudgetMemoState TreeBudgetMemoSearch
variable {n : ℕ}

structure Counts where
  calls : ℕ := 0
  hits : ℕ := 0
  expansions : ℕ := 0
  candidates : ℕ := 0
  lookupComparisons : ℕ := 0
  insertionScans : ℕ := 0
  deriving Repr, DecidableEq

def Counts.add (a b : Counts) : Counts :=
  ⟨a.calls + b.calls, a.hits + b.hits, a.expansions + b.expansions,
    a.candidates + b.candidates, a.lookupComparisons + b.lookupComparisons,
    a.insertionScans + b.insertionScans⟩

abbrev Measured (α : Type) := α × Counts

def bump {α : Type} (c : Counts) (out : Measured α) : Measured α :=
  (out.1, c.add out.2)

@[simp] theorem bump_erase {α : Type} (c : Counts) (out : Measured α) :
    (bump c out).1 = out.1 := rfl

/-- One comparison per visited association-list entry, including the matching entry. -/
def lookupStat : Cache n → Key n → Option (Answer n) × ℕ
  | [], _ => (none, 0)
  | e :: cs, q => if e.1 = q then (some e.2, 1) else
      let out := lookupStat cs q
      (out.1, out.2 + 1)

@[simp] theorem lookupStat_erase (cs : Cache n) (q : Key n) :
    (lookupStat cs q).1 = lookup cs q := by
  induction cs with
  | nil => rfl
  | cons e cs ih => simp only [lookupStat, lookup]; split <;> simp_all

/-- `insert` filters every old entry once, even if the key was absent. -/
def insertStat (cs : Cache n) (q : Key n) (a : Answer n) : Measured (Cache n) :=
  (insert cs q a, { insertionScans := cs.length })

@[simp] theorem insertStat_erase (cs : Cache n) (q : Key n) (a : Answer n) :
    (insertStat cs q a).1 = insert cs q a := rfl

/-- Logical retained suffix rows; shared heap tails are counted with multiplicity.
This is neither allocated bytes nor a peak-memory measurement. -/
def witnessRows (cs : Cache n) : ℕ :=
  (cs.map fun e => (e.2.getD []).length).sum

def scanStat (solve : (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n))
    (r : Fin n → ℕ) : List (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n)
  | [], cs => ((none, cs), {})
  | p :: ps, cs => bump { candidates := 1 } <|
    if ∀ v, p v ≤ r v then
      let out := solve (r - p) cs
      match out.1.1 with
      | some rows => ((some (p :: rows), out.1.2), out.2)
      | none => bump out.2 (scanStat solve r ps out.1.2)
    else scanStat solve r ps cs

theorem scanStat_erase
    (solve : (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n))
    (base : (Fin n → ℕ) → Cache n → Answer n × Cache n)
    (h : ∀ r cs, (solve r cs).1 = base r cs)
    (r : Fin n → ℕ) (ps : List (Fin n → ℕ)) (cs : Cache n) :
    (scanStat solve r ps cs).1 = scanCandidates base r ps cs := by
  induction ps generalizing cs with
  | nil => rfl
  | cons p ps ih =>
    simp only [scanStat, bump_erase, scanCandidates]
    split_ifs with hp
    · simp only [h]
      cases (base (r - p) cs).1 <;> simp [bump, ih]
    · exact ih cs

def memoStat (ps : List (Fin n → ℕ)) :
    ℕ → (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n)
  | k, r, cs =>
    let found := lookupStat cs (k, r)
    match found.1 with
    | some a => ((a, cs), { calls := 1, hits := 1, lookupComparisons := found.2 })
    | none =>
      let out := match k with
        | 0 => ((if r = 0 then some [] else none, cs), ({} : Counts))
        | j + 1 => scanStat (memoStat ps j) r ps cs
      let saved := insertStat out.1.2 (k, r) out.1.1
      ((out.1.1, saved.1),
        (Counts.add { calls := 1, expansions := 1, lookupComparisons := found.2 }
          out.2).add saved.2)

/-- Exact answer AND cache equality, for arbitrary candidate lists and raw caches. -/
theorem memoStat_erase (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ)
    (cs : Cache n) : (memoStat ps k r cs).1 = memoRowsWith ps k r cs := by
  induction k generalizing r cs with
  | zero =>
    cases he : lookup cs (0, r) <;>
      simp [memoStat, lookupStat_erase, he, memoRowsWith, insertStat]
  | succ k ih =>
    cases he : lookup cs (k + 1, r) <;>
      simp [memoStat, lookupStat_erase, he, memoRowsWith, insertStat, scanStat_erase _ _ ih]

def memoRowsStat (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ)
    (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :=
  memoStat (TreeBudgetFiniteSearch.candidates R H s T) k r cs

theorem memoRowsStat_erase (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ)
    (T : ℚ) (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoRowsStat R H s T k r cs).1 = memoRows R H s T k r cs := memoStat_erase ..

def firstStat {α β : Type} (f : α → Measured (Option β)) :
    List α → Measured (Option β)
  | [] => (none, {})
  | p :: ps => bump { candidates := 1 } <|
      let out := f p
      match out.1 with
      | some a => (some a, out.2)
      | none => bump out.2 (firstStat f ps)

theorem firstStat_erase {α β : Type} (f : α → Measured (Option β)) (ps : List α) :
    (firstStat f ps).1 = firstSuccess (fun p => (f p).1) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [firstStat, bump_erase, firstSuccess]
    cases (f p).1 <;> simp [bump, ih]

/-- Every uncached call expands. There are no cache misses/lookups in this mode;
`expansions` is the common comparable quantity, and may revisit the same state. -/
def searchStat (ps : List (Fin n → ℕ)) : ℕ → (Fin n → ℕ) → Measured (Answer n)
  | 0, r => (if r = 0 then some [] else none, { calls := 1, expansions := 1 })
  | k + 1, r => bump { calls := 1, expansions := 1 } <|
      firstStat (fun p => if ∀ v, p v ≤ r v then
        let out := searchStat ps k (r - p)
        (out.1.map (p :: ·), out.2)
        else (none, {})) ps

theorem searchStat_erase (ps : List (Fin n → ℕ)) (k : ℕ) (r : Fin n → ℕ) :
    (searchStat ps k r).1 = searchRowsWith ps k r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    simp only [searchStat, bump_erase, firstStat_erase, searchRowsWith]
    congr 1
    funext p
    split_ifs <;> simp [ih]

theorem searchRowsStat_erase (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ)
    (T : ℚ) (k : ℕ) (r : Fin n → ℕ) :
    (searchStat (TreeBudgetFiniteSearch.candidates R H s T) k r).1 =
      searchRows R H s T k r := searchStat_erase ..

end UAVProof.TreeBudgetSearchStats

#print axioms UAVProof.TreeBudgetSearchStats.bump_erase
#print axioms UAVProof.TreeBudgetSearchStats.lookupStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.insertStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.scanStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.memoStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.memoRowsStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.firstStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.searchStat_erase
#print axioms UAVProof.TreeBudgetSearchStats.searchRowsStat_erase
