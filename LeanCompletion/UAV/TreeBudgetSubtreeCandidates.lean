import LeanCompletion.UAV.TreeBudgetSubtreeExecutable

/-! Exact column-sum enumeration. These are local columns, not complete-route
candidates; only root children receive a top-edge cap. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState
variable {N m : ℕ}

def emptyV : Vector ℕ 0 := Vector.ofFn Fin.elim0
def consV (a : ℕ) (q : Vector ℕ m) : Vector ℕ (m + 1) :=
  Vector.ofFn (Fin.cons a (val q))
def tailV (q : Vector ℕ (m + 1)) : Vector ℕ m := Vector.ofFn fun i => val q i.succ

@[simp] theorem val_consV (a : ℕ) (q : Vector ℕ m) :
    val (consV a q) = Fin.cons a (val q) := by funext i; simp [consV]

@[simp] theorem val_tailV (q : Vector ℕ (m + 1)) (i : Fin m) :
    val (tailV q) i = val q i.succ := by simp [tailV]

theorem cons_tailV (q : Vector ℕ (m + 1)) : consV (val q 0) (tailV q) = q := by
  apply vector_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def compositionsV : (m : ℕ) → ℕ → List (Vector ℕ m)
  | 0, h => if h = 0 then [emptyV] else []
  | m + 1, h => (List.range (h + 1)).flatMap fun a =>
      (compositionsV m (h - a)).map (consV a)

theorem compositionsV_spec (m h : ℕ) (q : Vector ℕ m) :
    q ∈ compositionsV m h ↔ (∑ i, val q i) = h := by
  induction m generalizing h with
  | zero =>
    have he : q = emptyV := vector_ext (fun i => Fin.elim0 i)
    subst q
    simp [compositionsV, eq_comm]
  | succ m ih =>
    simp only [compositionsV, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      have hs := (ih (h - a) t).mp ht
      simp only [val_consV, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega
    · intro hq
      have hs : val q 0 + ∑ i, val (tailV q) i = h := by
        simpa only [Fin.sum_univ_succ, val_tailV] using hq
      refine ⟨val q 0, by omega, tailV q, (ih _ _).mpr (by omega), cons_tailV q⟩

def localCandidates (R : RootedTree (Fin N)) (H : Fin N → ℕ) (m : ℕ) (v : Fin N) :
    List (Vector ℕ m) :=
  (compositionsV m (H v)).filter fun q =>
    decide (R.parent v = R.root → ∀ i, val q i ≤ 1)

theorem localCandidates_spec (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (v : Fin N) (q : Vector ℕ m) :
    q ∈ localCandidates R H m v ↔
      (∑ i, val q i) = H v ∧ RootChildCap R v (val q) := by
  simp only [localCandidates, List.mem_filter, decide_eq_true_eq, compositionsV_spec, RootChildCap]

end UAVProof.TreeBudgetSubtreeExecutable
