import LeanCompletion.UAV.TreeBudgetSubtreeAutoScaleSeed
import LeanCompletion.UAV.TreeBudgetSubtreeWitnessDP

/-!
Integer-cost witness search with full ordered-payload refinement. Injective key
lifting preserves rightmost representatives and their matrices. The automatic
entry point returns exactly the rational solver's certificate, including row
order and multiplicities. Rational lifts occur only in the proof-side maps.
-/
namespace UAVProof.TreeBudgetSubtreeIntegerWitnessSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable

abbrev Matrix (N m : ℕ) := TreeBudgetSubtreeWitness.Matrix N m

/-- Natural transformation of rightmost-key deduplication, including payloads. -/
theorem dedupKey_natural {α β κ ι : Type} [DecidableEq κ] [DecidableEq ι]
    (ka : α → κ) (kb : β → ι) (g : α → β) (f : κ → ι)
    (hf : Function.Injective f) (hkey : ∀ x, kb (g x) = f (ka x)) (xs : List α) :
    (TreeBudgetSubtreeWitness.dedupKey ka xs).map g =
      TreeBudgetSubtreeWitness.dedupKey kb (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hm :
        kb (g x) ∈ (TreeBudgetSubtreeWitness.dedupKey kb (xs.map g)).map kb ↔
          ka x ∈ (TreeBudgetSubtreeWitness.dedupKey ka xs).map ka := by
      rw [← ih, List.map_map]
      constructor
      · intro h
        obtain ⟨y, hy, he⟩ := List.mem_map.mp h
        have hk : ka y = ka x := hf (by simpa only [Function.comp_apply, hkey] using he)
        exact List.mem_map.mpr ⟨y, hy, hk⟩
      · intro h
        obtain ⟨y, hy, he⟩ := List.mem_map.mp h
        refine List.mem_map.mpr ⟨y, hy, ?_⟩
        change kb (g y) = kb (g x)
        rw [hkey, hkey, he]
    simp only [TreeBudgetSubtreeWitness.dedupKey, List.map_cons]
    by_cases h : ka x ∈ (TreeBudgetSubtreeWitness.dedupKey ka xs).map ka
    · rw [if_pos h, if_pos (hm.mpr h), ih]
    · rw [if_neg h, if_neg (fun hh => h (hm.mp hh)), List.map_cons, ih]

variable {N m : ℕ}

structure Entry (N m : ℕ) where
  key : TreeBudgetSubtreeInteger.IntState m
  matrix : Matrix N m
  deriving Inhabited

structure Inside (N m : ℕ) where
  cost : Vector ℤ m
  picks : List (Entry N m)

structure Root (N m : ℕ) where
  key : TreeBudgetSubtreeInteger.IntRoot m
  picks : List (Entry N m)

/-- Proof-side map only; it must not be called by the actual integer solver. -/
def liftEntry (D : ℕ) (e : Entry N m) : TreeBudgetSubtreeWitness.Entry N m :=
  ⟨TreeBudgetSubtreeInteger.liftState D e.key, e.matrix⟩

def liftInside (D : ℕ) (r : Inside N m) : TreeBudgetSubtreeWitness.Inside N m :=
  ⟨TreeBudgetSubtreeInteger.liftCost D r.cost, r.picks.map (liftEntry D)⟩

def liftRoot (D : ℕ) (r : Root N m) : TreeBudgetSubtreeWitness.Root N m :=
  ⟨TreeBudgetSubtreeInteger.liftRoot D r.key, r.picks.map (liftEntry D)⟩

@[simp] theorem liftEntry_matrix (D : ℕ) (e : Entry N m) :
    (liftEntry D e).matrix = e.matrix := rfl

theorem dedupEntry_lift {D : ℕ} (hD : 0 < D) (xs : List (Entry N m)) :
    (TreeBudgetSubtreeWitness.dedupKey Entry.key xs).map (liftEntry D) =
      TreeBudgetSubtreeWitness.dedupKey TreeBudgetSubtreeWitness.Entry.key
        (xs.map (liftEntry D)) :=
  dedupKey_natural Entry.key TreeBudgetSubtreeWitness.Entry.key
    (liftEntry D) (TreeBudgetSubtreeInteger.liftState D)
    (TreeBudgetSubtreeInteger.liftState_injective hD) (fun _ => rfl) xs

def inside (a : Vector Bool m) (base : Vector ℤ m) :
    List (List (Entry N m)) → List (Inside N m)
  | [] => [⟨base, []⟩]
  | t :: ts =>
    let rest := inside a base ts
    TreeBudgetSubtreeWitness.dedupKey Inside.cost
      ((t.filter fun e => subsetB e.key.active a).flatMap fun e =>
        rest.map fun r => ⟨TreeBudgetSubtreeInteger.add e.key.cost r.cost, e :: r.picks⟩)

/-- Pure natural-number payload construction: no rational lift in the execution path. -/
def glue (v : Fin N) (q : Vector ℕ m) (es : List (Entry N m)) : Matrix N m :=
  Vector.ofFn fun i => Vector.ofFn fun x =>
    if x = v then val q i
    else (es.map fun e => TreeBudgetSubtreeWitness.matrixVal e.matrix i x).sum

theorem glue_lift (D : ℕ) (v : Fin N) (q : Vector ℕ m) (es : List (Entry N m)) :
    TreeBudgetSubtreeWitness.glue v q (es.map (liftEntry D)) = glue v q es := by
  simp [TreeBudgetSubtreeWitness.glue, glue, List.map_map, Function.comp_def]

def node (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) : List (Entry N m) :=
  TreeBudgetSubtreeWitness.dedupKey Entry.key
    ((localCandidates R H m v).flatMap fun q =>
      (inside (support q) (Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)) ts).map
        fun r => ⟨⟨support q, r.cost⟩, glue v q r.picks⟩)

def compute (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) : List (Entry N m) :=
  node R H w m v ((childrenList R v).attach.map fun u => compute R H w m u.val)
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

def roots : List (List (Entry N m)) → List (Root N m)
  | [] => [⟨TreeBudgetSubtreeInteger.rootZero m, []⟩]
  | t :: ts =>
    let rest := roots ts
    TreeBudgetSubtreeWitness.dedupKey Root.key
      ((t.flatMap fun e => rest.map fun r =>
        ⟨TreeBudgetSubtreeInteger.rootAdd r.key e.key, e :: r.picks⟩).filter
          fun r => TreeBudgetSubtreeInteger.cap r.key)

def certificate (R : RootedTree (Fin N)) (r : Root N m) :
    TreeBudgetCertificate.Certificate (Fin N) :=
  ⟨m, TreeBudgetSubtreeWitness.matrixVal
    (glue R.root (Vector.ofFn fun _ => 0) r.picks), fun _ => 1⟩

theorem certificate_lift (D : ℕ) (R : RootedTree (Fin N)) (r : Root N m) :
    TreeBudgetSubtreeWitness.certificate R (liftRoot D r) = certificate R r := by
  simp [TreeBudgetSubtreeWitness.certificate, certificate, liftRoot, glue_lift]

def solve (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) : Option (TreeBudgetCertificate.Certificate (Fin N)) :=
  ((roots ((childrenList R R.root).map (compute R H w m))).find?
    fun r => TreeBudgetSubtreeInteger.accept B r.key).map (certificate R)

def solveAuto (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    Option (TreeBudgetCertificate.Certificate (Fin N)) :=
  let p := TreeBudgetSubtreeAutoScaleSeed.prepare R s T
  solve R H (val p.weight) m p.budget

theorem inside_lift_eq {D : ℕ} (hD : 0 < D)
    (a : Vector Bool m) (base : Vector ℤ m) (ts : List (List (Entry N m))) :
    (inside a base ts).map (liftInside D) =
      TreeBudgetSubtreeWitness.inside a (TreeBudgetSubtreeInteger.liftCost D base)
        (ts.map (List.map (liftEntry D))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [inside, TreeBudgetSubtreeWitness.inside, List.map_cons]
    rw [dedupKey_natural Inside.cost TreeBudgetSubtreeWitness.Inside.cost
      (liftInside D) (TreeBudgetSubtreeInteger.liftCost D)
      (TreeBudgetSubtreeInteger.liftCost_injective hD) (fun _ => rfl)]
    congr 1
    simp only [List.map_flatMap, List.map_map, List.filter_map, List.flatMap_map,
      Function.comp_def]
    apply List.flatMap_congr
    intro e _
    rw [← ih, List.map_map]
    apply List.map_congr_left
    intro r _
    simp [liftInside, liftEntry, TreeBudgetSubtreeInteger.lift_add,
      TreeBudgetSubtreeInteger.liftState]

theorem node_lift_eq {D : ℕ} (hD : 0 < D)
    (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (hw : (w v : ℚ) = (D : ℚ) * linearWeight R s v)
    (ts : List (List (Entry N m))) :
    (node R H w m v ts).map (liftEntry D) =
      TreeBudgetSubtreeWitness.node R H s m v (ts.map (List.map (liftEntry D))) := by
  unfold node TreeBudgetSubtreeWitness.node
  rw [dedupEntry_lift hD]
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  rw [List.map_map, ← TreeBudgetSubtreeInteger.lift_initial hD (w v) _ hw q,
    ← inside_lift_eq hD, List.map_map]
  apply List.map_congr_left
  intro r _
  simp [liftEntry, liftInside, TreeBudgetSubtreeInteger.liftState,
    glue_lift]

theorem compute_lift_eq {D : ℕ} (hD : 0 < D)
    (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (hv : v ≠ R.root)
    (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    (compute R H w m v).map (liftEntry D) =
      TreeBudgetSubtreeWitness.compute R H s m v := by
  rw [compute, node_lift_eq hD R H s w m v (hw v hv), TreeBudgetSubtreeWitness.compute]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro u _
  exact compute_lift_eq hD R H s w m u.val
    ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp u.property)).1 hw
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem roots_lift_eq {D : ℕ} (hD : 0 < D) (ts : List (List (Entry N m))) :
    (roots ts).map (liftRoot D) =
      TreeBudgetSubtreeWitness.roots (ts.map (List.map (liftEntry D))) := by
  induction ts with
  | nil => simp [roots, TreeBudgetSubtreeWitness.roots, liftRoot]
  | cons t ts ih =>
    simp only [roots, TreeBudgetSubtreeWitness.roots, List.map_cons]
    rw [dedupKey_natural Root.key TreeBudgetSubtreeWitness.Root.key
      (liftRoot D) (TreeBudgetSubtreeInteger.liftRoot D)
      (TreeBudgetSubtreeInteger.liftRoot_injective hD) (fun _ => rfl)]
    have hr : ((t.flatMap fun e => (roots ts).map fun r =>
        (⟨TreeBudgetSubtreeInteger.rootAdd r.key e.key, e :: r.picks⟩ : Root N m)).map
          (liftRoot D)) =
        (t.map (liftEntry D)).flatMap (fun e =>
          (TreeBudgetSubtreeWitness.roots (ts.map (List.map (liftEntry D)))).map
            fun r => ⟨rootAdd r.key e.key, e :: r.picks⟩) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map]
      apply List.flatMap_congr
      intro e _
      rw [← ih, List.map_map]
      apply List.map_congr_left
      intro r _
      simp [liftRoot, liftEntry]
    congr 1
    rw [← hr, List.filter_map]
    rfl

theorem solve_lift_eq {D : ℕ} (hD : 0 < D)
    (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (m : ℕ) (T : ℚ)
    (hw : ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x) :
    solve R H w m (TreeBudgetSubtreeInteger.floorBudget D T) =
      TreeBudgetSubtreeWitness.solve R H s m T := by
  unfold solve TreeBudgetSubtreeWitness.solve
  have hc : ((childrenList R R.root).map (compute R H w m)).map (List.map (liftEntry D)) =
      (childrenList R R.root).map (TreeBudgetSubtreeWitness.compute R H s m) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro u hu
    exact compute_lift_eq hD R H s w m u
      ((R.mem_children _ _).mp ((mem_childrenList _ _ _).mp hu)).1 hw
  rw [← hc, ← roots_lift_eq hD, List.find?_map, Option.map_map]
  simp only [Function.comp_def, liftRoot, ← TreeBudgetSubtreeInteger.accept_lift_eq hD]
  congr 1
  funext r
  exact (certificate_lift D R r).symm

theorem solveAuto_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    solveAuto R H s m T = TreeBudgetSubtreeWitness.solve R H s m T := by
  unfold solveAuto
  change solve R H (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) m
    (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).budget = _
  rw [TreeBudgetSubtreeAutoScaleSeed.prepare_budget]
  exact solve_lift_eq (TreeBudgetSubtreeAutoScaleSeed.prepare_pos R s T)
    R H s (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) m T
    (TreeBudgetSubtreeAutoScaleSeed.prepare_weight R s T)

/-- Any two valid positive scales return the same entire certificate. -/
theorem solve_scale_independent (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (D₁ D₂ : ℕ)
    (w₁ w₂ : Fin N → ℤ) (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (hw₁ : ∀ x, x ≠ R.root → (w₁ x : ℚ) = (D₁ : ℚ) * linearWeight R s x)
    (hw₂ : ∀ x, x ≠ R.root → (w₂ x : ℚ) = (D₂ : ℚ) * linearWeight R s x) :
    solve R H w₁ m (TreeBudgetSubtreeInteger.floorBudget D₁ T) =
      solve R H w₂ m (TreeBudgetSubtreeInteger.floorBudget D₂ T) := by
  rw [solve_lift_eq h₁ R H s w₁ m T hw₁, solve_lift_eq h₂ R H s w₂ m T hw₂]

theorem solveAuto_sound (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (c : TreeBudgetCertificate.Certificate (Fin N))
    (hc : solveAuto R H s m T = some c) :
    TreeBudgetCertificate.checkCertificate R H m s T c = true := by
  rw [solveAuto_eq] at hc
  exact TreeBudgetSubtreeWitness.solve_sound R H s m T c hc

theorem solveAuto_none_iff (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    solveAuto R H s m T = none ↔ ¬ TreeBudgetMatrix.MatrixFeasible R H m s T := by
  rw [solveAuto_eq]
  exact TreeBudgetSubtreeWitness.solve_none_iff R H s m T

theorem solveAuto_size (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (c : TreeBudgetCertificate.Certificate (Fin N))
    (hc : solveAuto R H s m T = some c) : c.size = m := by
  rw [solveAuto_eq] at hc
  exact TreeBudgetSubtreeWitness.solve_size R H s m T c hc

theorem solveAuto_exact_iff (R : RootedTree (Fin N)) (H d : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (hd : SupportExactFeasibility.HasDegrees R.root d m (edgeFlow R H)) :
    (solveAuto R H s m T).isSome = true ↔
      SupportExactFeasibility.ExactFeasible R.root (edgeFlow R H) d m s T := by
  rw [solveAuto_eq]
  exact TreeBudgetSubtreeWitness.solve_exact_iff R H d s m T hd

#print axioms dedupKey_natural
#print axioms dedupEntry_lift
#print axioms glue_lift
#print axioms certificate_lift

end UAVProof.TreeBudgetSubtreeIntegerWitnessSeed
