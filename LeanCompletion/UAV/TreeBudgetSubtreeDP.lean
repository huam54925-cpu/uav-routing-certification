import LeanCompletion.UAV.TreeBudgetSubtreeFold

/-! Executable compressed-state DP with exact signed rational costs. Child
tables are materialized outside the local-column loop. No budget pruning is
performed before the final root acceptance check. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetMatrix
variable {N m : ℕ}

def nodeTable (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (tables : List (List (ExecCompactState m))) : List (ExecCompactState m) :=
  ((localCandidates R H m v).flatMap fun q =>
    (insideCosts (support q)
      (Vector.ofFn (fun i => linearWeight R s v * ((val q i : ℕ) : ℚ))) tables).map
      (fun b => ⟨support q, b⟩)).dedup

theorem nodeTable_spec (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (v : Fin N) (hv : v ≠ R.root) (tables : Fin N → List (ExecCompactState m))
    (ht : ∀ u ∈ R.children v, ∀ e, e ∈ tables u ↔ CompactRep R H m s u (decodeState e))
    (e : ExecCompactState m) :
    e ∈ nodeTable R H s m v ((childrenList R v).map tables) ↔
      CompactRep R H m s v (decodeState e) := by
  classical
  rw [compactRep_merge_iff R H m s v hv]
  simp only [nodeTable, List.mem_dedup, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨q, hq, b, hb, rfl⟩
    obtain ⟨es, hsel, hs, hc⟩ := (insideCosts_spec _ _ _ _).mp hb
    obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R v) tables es).mp hsel
    obtain ⟨hqsum, hcap⟩ := (localCandidates_spec R H v q).mp hq
    refine ⟨val q, hqsum, hcap, ?_, fun u => decodeState (f u), ?_, ?_, ?_⟩
    · intro i; simp [decodeState, support]
    · intro u hu
      exact (ht u hu (f u)).mp (hm u ((mem_childrenList R v u).mpr hu))
    · intro u hu i hi
      have hmem : f u ∈ es := by
        rw [← hf]
        exact List.mem_map_of_mem ((mem_childrenList R v u).mpr hu)
      have hsub := (subsetB_spec _ _).mp (hs (f u) hmem)
      exact (mem_decodeState _ i).mpr (hsub i ((mem_decodeState _ i).mp hi))
    · intro i
      have h := hc i
      rw [← hf, List.map_map, childrenList_sum] at h
      simpa [decodeState, Function.comp_def] using h
  · rintro ⟨q, hq, hcap, ha, zs, hz, hs, hc⟩
    let qv := Vector.ofFn q
    have hqv : qv ∈ localCandidates R H m v := by
      apply (localCandidates_spec _ _ _ _).mpr
      refine ⟨by simpa [qv] using hq, ?_⟩
      intro hp i
      simpa [qv] using hcap hp i
    have hactive : support qv = e.active := by
      apply vector_ext
      intro i
      apply Bool.eq_iff_iff.mpr
      simpa [support, qv] using (ha i).symm
    refine ⟨qv, hqv, e.cost, ?_, ?_⟩
    · apply (insideCosts_spec _ _ _ _).mpr
      refine ⟨(childrenList R v).map (fun u => encodeState (zs u)), ?_, ?_, ?_⟩
      · apply (selected_family _ (childrenList_nodup R v) _ _).mpr
        refine ⟨fun u => encodeState (zs u), rfl, ?_⟩
        intro u hu
        apply (ht u ((mem_childrenList _ _ _).mp hu) _).mpr
        simpa using hz u ((mem_childrenList _ _ _).mp hu)
      · intro child hchild
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hchild
        rw [hactive, subsetB_spec]
        intro i hi
        apply (mem_decodeState e i).mp
        apply hs u ((mem_childrenList _ _ _).mp hu)
        simpa [encodeState] using hi
      · intro i
        simpa [qv, List.map_map, Function.comp_def, encodeState,
          childrenList_sum, decodeState] using hc i
    · exact state_ext (fun i => congrArg (fun a => val a i) hactive) (fun _ => rfl)

def computeCompact (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) : List (ExecCompactState m) :=
  let tables := (childrenList R v).attach.map fun u => computeCompact R H s m u.val
  nodeTable R H s m v tables
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList R v u.val).mp u.property)

theorem computeCompact_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) :
    computeCompact R H s m v =
      nodeTable R H s m v ((childrenList R v).map (computeCompact R H s m)) := by
  rw [computeCompact]
  simp only [List.attach_map_val]

theorem computeCompact_spec (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (v : Fin N) (hv : v ≠ R.root) (e : ExecCompactState m) :
    e ∈ computeCompact R H s m v ↔ CompactRep R H m s v (decodeState e) := by
  rw [computeCompact_eq]
  apply nodeTable_spec R H s v hv
  intro u hu e
  exact computeCompact_spec R H s m u ((R.mem_children _ _).mp hu).1 e
termination_by R.rank v
decreasing_by exact R.child_rank hu

def acceptRootB (T : ℚ) (b : ExecRootState m) : Bool :=
  (List.finRange m).all fun i => decide (val b.used i = 1 ∧ val b.cost i ≤ T)

theorem acceptRootB_spec (T : ℚ) (b : ExecRootState m) :
    acceptRootB T b = true ↔ ∀ i, val b.used i = 1 ∧ val b.cost i ≤ T := by
  simp [acceptRootB]

def checkCompact (R : RootedTree (Fin N)) (H : Fin N → ℕ) (s : Fin N → ℚ)
    (m : ℕ) (T : ℚ) : Bool :=
  let tables := (childrenList R R.root).map (computeCompact R H s m)
  (rootFold tables).any (acceptRootB T)

theorem checkCompact_eq_true_iff (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    checkCompact R H s m T = true ↔ MatrixFeasible R H m s T := by
  classical
  rw [← compactRootAccept_iff_matrixFeasible]
  simp only [checkCompact, List.any_eq_true, acceptRootB_spec]
  constructor
  · rintro ⟨b, hb, haccept⟩
    obtain ⟨es, hsel, _, hu, hc⟩ := (rootFold_spec _ b).mp hb
    obtain ⟨f, hf, hm⟩ := (selected_family _ (childrenList_nodup R R.root) _ _).mp hsel
    refine ⟨fun u => decodeState (f u), ?_, ?_, ?_⟩
    · intro u hu
      exact (computeCompact_spec R H s m u ((R.mem_children _ _).mp hu).1 (f u)).mp
        (hm u ((mem_childrenList _ _ _).mpr hu))
    · intro i
      have h := hu i
      rw [← hf, List.map_map, childrenList_sum, (haccept i).1] at h
      simpa [decodeState, bit, Function.comp_def] using h.symm
    · intro i
      have h := hc i
      rw [← hf, List.map_map, childrenList_sum] at h
      simpa only [decodeState, Function.comp_apply, h] using (haccept i).2
  · rintro ⟨zs, hz, hdegree, hbudget⟩
    let es := (childrenList R R.root).map (fun u => encodeState (zs u))
    let b : ExecRootState m :=
      ⟨Vector.ofFn (fun _ => 1), Vector.ofFn (fun i => ∑ u ∈ R.children R.root, (zs u).cost i)⟩
    refine ⟨b, (rootFold_spec _ b).mpr ?_, ?_⟩
    · refine ⟨es, ?_, by simp [b], ?_, ?_⟩
      · apply (selected_family _ (childrenList_nodup R R.root) _ _).mpr
        refine ⟨fun u => encodeState (zs u), rfl, ?_⟩
        intro u hu
        have hchild := (mem_childrenList R R.root u).mp hu
        apply (computeCompact_spec R H s m u ((R.mem_children _ _).mp hchild).1 _).mpr
        simpa using hz u ((mem_childrenList _ _ _).mp hu)
      · intro i
        simpa [es, b, List.map_map, Function.comp_def, encodeState,
          bit, childrenList_sum] using (hdegree i).symm
      · intro i
        simp [es, b, List.map_map, Function.comp_def, encodeState, childrenList_sum]
    · intro i
      constructor
      · simp [b]
      · simpa [b] using hbudget i

theorem checkCompact_eq_false_iff (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    checkCompact R H s m T = false ↔ ¬ MatrixFeasible R H m s T := by
  have h := checkCompact_eq_true_iff R H s m T
  cases he : checkCompact R H s m T <;> simp_all

theorem checkCompact_exact_iff (R : RootedTree (Fin N)) (H d : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (hd : SupportExactFeasibility.HasDegrees R.root d m (edgeFlow R H)) :
    checkCompact R H s m T = true ↔
      SupportExactFeasibility.ExactFeasible R.root (edgeFlow R H) d m s T :=
  (checkCompact_eq_true_iff R H s m T).trans (exact_iff_matrix R H d m s T hd).symm

end UAVProof.TreeBudgetSubtreeExecutable

#print axioms UAVProof.TreeBudgetSubtreeExecutable.computeCompact_spec
#print axioms UAVProof.TreeBudgetSubtreeExecutable.checkCompact_eq_true_iff
#print axioms UAVProof.TreeBudgetSubtreeExecutable.checkCompact_eq_false_iff
#print axioms UAVProof.TreeBudgetSubtreeExecutable.checkCompact_exact_iff
