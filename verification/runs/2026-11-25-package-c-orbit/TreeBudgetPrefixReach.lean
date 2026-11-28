import TreeBudgetPrefixFold

/-!
# Issue 26, multi-child fold, item 2

Candidate for local elaboration against commit 6dd4ce8.
This module uses the prototype directory's existing import path.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

noncomputable section

abbrev OrbitHist := Multiset JointType

/-- The two supports stay explicit so a support rewrite never needs to cast
an already chosen dependent table. -/
def HistJoinOn (A B : Finset JointType) (p c h : OrbitHist) : Prop :=
  ∃ N : A → B → ℕ,
    (∀ a : A, (∑ b : B, N a b) = p.count a.1) ∧
    (∀ b : B, (∑ a : A, N a b) = c.count b.1) ∧
    (∀ (a : A) (b : B), ¬ K_in a.1 b.1 → N a b = 0) ∧
    tablePushforwardHist N = h

def HistJoin (p c h : OrbitHist) : Prop :=
  HistJoinOn p.toFinset c.toFinset p c h

theorem jointHist_support_image {m : ℕ} (z : CompactState m) :
    (jointHist z).toFinset = Finset.univ.image (jointType z) := by
  classical
  ext t
  simp [jointHist, Finset.mem_image]

theorem jointHist_count_filter {m : ℕ} (z : CompactState m) (t : JointType) :
    (jointHist z).count t =
      (Finset.univ.filter (fun i : Fin m => jointType z i = t)).card := by
  rw [count_jointHist_eq_card_fiber, Fintype.card_subtype]

/-- The representative is arbitrary on each side. This lemma works in both directions. -/
theorem histJoin_jointHist_iff {m : ℕ} (x y : CompactState m) (h : OrbitHist) :
    HistJoin (jointHist x) (jointHist y) h ↔
      ∃ N : (Finset.univ.image (jointType x)) → (Finset.univ.image (jointType y)) → ℕ,
        LegalTable (Finset.univ.image (jointType x)) (Finset.univ.image (jointType y))
          (jointType x) (jointType y) K_in N ∧ tablePushforwardHist N = h := by
  classical
  unfold HistJoin
  rw [jointHist_support_image x, jointHist_support_image y]
  simp only [HistJoinOn, LegalTable, jointHist_count_filter]
  constructor
  · rintro ⟨N, hrow, hcol, hzero, hout⟩
    exact ⟨N, ⟨fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
               fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩,
               hrow, hcol, hzero⟩, hout⟩
  · rintro ⟨N, ⟨_, _, hrow, hcol, hzero⟩, hout⟩
    exact ⟨N, hrow, hcol, hzero, hout⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Semantic availability of a histogram at the child. -/
def ChildHist (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ)
    (u : V) (c : OrbitHist) : Prop :=
  ∃ z : CompactState m, CompactRep R H m s u z ∧ jointHist z = c

def histAdvance (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ)
    (prev : OrbitHist → Prop) (u : V) (h : OrbitHist) : Prop :=
  ∃ p c : OrbitHist, prev p ∧ ChildHist R H m s u c ∧ HistJoin p c h

def prefixSeed (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (v : V) (q : Fin m → ℕ) : OrbitHist :=
  jointHist (parentState R s v q ∅ (fun _ _ _ => 0))

def PrefixReach (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (us : List V) : OrbitHist → Prop :=
  us.foldl (histAdvance R H m s) (fun h => prefixSeed R s v q = h)

def PrefixWitnessHist (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (q : Fin m → ℕ) (S : Finset V) (h : OrbitHist) : Prop :=
  ∃ ns : V → Fin m → V → ℕ,
    PrefixValid R H v q S ns ∧ jointHist (parentState R s v q S ns) = h

theorem prefixWitnessHist_empty_iff (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (h : OrbitHist) :
    PrefixWitnessHist R H s v q ∅ h ↔ prefixSeed R s v q = h := by
  constructor
  · rintro ⟨ns, _, hh⟩
    have he : parentState R s v q ∅ (fun _ _ _ => 0) = parentState R s v q ∅ ns := by
      apply compactState_ext rfl
      funext i
      simp only [parentState_empty_cost]
    exact (congrArg jointHist he).trans hh
  · intro hh
    exact ⟨_, prefixValid_empty R H v q (fun _ _ _ => 0), hh⟩

/-- One fresh child, exact in both directions for an arbitrary feasible prefix. -/
theorem histAdvance_prefixWitness_iff (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (S : Finset V) (u : V)
    (hu : u ∈ R.children v) (hfresh : u ∉ S) (h : OrbitHist) :
    histAdvance R H m s (PrefixWitnessHist R H s v q S) u h ↔
      PrefixWitnessHist R H s v q (insert u S) h := by
  classical
  constructor
  · rintro ⟨p, c, ⟨ns, hP, hp⟩, ⟨z, ⟨n, hn, hcap, hact, hcost⟩, hc⟩, hj⟩
    rw [← hp, ← hc] at hj
    obtain ⟨σ, hInv, _, hout⟩ :=
      prefixValid_insert_of_transport R H s v q S u hu hfresh ns hP n z
        hn hcap hact hcost h ((histJoin_jointHist_iff _ _ h).mp hj)
    exact ⟨extendChild u ns (reindexMatrix σ n), hInv, hout⟩
  · rintro ⟨ns, hP, hout⟩
    have hin : u ∈ insert u S := Finset.mem_insert_self _ _
    have hold {w : V} (hw : w ∈ S) : w ∈ insert u S := Finset.mem_insert_of_mem hw
    have hOld : PrefixValid R H v q S ns :=
      ⟨fun _ hw => hP.sub_children (hold hw),
       fun w hw => hP.valid w (hold hw),
       fun w hw => hP.cap w (hold hw),
       fun w hw => hP.compat w (hold hw)⟩
    let n := ns u
    let z : CompactState m :=
      ⟨Finset.univ.filter (fun i => 0 < n i u), fun i => subtreeLinearCost R s u (n i)⟩
    have ha (i : Fin m) : i ∈ z.active ↔ 0 < n i u := by simp [z]
    have hc (i : Fin m) : subtreeLinearCost R s u (n i) = z.cost i := rfl
    have hV := hP.valid u hin
    have hC := hP.cap u hin
    have hRep : CompactRep R H m s u z := ⟨n, hV, hC, ha, hc⟩
    let σ := Equiv.refl (Fin m)
    have hsame : extendChild u ns (reindexMatrix σ n) = ns := by
      funext w
      by_cases hw : w = u
      · subst w
        simp [extendChild, σ, n]
        rfl
      · simp [extendChild, hw]
    refine ⟨jointHist (parentState R s v q S ns), jointHist z,
      ⟨ns, hOld, rfl⟩, ⟨z, hRep, rfl⟩, (histJoin_jointHist_iff _ _ h).mpr ?_⟩
    apply (inside_join_hist_iff R H s v q S u hfresh ns n z hV hC ha hc h).mpr
    refine ⟨σ, hV, hC, compactRep_reindex R H s u σ z hRep, hP.compat u hin, ?_⟩
    rw [hsame]
    exact hout

/-- Induct left-to-right with an arbitrary set of already processed children.
All three list hypotheses have shorter-list versions in the cons case. -/
theorem histFold_from_iff (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (S : Finset V) (us : List V)
    (h : OrbitHist) :
    us.Nodup → (∀ u ∈ us, u ∈ R.children v) → (∀ u ∈ us, u ∉ S) →
    (us.foldl (histAdvance R H m s) (PrefixWitnessHist R H s v q S) h ↔
      PrefixWitnessHist R H s v q (S ∪ us.toFinset) h) := by
  classical
  induction us generalizing S with
  | nil => simp
  | cons u us ih =>
    intro hd hall hf
    obtain ⟨hnot, hd'⟩ := List.nodup_cons.mp hd
    have hu : u ∈ R.children v := hall u (by simp)
    have hf0 : u ∉ S := hf u (by simp)
    have hstep :
        histAdvance R H m s (PrefixWitnessHist R H s v q S) u =
        PrefixWitnessHist R H s v q (insert u S) := by
      funext t
      exact propext (histAdvance_prefixWitness_iff R H s v q S u hu hf0 t)
    have hrest (w : V) (hw : w ∈ us) : w ∉ insert u S := by
      intro hin
      rcases Finset.mem_insert.mp hin with e | hS
      · exact hnot (e ▸ hw)
      · exact hf w (List.mem_cons_of_mem u hw) hS
    have he : insert u S ∪ us.toFinset = S ∪ (u :: us).toFinset := by
      ext w
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
      tauto
    rw [List.foldl_cons, hstep, ← he]
    exact ih (insert u S) hd' (fun w hw => hall w (List.mem_cons_of_mem u hw)) hrest

/-- The local statement holds for every fixed q. At the internal-node interface
one supplies v ≠ R.root, (∑ i, q i) = H v and RootChildCap R v q separately. -/
theorem prefixReach_iff_witness (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (us : List V)
    (hd : us.Nodup) (hall : ∀ u ∈ us, u ∈ R.children v) (h : OrbitHist) :
    PrefixReach R H s v q us h ↔
      ∃ ns : V → Fin m → V → ℕ, PrefixValid R H v q us.toFinset ns ∧
        jointHist (parentState R s v q us.toFinset ns) = h := by
  classical
  have hbase : (fun t => prefixSeed R s v q = t) = PrefixWitnessHist R H s v q ∅ := by
    funext t
    exact propext (prefixWitnessHist_empty_iff R H s v q t).symm
  unfold PrefixReach
  rw [hbase]
  have hf (u : V) (_ : u ∈ us) : u ∉ (∅ : Finset V) := Finset.notMem_empty u
  simpa only [Finset.empty_union, PrefixWitnessHist] using
    (histFold_from_iff R H s v q ∅ us h hd hall hf)

/-- Orders with the same processed set have the same set of reachable outputs. -/
theorem prefixReach_iff_of_same_children (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (xs ys : List V)
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hcx : ∀ u ∈ xs, u ∈ R.children v) (hcy : ∀ u ∈ ys, u ∈ R.children v)
    (he : xs.toFinset = ys.toFinset) (h : OrbitHist) :
    PrefixReach R H s v q xs h ↔ PrefixReach R H s v q ys h := by
  rw [prefixReach_iff_witness R H s v q xs hx hcx,
      prefixReach_iff_witness R H s v q ys hy hcy, he]

theorem prefixReach_nil_iff (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (q : Fin m → ℕ) (h : OrbitHist) :
    PrefixReach R H s v q [] h ↔ prefixSeed R s v q = h := Iff.rfl

theorem prefixReach_zero_routes_only_empty (R : RootedTree V) (H : V → ℕ)
    (s : V → ℚ) (v : V) (q : Fin 0 → ℕ) (us : List V)
    (hd : us.Nodup) (hall : ∀ u ∈ us, u ∈ R.children v) (h : OrbitHist)
    (hr : PrefixReach R H s v q us h) : h = 0 := by
  obtain ⟨ns, _, hh⟩ := (prefixReach_iff_witness R H s v q us hd hall h).mp hr
  rw [← hh]
  simp [jointHist]

/-- Reuse the two-child signed-cost witness of item 1 through the new reachability interface. -/
theorem ex_prefixReach_two_child_hub (R : RootedTree (Fin 4))
    (hroot : R.root = 0) (hparent : R.parent = ![0, 0, 1, 1]) :
    let s : Fin 4 → ℚ := ![0, 2, -5, 3]
    let H : Fin 4 → ℕ := ![0, 2, 1, 1]
    let q : Fin 2 → ℕ := ![1, 1]
    PrefixReach R H s 1 q [2, 3]
      (jointHist (⟨Finset.univ, ![-1, 7]⟩ : CompactState 2)) := by
  intro s H q
  have hall (u : Fin 4) (hu : u ∈ ([2, 3] : List (Fin 4))) : u ∈ R.children 1 := by
    have e : u = 2 ∨ u = 3 := by simpa using hu
    rcases e with rfl | rfl <;> rw [R.mem_children, hroot, hparent] <;> decide
  have hs : ([2, 3] : List (Fin 4)).toFinset = {3, 2} := by decide
  apply (prefixReach_iff_witness R H s 1 q [2, 3] (by decide) hall _).mpr
  rw [hs]
  obtain ⟨_, hp, _, h0, h1⟩ := ex_two_child_hub_regression R hroot hparent
  -- hp fixes the existential witness before comparing its two rows.
  refine ⟨_, hp, congrArg jointHist ?_⟩
  apply compactState_ext
  · ext i
    fin_cases i <;> simp [parentState, q]
  · funext i
    fin_cases i
    · exact h0
    · exact h1

end

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.histJoin_jointHist_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.histAdvance_prefixWitness_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.histFold_from_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixReach_iff_witness
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixReach_iff_of_same_children
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixReach_nil_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.prefixReach_zero_routes_only_empty

#print axioms UAVProof.TreeBudgetOrbitPrototype.ex_prefixReach_two_child_hub
