import LeanCompletion.UAV.TreeFlowExistence

/-! A materialized parent array and a bounded, executable rooted-tree check.
The graph and rank below are proof-only interpretations. The runtime data are
the root index and array, and the validator follows at most n links per vertex. -/
namespace UAVProof.TreeBudgetParentArray
open TreeFlowExistence
variable {n : ℕ}

structure ParentArray (n : ℕ) where
  root : Fin n
  parents : Vector (Fin n) n

def parent (P : ParentArray n) (v : Fin n) : Fin n := P.parents[v]

def follow (P : ParentArray n) : ℕ → Fin n → Fin n
  | 0, v => v
  | k + 1, v => follow P k (parent P v)

def Valid (P : ParentArray n) : Prop :=
  parent P P.root = P.root ∧ ∀ v, follow P n v = P.root

def validateB (P : ParentArray n) : Bool :=
  decide (parent P P.root = P.root) &&
    (List.finRange n).all (fun v => decide (follow P n v = P.root))

theorem validateB_eq_true (P : ParentArray n) : validateB P = true ↔ Valid P := by
  simp [validateB, Valid, List.all_eq_true]

theorem follow_fixed (P : ParentArray n) (v : Fin n) (h : parent P v = v) (k : ℕ) :
    follow P k v = v := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [follow, h] using ih

theorem parent_ne_self (P : ParentArray n) (hP : Valid P) (v : Fin n) (hv : v ≠ P.root) :
    parent P v ≠ v := by
  intro he
  exact hv ((follow_fixed P v he n).symm.trans (hP.2 v))

def graph (P : ParentArray n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => v ≠ P.root ∧ parent P v = u)

theorem graph_adj (P : ParentArray n) (hP : Valid P) (u v : Fin n) :
    (graph P).Adj u v ↔
      (v ≠ P.root ∧ parent P v = u) ∨ (u ≠ P.root ∧ parent P u = v) := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact parent_ne_self P hP _ h.1 h.2

theorem reachable_follow (P : ParentArray n) (hP : Valid P) (k : ℕ) (v : Fin n) :
    (graph P).Reachable v (follow P k v) := by
  induction k generalizing v with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    have hp : (graph P).Reachable v (parent P v) := by
      by_cases hv : v = P.root
      · subst v
        rw [hP.1]
      · exact ((graph_adj P hP _ _).mpr (Or.inr ⟨hv, rfl⟩)).reachable
    exact hp.trans (ih (parent P v))

theorem graph_connected (P : ParentArray n) (hP : Valid P) : (graph P).Connected := by
  letI : Nonempty (Fin n) := ⟨P.root⟩
  constructor
  intro u v
  have hu := reachable_follow P hP n u
  have hv := reachable_follow P hP n v
  rw [hP.2] at hu hv
  exact hu.trans hv.symm

theorem graph_isTree (P : ParentArray n) (hP : Valid P) : (graph P).IsTree := by
  classical
  have hconn := graph_connected P hP
  have hedge : (graph P).edgeFinset ⊆
      (Finset.univ.erase P.root).image (fun v => s(parent P v, v)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have ha : (graph P).Adj u v := (SimpleGraph.mem_edgeSet ..).mp
        (SimpleGraph.mem_edgeFinset.mp he)
      rcases (graph_adj P hP u v).mp ha with ⟨hv, hp⟩ | ⟨hu, hp⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], by rw [hp]⟩
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], by rw [hp]; exact Sym2.eq_swap⟩
  have hle := (Finset.card_le_card hedge).trans (Finset.card_image_le)
  have hcard : (Finset.univ.erase P.root : Finset (Fin n)).card = n - 1 := by simp
  rw [hcard] at hle
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  have hn : 0 < n := (Nat.zero_le P.root.val).trans_lt P.root.isLt
  have heq : Nat.card (graph P).edgeSet = (graph P).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [heq, Nat.card_eq_fintype_card, Fintype.card_fin] at hlo
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨hconn, ?_⟩
  rw [heq, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

noncomputable def depth (P : ParentArray n) (hP : Valid P) (v : Fin n) : ℕ :=
  Nat.find (show ∃ k, follow P k v = P.root from ⟨n, hP.2 v⟩)

theorem depth_spec (P : ParentArray n) (hP : Valid P) (v : Fin n) :
    follow P (depth P hP v) v = P.root := by
  unfold depth
  exact Nat.find_spec (show ∃ k, follow P k v = P.root from ⟨n, hP.2 v⟩)

theorem depth_le (P : ParentArray n) (hP : Valid P) (v : Fin n) :
    depth P hP v ≤ n := Nat.find_min' _ (hP.2 v)

theorem depth_parent (P : ParentArray n) (hP : Valid P) (v : Fin n) (hv : v ≠ P.root) :
    depth P hP (parent P v) + 1 = depth P hP v := by
  have hd := depth_spec P hP v
  have hn : depth P hP v ≠ 0 := by
    intro hz
    rw [hz] at hd
    exact hv hd
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hparent : follow P k (parent P v) = P.root := by
    simpa only [hk, follow] using hd
  have hle : depth P hP (parent P v) ≤ k := Nat.find_min' _ hparent
  have hle' : depth P hP v ≤ depth P hP (parent P v) + 1 :=
    Nat.find_min' _ (by simpa only [follow] using depth_spec P hP (parent P v))
  omega

/-- This proof object is not stored or computed by the runtime executor. -/
noncomputable def toRootedTree (P : ParentArray n) (hP : Valid P) : RootedTree (Fin n) where
  graph := graph P
  isTree := graph_isTree P hP
  root := P.root
  parent := parent P
  parent_root := hP.1
  rank := fun v => n - depth P hP v
  parent_rank := by
    intro v hv
    have h := depth_parent P hP v hv
    have hle := depth_le P hP v
    omega
  adj_iff := graph_adj P hP

@[simp] theorem toRootedTree_parent (P : ParentArray n) (hP : Valid P) (v : Fin n) :
    (toRootedTree P hP).parent v = P.parents[v] := rfl

@[simp] theorem toRootedTree_root (P : ParentArray n) (hP : Valid P) :
    (toRootedTree P hP).root = P.root := rfl

/-- Reject invalid indices before materializing the typed array. -/
def decodeParents (root : ℕ) (parents : List ℕ) :
    Option {P : ParentArray parents.length // Valid P} :=
  if hr : root < parents.length then
    if hp : ∀ v ∈ parents, v < parents.length then
      let P : ParentArray parents.length :=
        ⟨⟨root, hr⟩, Vector.ofFn fun i =>
          ⟨parents[i], hp _ (List.getElem_mem i.isLt)⟩⟩
      if hP : validateB P = true then some ⟨P, (validateB_eq_true P).mp hP⟩ else none
    else none
  else none

theorem decodeParents_invalid_root (root : ℕ) (parents : List ℕ)
    (h : parents.length ≤ root) : decodeParents root parents = none := by
  simp [decodeParents, Nat.not_lt.mpr h]

theorem decodeParents_invalid_index (root : ℕ) (parents : List ℕ)
    (h : ∃ v ∈ parents, parents.length ≤ v) : decodeParents root parents = none := by
  have hn : ¬ ∀ v ∈ parents, v < parents.length := by
    obtain ⟨v, hv, hle⟩ := h
    exact fun hh => (Nat.not_lt.mpr hle) (hh v hv)
  simp [decodeParents, hn]

theorem decodeParents_spec (root : ℕ) (parents : List ℕ)
    (out : {P : ParentArray parents.length // Valid P})
    (h : decodeParents root parents = some out) :
    out.val.root.val = root ∧ ∀ v : Fin parents.length, (out.val.parents[v]).val = parents[v] := by
  unfold decodeParents at h
  split at h
  · split at h
    · dsimp only at h
      split at h
      · cases Option.some.inj h
        constructor
        · rfl
        · intro v; simp
      · cases h
    · cases h
  · cases h

/-- Each successor step performs exactly one parent-array read. -/
def followReads (P : ParentArray n) : ℕ → Fin n → Fin n × ℕ
  | 0, v => (v, 0)
  | k + 1, v =>
      let out := followReads P k (parent P v)
      (out.1, out.2 + 1)

theorem followReads_spec (P : ParentArray n) (k : ℕ) (v : Fin n) :
    followReads P k v = (follow P k v, k) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [followReads, follow, ih]

def checkVerticesReads (P : ParentArray n) : List (Fin n) → Bool × ℕ
  | [] => (true, 0)
  | v :: vs =>
      let out := followReads P n v
      if out.1 = P.root then
        let tail := checkVerticesReads P vs
        (tail.1, out.2 + tail.2)
      else (false, out.2)

theorem checkVerticesReads_value (P : ParentArray n) (vs : List (Fin n)) :
    (checkVerticesReads P vs).1 = vs.all (fun v => decide (follow P n v = P.root)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [checkVerticesReads, followReads_spec, List.all_cons]
    split <;> simp_all

theorem checkVerticesReads_bound (P : ParentArray n) (vs : List (Fin n)) :
    (checkVerticesReads P vs).2 ≤ vs.length * n := by
  induction vs with
  | nil => simp [checkVerticesReads]
  | cons v vs ih =>
    simp only [checkVerticesReads, followReads_spec, List.length_cons]
    split <;> simp_all [Nat.add_mul]
    omega

def validateReads (P : ParentArray n) : Bool × ℕ :=
  if parent P P.root = P.root then
    let out := checkVerticesReads P (List.finRange n)
    (out.1, out.2 + 1)
  else (false, 1)

theorem validateReads_value (P : ParentArray n) : (validateReads P).1 = validateB P := by
  simp only [validateReads, validateB]
  split <;> simp_all [checkVerticesReads_value]

theorem validateReads_bound (P : ParentArray n) : (validateReads P).2 ≤ n * n + 1 := by
  have h := checkVerticesReads_bound P (List.finRange n)
  simp only [List.length_finRange] at h
  unfold validateReads
  split <;> simp_all

def denominatorsPositiveB (ds : List ℕ) (budget : ℕ) : Bool :=
  decide (0 < budget) && ds.all (fun d => decide (0 < d))

theorem denominatorsPositiveB_eq_true (ds : List ℕ) (budget : ℕ) :
    denominatorsPositiveB ds budget = true ↔ 0 < budget ∧ ∀ d ∈ ds, 0 < d := by
  simp [denominatorsPositiveB, List.all_eq_true]

theorem ordinary_parent_chain : (decodeParents 0 [0, 0, 1]).isSome = true := by decide +kernel
theorem nonfirst_root : (decodeParents 1 [1, 1, 0]).isSome = true := by decide +kernel
theorem empty_tree_rejected : (decodeParents 0 []).isSome = false := by decide +kernel
theorem invalid_index_rejected : (decodeParents 0 [0, 4]).isSome = false := by decide +kernel
theorem nonroot_self_loop_rejected : (decodeParents 0 [0, 1]).isSome = false := by decide +kernel
theorem nonroot_cycle_rejected : (decodeParents 0 [0, 2, 1]).isSome = false := by decide +kernel
theorem zero_denominator_rejected : denominatorsPositiveB [2, 0, 4] 3 = false := by decide +kernel

end UAVProof.TreeBudgetParentArray

#print axioms UAVProof.TreeBudgetParentArray.ParentArray
#print axioms UAVProof.TreeBudgetParentArray.parent
#print axioms UAVProof.TreeBudgetParentArray.follow
#print axioms UAVProof.TreeBudgetParentArray.Valid
#print axioms UAVProof.TreeBudgetParentArray.validateB
#print axioms UAVProof.TreeBudgetParentArray.validateB_eq_true
#print axioms UAVProof.TreeBudgetParentArray.follow_fixed
#print axioms UAVProof.TreeBudgetParentArray.parent_ne_self
#print axioms UAVProof.TreeBudgetParentArray.graph
#print axioms UAVProof.TreeBudgetParentArray.graph_adj
#print axioms UAVProof.TreeBudgetParentArray.reachable_follow
#print axioms UAVProof.TreeBudgetParentArray.graph_connected
#print axioms UAVProof.TreeBudgetParentArray.graph_isTree
#print axioms UAVProof.TreeBudgetParentArray.depth
#print axioms UAVProof.TreeBudgetParentArray.depth_spec
#print axioms UAVProof.TreeBudgetParentArray.depth_le
#print axioms UAVProof.TreeBudgetParentArray.depth_parent
#print axioms UAVProof.TreeBudgetParentArray.toRootedTree
#print axioms UAVProof.TreeBudgetParentArray.toRootedTree_parent
#print axioms UAVProof.TreeBudgetParentArray.toRootedTree_root
#print axioms UAVProof.TreeBudgetParentArray.decodeParents
#print axioms UAVProof.TreeBudgetParentArray.decodeParents_invalid_root
#print axioms UAVProof.TreeBudgetParentArray.decodeParents_invalid_index
#print axioms UAVProof.TreeBudgetParentArray.decodeParents_spec
#print axioms UAVProof.TreeBudgetParentArray.followReads
#print axioms UAVProof.TreeBudgetParentArray.followReads_spec
#print axioms UAVProof.TreeBudgetParentArray.checkVerticesReads
#print axioms UAVProof.TreeBudgetParentArray.checkVerticesReads_value
#print axioms UAVProof.TreeBudgetParentArray.checkVerticesReads_bound
#print axioms UAVProof.TreeBudgetParentArray.validateReads
#print axioms UAVProof.TreeBudgetParentArray.validateReads_value
#print axioms UAVProof.TreeBudgetParentArray.validateReads_bound
#print axioms UAVProof.TreeBudgetParentArray.denominatorsPositiveB
#print axioms UAVProof.TreeBudgetParentArray.denominatorsPositiveB_eq_true
#print axioms UAVProof.TreeBudgetParentArray.ordinary_parent_chain
#print axioms UAVProof.TreeBudgetParentArray.nonfirst_root
#print axioms UAVProof.TreeBudgetParentArray.empty_tree_rejected
#print axioms UAVProof.TreeBudgetParentArray.invalid_index_rejected
#print axioms UAVProof.TreeBudgetParentArray.nonroot_self_loop_rejected
#print axioms UAVProof.TreeBudgetParentArray.nonroot_cycle_rejected
#print axioms UAVProof.TreeBudgetParentArray.zero_denominator_rejected
