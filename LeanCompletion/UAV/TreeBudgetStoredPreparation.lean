import LeanCompletion.UAV.TreeBudgetStoredSearch
import LeanCompletion.UAV.TreeBudgetBinaryPipeline

/-! The production preparation path performs no search. It invokes the existing
costed normalization, scaling, candidate enumeration and root count, then builds
the actual initial heap using addressed allocations. -/
namespace UAVProof.TreeBudgetStoredPreparation
open TreeBudgetBitMachine TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSearchStore TreeBudgetSharedAnswerStore TreeBudgetChargedCache
open TreeBudgetStoredSearch TreeBudgetBinaryInput TreeBudgetBinaryCodec
open TreeBudgetBinaryPreprocessing TreeBudgetCostedCandidates TreeBudgetBinaryPipeline
open TreeBudgetVectorMemoState TreeBudgetCostedSearch TreeBudgetBinarySearch

structure Prepared (n : ℕ) where
  residual : Vector ℕ n
  candidates : List (Vector ℕ n)
  depth : ℕ

def prepareInput (I : Input) : Costed (Prepared I.n) :=
  let H := normalizeCost I.parents I.H
  let A := scaleFeesCost I.numerators I.denominators I.budgetDenominator
  let budget := scaleBudgetCost I.denominators I.budgetNumerator
  let ps := candidateCost I.parents H.value A.value budget.value
  let count := rootCountCost I.parents H.value
  ⟨⟨H.value, ps.value, count.value⟩,
    H.steps + A.steps + budget.steps + ps.steps + count.steps,
    H.allocations + A.allocations + budget.allocations + ps.allocations + count.allocations⟩

theorem prepareInput_search (I : Input) :
    (preparedSearch I).value =
      (memoCost (backend I.n) (prepareInput I).value.candidates
        (prepareInput I).value.depth (prepareInput I).value.residual []).value ∧
    (preparedSearch I).events =
      (memoCost (backend I.n) (prepareInput I).value.candidates
        (prepareInput I).value.depth (prepareInput I).value.residual []).events := ⟨rfl, rfl⟩

def rowsWrite {n : ℕ} : Heap → List (Vector ℕ n) → Costed (ℕ × Heap)
  | heap, [] => alloc heap [.bit false]
  | heap, p :: ps =>
    TreeBudgetBitMachine.bind (rowsWrite heap ps) fun tail =>
      TreeBudgetBitMachine.bind (vectorWrite tail.2 p) fun row =>
        charge 1 3 (alloc row.2 [.bit true, .ref row.1, .ref tail.1])

theorem rowsWrite_correct {n : ℕ} (heap : Heap) (ps : List (Vector ℕ n))
    (hh : WellFormed heap) :
    RowsRep (rowsWrite heap ps).value.2 (rowsWrite heap ps).value.1 (ps.map Vector.toList) ∧
      WellFormed (rowsWrite heap ps).value.2 ∧ Extends heap (rowsWrite heap ps).value.2 := by
  induction ps generalizing heap with
  | nil =>
    simp only [rowsWrite, alloc_value heap [.bit false] (by simp)]
    exact ⟨emptyRows_correct heap, failure_wellFormed heap hh, allocateBlock_extends ..⟩
  | cons p ps ih =>
    let tail := (rowsWrite heap ps).value
    obtain ⟨ht, hwt, het⟩ := ih heap hh
    let row := allocateBlob tail.2 (encodeNats p.toList)
    have hr := allocateBlob_correct tail.2 (encodeNats p.toList)
    have her : Extends tail.2 row.2 := allocateBlock_extends ..
    have hwr : WellFormed row.2 := allocateBlob_wellFormed tail.2 _ hwt
    have ht' := rowsRep_persist her _ _ ht
    have hbr := blobRep_address_lt _ _ _ hr
    have hbt := rowsRep_address_lt ht'
    have href : ∀ a, Slot.ref a ∈ [.bit true, .ref row.1, .ref tail.1] → a < row.2.size := by
      intro a ha; simp at ha
      rcases ha with rfl | rfl <;> assumption
    simp only [rowsWrite, costBind_value, vectorWrite_value, charge]
    change RowsRep (alloc row.2 [.bit true, .ref row.1, .ref tail.1]).value.2
      (alloc row.2 [.bit true, .ref row.1, .ref tail.1]).value.1 _ ∧ _
    rw [alloc_value _ _ href]
    exact ⟨prependRows_correct _ _ _ _ _ hr ht',
      prependRows_wellFormed _ _ _ hwr hbr hbt,
      extends_trans het (extends_trans her (allocateBlock_extends ..))⟩

structure Initial where
  heap : Heap
  candidates : ℕ
  residual : ℕ
  cache : ℕ
  parent : ℕ

def initializeStore {n : ℕ} (P : Prepared n) : Costed Initial :=
  TreeBudgetBitMachine.bind (alloc #[] [.bit false]) fun parent =>
    TreeBudgetBitMachine.bind (rowsWrite parent.2 P.candidates) fun candidates =>
      TreeBudgetBitMachine.bind (vectorWrite candidates.2 P.residual) fun residual =>
        TreeBudgetBitMachine.bind (alloc residual.2 [.bit false]) fun cache =>
          ⟨⟨cache.2, candidates.1, residual.1, cache.1, parent.1⟩, 1, 5⟩

def InitialRep {n : ℕ} (P : Prepared n) (state : Initial) : Prop :=
  WellFormed state.heap ∧ RowsRep state.heap state.candidates (P.candidates.map Vector.toList) ∧
    RowRep state.heap state.residual P.residual.toList ∧
    TreeBudgetChargedCache.CacheRep state.heap state.cache [] ∧
    FramesRep state.heap state.parent ∧ state.parent < state.heap.size

theorem initializeStore_correct {n : ℕ} (P : Prepared n) : InitialRep P (initializeStore P).value := by
  let parent := allocateBlock #[] [.bit false]
  have hpw : WellFormed parent := by
    apply wellFormed_allocateBlock #[] _
    · simp [WellFormed, TreeBudgetAllocationBounds.read]
    · simp
  have hpf : FramesRep parent 0 := .root 0 (allocateTyped_represents #[] [.bit false])
  let candidates := (rowsWrite parent P.candidates).value
  obtain ⟨hc, hcw, hec⟩ := rowsWrite_correct parent P.candidates hpw
  let residual := allocateBlob candidates.2 (encodeNats P.residual.toList)
  have hr := allocateBlob_correct candidates.2 (encodeNats P.residual.toList)
  have hrw : WellFormed residual.2 := allocateBlob_wellFormed candidates.2 _ hcw
  have her : Extends candidates.2 residual.2 := allocateBlock_extends ..
  have hecache := allocateBlock_extends residual.2 [.bit false]
  have he := extends_trans hec (extends_trans her hecache)
  have hcacherep : TreeBudgetChargedCache.CacheRep
      (allocateBlock residual.2 [.bit false]) residual.2.size [] :=
    .nil _ (allocateTyped_represents residual.2 [.bit false])
  simp only [initializeStore, costBind_value, alloc_value #[] [.bit false] (by simp),
    vectorWrite_value, alloc_value _ [.bit false] (by simp)]
  change InitialRep P ⟨allocateBlock residual.2 [.bit false], candidates.1,
    residual.1, residual.2.size, 0⟩
  refine ⟨failure_wellFormed _ hrw, rowsRep_persist (extends_trans her hecache) _ _ hc,
    blobRep_persist hecache _ _ hr, hcacherep, framesRep_persist he hpf, ?_⟩
  have hb := he.size_le
  have hp : parent.size = 1 := by simp [parent, allocateBlock_size]
  dsimp only
  omega

end UAVProof.TreeBudgetStoredPreparation
