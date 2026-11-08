import LeanCompletion.UAV.TreeBudgetStoredReadWork
import LeanCompletion.UAV.TreeBudgetStoredSearch

namespace UAVProof.TreeBudgetStoredNodeWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredSearch
open TreeBudgetBinaryCodec TreeBudgetSearchStore

theorem refThen_work {α : Type} (heap : Heap) (a offset W B : ℕ)
    (f : ℕ → Costed (Option α)) (hw : (a + offset).size ≤ W) (hf : ∀ x, work (f x) ≤ B) :
    work (thenD (loadRef heap a offset) f) ≤ 84 * (W + 1) + B + 1 :=
  work_then_uniform _ _ _ _ (loadRef_work heap a offset W hw) hf

set_option maxRecDepth 4096 in
theorem headRead_work (heap : Heap) (a W : ℕ) (hw : (a + 3).size ≤ W) :
    work (headRead heap a) ≤ 512 * (W + 1) := by
  have hwidth : ∀ i, i ≤ 3 → (a + i).size ≤ W :=
    fun i hi => (Nat.size_le_size (Nat.add_le_add_left hi a)).trans hw
  have ht : ∀ (k v : ℕ), work (thenD (loadRef heap a 3) fun t => ret (some (k, v, t))) ≤
      84 * (W + 1) + 2 := by
    intro k v
    simpa using refThen_work heap a 3 W 1 _ hw (fun _ => le_rfl)
  have hv : ∀ (k : ℕ), work (thenD (loadRef heap a 2) fun v =>
      thenD (loadRef heap a 3) fun t => ret (some (k, v, t))) ≤ 168 * (W + 1) + 3 := by
    intro k
    have h := refThen_work heap a 2 W _ _ (hwidth 2 (by omega)) (ht k)
    omega
  have hk := refThen_work heap a 1 W _ _ (hwidth 1 (by omega)) hv
  have hl := load_work heap a W (by simpa using hwidth 0 (by omega))
  have h := work_then_uniform (load heap a)
    (fun slot => match slot with
      | .ref _ => bad
      | .bit false => ret none
      | .bit true => thenD (loadRef heap a 1) fun k => thenD (loadRef heap a 2) fun v =>
          thenD (loadRef heap a 3) fun t => ret (some (k, v, t))) (10 * (W + 1)) (252 * (W + 1) + 4) hl (by
    intro slot
    cases slot with
    | ref _ => simp
    | bit b => cases b with
      | false => simp
      | true => exact hk.trans (by omega))
  change work (headRead heap a) ≤ _ at h
  omega

theorem rowsHead_work (heap : Heap) (a W : ℕ) (hw : (a + 2).size ≤ W) :
    work (rowsHead heap a) ≤ 256 * (W + 1) := by
  have hwidth : ∀ i, i ≤ 2 → (a + i).size ≤ W :=
    fun i hi => (Nat.size_le_size (Nat.add_le_add_left hi a)).trans hw
  have ht : ∀ (r : ℕ), work (thenD (loadRef heap a 2) fun t => ret (some (r, t))) ≤ 84 * (W + 1) + 2 := by
    intro r
    simpa using refThen_work heap a 2 W 1 _ hw (fun _ => le_rfl)
  have hk := refThen_work heap a 1 W _ _ (hwidth 1 (by omega)) ht
  have hl := load_work heap a W (by simpa using hwidth 0 (by omega))
  have h := work_then_uniform (load heap a)
    (fun slot => match slot with
      | .ref _ => bad
      | .bit false => ret none
      | .bit true => thenD (loadRef heap a 1) fun r =>
          thenD (loadRef heap a 2) fun t => ret (some (r, t))) (10 * (W + 1)) (168 * (W + 1) + 3) hl (by
    intro slot
    cases slot with
    | ref _ => simp
    | bit b => cases b with
      | false => simp
      | true => exact hk.trans (by omega))
  change work (rowsHead heap a) ≤ _ at h
  omega

theorem answerHead_work (heap : Heap) (a W : ℕ) (hw : (a + 1).size ≤ W) :
    work (answerHead heap a) ≤ 128 * (W + 1) := by
  have hk := refThen_work heap a 1 W 1 (fun r => ret (some r)) hw (fun _ => le_rfl)
  have hl := load_work heap a W ((Nat.size_le_size (Nat.le_succ a)).trans hw)
  have h := work_then_uniform (load heap a)
    (fun slot => match slot with
      | .ref _ => bad
      | .bit false => ret none
      | .bit true => thenD (loadRef heap a 1) fun r => ret (some r)) (10 * (W + 1)) (84 * (W + 1) + 2) hl (by
    intro slot
    cases slot with
    | ref _ => simp
    | bit b => cases b with
      | false => simp
      | true => exact hk)
  change work (answerHead heap a) ≤ _ at h
  omega

set_option maxRecDepth 4096 in
theorem frameRead_work (heap : Heap) (a W : ℕ) (hw : (a + 4).size ≤ W) :
    work (frameRead heap a) ≤ 512 * (W + 1) := by
  have hwidth : ∀ i, i ≤ 4 → (a + i).size ≤ W :=
    fun i hi => (Nat.size_le_size (Nat.add_le_add_left hi a)).trans hw
  have h₄ : ∀ (r t v : ℕ), work (thenD (loadRef heap a 4) fun p => ret (r, t, v, p)) ≤
      84 * (W + 1) + 2 := by
    intro r t v
    simpa using refThen_work heap a 4 W 1 _ hw (fun _ => le_rfl)
  have h₃ : ∀ (r t : ℕ), work (thenD (loadRef heap a 3) fun v =>
      thenD (loadRef heap a 4) fun p => ret (r, t, v, p)) ≤ 168 * (W + 1) + 3 := by
    intro r t
    have h := refThen_work heap a 3 W _ _ (hwidth 3 (by omega)) (h₄ r t)
    omega
  have h₂ : ∀ (r : ℕ), work (thenD (loadRef heap a 2) fun t => thenD (loadRef heap a 3) fun v =>
      thenD (loadRef heap a 4) fun p => ret (r, t, v, p)) ≤ 252 * (W + 1) + 4 := by
    intro r
    have h := refThen_work heap a 2 W _ _ (hwidth 2 (by omega)) (h₃ r)
    omega
  have h := refThen_work heap a 1 W _ _ (hwidth 1 (by omega)) h₂
  change work (frameRead heap a) ≤ _ at h
  omega

end UAVProof.TreeBudgetStoredNodeWork
