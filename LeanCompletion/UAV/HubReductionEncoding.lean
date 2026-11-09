import LeanCompletion.UAV.HubReductionCodec
import LeanCompletion.UAV.HubNumberedInstance

/-! Sparse-record interpretation, the existing numbered route model, and the
paper's exact and linear bit-length bounds. No runtime theorem is claimed. -/
namespace UAVProof.HubReductionEncoding
open HubGammaCodec HubReductionCodec HubNumberedInstance

def sourceWeights (s : Source) (h : SourceShape s) : HubThreePartition.Item s.m → ℕ :=
  fun i => s.items.get ⟨i.val, by have := i.isLt; unfold SourceShape at h; omega⟩

def canonicalTarget (s : Source) : Target where
  n := 3*s.m+2
  routes := s.m
  budget := s.budget
  edges := (0,s.m) :: List.replicate (3*s.m) (1,1)
  demands := 0 :: 4*s.m :: List.replicate (3*s.m) 1
  costs := 0 :: 0 :: s.items

theorem canonicalTarget_wellFormed (s : Source) (h : SourceShape s) :
    TargetWellFormed (canonicalTarget s) := by
  refine ⟨by simp [canonicalTarget], by simp [canonicalTarget],
    by simp [canonicalTarget], by simpa [canonicalTarget, SourceShape] using h, ?_⟩
  intro i
  obtain ⟨i,hi⟩ := i
  cases i with
  | zero => simp [canonicalTarget]
  | succ i => simp [canonicalTarget, List.get_eq_getElem]

def edgeAt (t : Target) (v : ℕ) : ℕ × ℕ := t.edges[v-1]?.getD (0,0)

/-- Interpret a parent edge in both directions, with its stored multiplicity. -/
def sparseFlow (t : Target) (u v : Fin t.n) : ℕ :=
  if 0 < v.val ∧ (edgeAt t v.val).1 = u.val then (edgeAt t v.val).2
  else if 0 < u.val ∧ (edgeAt t u.val).1 = v.val then (edgeAt t u.val).2
  else 0

def sparseDemand (t : Target) (v : Fin t.n) : ℕ := t.demands[v.val]?.getD 0
def sparseService (t : Target) (v : Fin t.n) : ℚ := (t.costs[v.val]?.getD 0 : ℕ)

def SparseFeasible (t : Target) : Prop :=
  ∃ h : 0 < t.n, SupportExactFeasibility.ExactFeasible ⟨0,h⟩
    (sparseFlow t) (sparseDemand t) t.routes (sparseService t) (t.budget : ℚ)

@[simp] theorem canonical_edge_hub (s : Source) : edgeAt (canonicalTarget s) 1 = (0,s.m) := rfl

@[simp] theorem canonical_edge_leaf (s : Source) (i : HubThreePartition.Item s.m) :
    edgeAt (canonicalTarget s) (i.val+2) = (1,1) := by
  simp [edgeAt, canonicalTarget, i.isLt]

theorem canonicalTarget_flow (s : Source) (u v : Vertex s.m) :
    sparseFlow (canonicalTarget s) u v = numberedFlow s.m u v := by
  rcases vertex_cases u with rfl | rfl | ⟨i,rfl⟩ <;>
    rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩ <;>
    simp [sparseFlow, numberedFlow, depotN, hubN, leafN, Fin.val_succ,
      Nat.add_assoc, canonical_edge_leaf]

theorem canonicalTarget_demand (s : Source) (v : Vertex s.m) :
    sparseDemand (canonicalTarget s) v = numberedDemand s.m v := by
  rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
  · simp [sparseDemand, canonicalTarget, numberedDemand, depotN]
  · simp [sparseDemand, canonicalTarget, numberedDemand, hubN]
  · simp [sparseDemand, canonicalTarget, numberedDemand, leafN, i.isLt]

theorem canonicalTarget_service (s : Source) (h : SourceShape s) (v : Vertex s.m) :
    sparseService (canonicalTarget s) v = numberedService (sourceWeights s h) v := by
  rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
  · simp [sparseService, canonicalTarget, numberedService, depotN]
  · simp [sparseService, canonicalTarget, numberedService, hubN]
  · have hi : i.val < s.items.length := by have := i.isLt; unfold SourceShape at h; omega
    simp [sparseService, canonicalTarget, numberedService, leafN, sourceWeights,
      List.getElem?_eq_getElem hi, List.get_eq_getElem]

theorem canonicalTarget_feasible_iff (s : Source) (h : SourceShape s) :
    SparseFeasible (canonicalTarget s) ↔
      HubThreePartition.RoutingFeasible (sourceWeights s h) s.budget := by
  rw [← numbered_routing_iff]
  have hf := funext (fun u => funext (canonicalTarget_flow s u))
  have hd := funext (canonicalTarget_demand s)
  have hc := funext (canonicalTarget_service s h)
  unfold SparseFeasible
  rw [hf, hd, hc]
  simp [canonicalTarget, NumberedRoutingFeasible, depotN]
  rfl

theorem canonicalTarget_threePartition_iff (s : Source) (h : SourceShape s)
    (hv : HubThreePartition.ValidInput (sourceWeights s h) s.budget) :
    SparseFeasible (canonicalTarget s) ↔
      HubThreePartition.ThreePartition (sourceWeights s h) s.budget := by
  rw [canonicalTarget_feasible_iff s h]
  exact HubThreePartition.exact_iff_threePartition _ _ hv

theorem encodeAll_length (xs : List ℕ) :
    (encodeAll xs).length = (xs.map gammaLength).sum := by
  induction xs with
  | nil => rfl
  | cons n xs ih => simp_all [encodeAll]

@[simp] theorem gammaLength_zero : gammaLength 0 = 1 := rfl
@[simp] theorem gammaLength_one : gammaLength 1 = 3 := rfl

theorem encodeSource_length (s : Source) :
    (encodeSource s).length = gammaLength s.m + gammaLength s.budget +
      (s.items.map gammaLength).sum := by
  simp [encodeSource, sourceFields, encodeAll_length, Nat.add_assoc]

theorem edgeFields_weight (es : List (ℕ × ℕ)) :
    ((edgeFields es).map gammaLength).sum =
      (es.map (fun p => gammaLength p.1 + gammaLength p.2)).sum := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    change gammaLength p.1 + (gammaLength p.2 + ((edgeFields es).map gammaLength).sum) =
      (gammaLength p.1 + gammaLength p.2) +
        (es.map (fun p => gammaLength p.1 + gammaLength p.2)).sum
    rw [ih]; omega

theorem encodeTarget_length (t : Target) :
    (encodeTarget t).length = gammaLength t.n + gammaLength t.routes +
      gammaLength t.budget +
      (t.edges.map (fun p => gammaLength p.1 + gammaLength p.2)).sum +
      (t.demands.map gammaLength).sum + (t.costs.map gammaLength).sum := by
  simp [encodeTarget, targetFields, encodeAll_length, edgeFields_weight, Nat.add_assoc]

theorem canonicalTarget_length_exact (s : Source) :
    (encodeTarget (canonicalTarget s)).length = (encodeSource s).length +
      gammaLength (3*s.m+2) + gammaLength s.m + gammaLength (4*s.m) + 27*s.m+4 := by
  rw [encodeTarget_length, encodeSource_length]
  simp [canonicalTarget]
  omega

theorem gammaLength_scale (m n : ℕ) (h : n + 1 ≤ 4 * (m + 1)) :
    gammaLength n ≤ gammaLength m + 4 := by
  have hs := Nat.size_le_size h
  have ht : (4*(m+1)).size = (m+1).size+2 := by
    have := Nat.size_shiftLeft (m := m+1) (by omega) 2
    simpa [Nat.shiftLeft_eq_mul_pow, Nat.mul_comm] using this
  have hp : 0 < (m+1).size := Nat.size_pos.mpr (by omega)
  rw [ht] at hs
  unfold gammaLength
  omega

theorem gammaLength_pos (n : ℕ) (h : 0 < n) : 3 ≤ gammaLength n := by
  have hs := Nat.size_le_size (show 2 ≤ n+1 by omega)
  have htwo : Nat.size 2 = 2 := rfl
  rw [htwo] at hs
  unfold gammaLength; omega

theorem item_length_lower (xs : List ℕ) (h : ∀ n ∈ xs, 0 < n) :
    3*xs.length ≤ (xs.map gammaLength).sum := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
    have hn := gammaLength_pos n (h n (by simp))
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem canonicalTarget_length_le_of_positive (s : Source) (h : SourceShape s)
    (hb : 0 < s.budget) (ha : ∀ a ∈ s.items, 0 < a) :
    (encodeTarget (canonicalTarget s)).length ≤ 4*(encodeSource s).length+3 := by
  have h1 := gammaLength_scale s.m (3*s.m+2) (by omega)
  have h2 := gammaLength_scale s.m (4*s.m) (by omega)
  have h3 := gammaLength_pos s.budget hb
  have h4 := item_length_lower s.items ha
  unfold SourceShape at h
  rw [canonicalTarget_length_exact, encodeSource_length]
  omega

theorem canonicalTarget_length_le_of_valid (s : Source) (h : SourceShape s)
    (hv : HubThreePartition.ValidInput (sourceWeights s h) s.budget) :
    (encodeTarget (canonicalTarget s)).length ≤ 4*(encodeSource s).length+3 := by
  apply canonicalTarget_length_le_of_positive s h hv.1
  intro a ha
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
  have hi' : i < 3*s.m := by unfold SourceShape at h; omega
  have := HubThreePartition.input_item_pos _ _ hv ⟨i,hi'⟩
  simpa [sourceWeights, List.get_eq_getElem, he] using this

end UAVProof.HubReductionEncoding
