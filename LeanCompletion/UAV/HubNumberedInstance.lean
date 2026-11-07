import LeanCompletion.UAV.HubThreePartition

/-!
# Numbered strict-hub instances

The numbered vertex set used in the binary-format paper is identified with
the existing Option/Option hub model. This file transports actual route lists,
occurrence counts, exact directed flow and signed service costs. It does not
implement binary parsing or establish a machine-cost bound.
-/

namespace UAVProof.HubNumberedInstance

open HubSpokeSupportExact SupportExactFeasibility ResourceCuts

namespace Relabel

variable {V W : Type*}

/-- Relabel the task list, retaining each occurrence and its order. -/
def mapRoute (e : V ≃ W) {o : V} (r : LegalRoute o) : LegalRoute (e o) where
  visits := r.visits.map e
  visits_nonempty := by simpa using r.visits_nonempty
  depot_not_mem := by simpa using r.depot_not_mem
  adjacent_ne := by
    have h := List.isChain_map_of_isChain (S := (· ≠ ·)) e
      (fun a b (hab : a ≠ b) heq => hab (e.injective heq)) r.adjacent_ne
    simpa [depotRoute] using h

@[simp] theorem mapRoute_vertices (e : V ≃ W) {o : V} (r : LegalRoute o) :
    (mapRoute e r).vertices = r.vertices.map e := by
  simp [mapRoute, LegalRoute.vertices, depotRoute]

theorem map_count [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (l : List V) (v : V) : (l.map e).count (e v) = l.count v :=
  List.count_map_of_injective l e e.injective v

theorem map_flow [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (l : List V) (u v : V) :
    routeFlow (l.map e) (e u) (e v) = routeFlow l u v := by
  induction l with
  | nil => simp [routeFlow]
  | cons a l ih =>
    cases l with
    | nil => simp [routeFlow]
    | cons b l =>
      simpa [routeFlow, List.count_cons] using ih

theorem mapRoute_count [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) {o : V} (r : LegalRoute o) (v : V) :
    (mapRoute e r).visits.count (e v) = r.visits.count v :=
  map_count e r.visits v

theorem mapRoute_flow [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) {o : V} (r : LegalRoute o) (u v : V) :
    routeFlow (mapRoute e r).vertices (e u) (e v) = routeFlow r.vertices u v := by
  rw [mapRoute_vertices]
  exact map_flow e r.vertices u v

theorem mapRoute_service [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) {o : V} (r : LegalRoute o) (s : W → ℚ) :
    routeServiceIn (mapRoute e r) Finset.univ s =
      routeServiceIn r Finset.univ (fun v => s (e v)) := by
  unfold routeServiceIn
  rw [← e.sum_comp (fun w => s w * ((mapRoute e r).visits.count w : ℚ))]
  simp [mapRoute_count]

theorem exactFeasible_forward [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (o : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ)
    (h : ExactFeasible o x d m s T) :
    ExactFeasible (e o) (fun u v => x (e.symm u) (e.symm v))
      (fun v => d (e.symm v)) m (fun v => s (e.symm v)) T := by
  obtain ⟨rs, hc, hb, hf⟩ := h
  refine ⟨fun r => mapRoute e (rs r), ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨v, rfl⟩ := e.surjective v
    have hvo : v ≠ o := fun heq => hv (congrArg e heq)
    simpa [totalVisitCount, mapRoute_count] using hc v hvo
  · intro r
    simpa [mapRoute_service] using hb r
  · intro u v
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    simpa only [totalRouteFlow, mapRoute_flow, e.symm_apply_apply] using hf u v

theorem exactFeasible_iff [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (o : V) (x : W → W → ℕ) (d : W → ℕ) (m : ℕ)
    (s : W → ℚ) (T : ℚ) :
    ExactFeasible o (fun u v => x (e u) (e v)) (fun v => d (e v))
      m (fun v => s (e v)) T ↔ ExactFeasible (e o) x d m s T := by
  constructor
  · intro h
    simpa using exactFeasible_forward e o _ _ m _ T h
  · intro h
    simpa using exactFeasible_forward e.symm (e o) x d m s T h

end Relabel

abbrev Vertex (m : ℕ) := Fin (3 * m + 2)

def depotN (m : ℕ) : Vertex m := 0
def hubN (m : ℕ) : Vertex m := 1
def leafN {m : ℕ} (i : HubThreePartition.Item m) : Vertex m := i.succ.succ

/-- Two successive zero/successor decompositions: 0 is depot, 1 is hub. -/
def nodeEquiv (m : ℕ) : Vertex m ≃ Node (HubThreePartition.Item m) :=
  (finSuccEquiv (3 * m + 1)).trans (Equiv.optionCongr (finSuccEquiv (3 * m)))

@[simp] theorem nodeEquiv_depot (m : ℕ) : nodeEquiv m (depotN m) = depot := by
  simp [nodeEquiv, depotN, depot]

@[simp] theorem nodeEquiv_hub (m : ℕ) : nodeEquiv m (hubN m) = hub := by
  change (nodeEquiv m) (0 : Fin (3 * m + 1)).succ = hub
  simp [nodeEquiv, hub]

@[simp] theorem nodeEquiv_leaf {m : ℕ} (i : HubThreePartition.Item m) :
    nodeEquiv m (leafN i) = satellite i := by
  simp [nodeEquiv, leafN, satellite]

theorem vertex_cases {m : ℕ} (v : Vertex m) :
    v = depotN m ∨ v = hubN m ∨ ∃ i, v = leafN i := by
  obtain h | ⟨v, rfl⟩ := Fin.eq_zero_or_eq_succ v
  · exact Or.inl h
  obtain h | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ v
  · exact Or.inr (Or.inl (congrArg Fin.succ h))
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

/-- Independent numerical formula for the sparse symmetric flow. -/
def numberedFlow (m : ℕ) (u v : Vertex m) : ℕ :=
  if (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) then m
  else if (u.val = 1 ∧ 2 ≤ v.val) ∨ (2 ≤ u.val ∧ v.val = 1) then 1 else 0

def numberedDemand (m : ℕ) (v : Vertex m) : ℕ :=
  if v.val = 0 then 0 else if v.val = 1 then 4 * m else 1

def numberedService {m : ℕ} (a : HubThreePartition.Item m → ℕ)
    (v : Vertex m) : ℚ :=
  if hv : 2 ≤ v.val then a ⟨v.val - 2, by have := v.isLt; omega⟩ else 0

theorem numberedFlow_eq (m : ℕ) (u v : Vertex m) :
    numberedFlow m u v = canonicalFlow m (fun _ => 1) (nodeEquiv m u) (nodeEquiv m v) := by
  rcases vertex_cases u with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases vertex_cases v with rfl | rfl | ⟨j, rfl⟩ <;>
    simp only [nodeEquiv_depot, nodeEquiv_hub, nodeEquiv_leaf] <;>
    simp [numberedFlow, depotN, hubN, leafN,
      canonicalFlow, Fin.val_succ, depot, hub, satellite]

theorem numberedDemand_eq (m : ℕ) (v : Vertex m) :
    numberedDemand m v = required m (fun _ => 1) (nodeEquiv m v) := by
  rcases vertex_cases v with rfl | rfl | ⟨i, rfl⟩
  · rw [nodeEquiv_depot]
    simp [numberedDemand, depotN, required, depot]
  · simpa [numberedDemand, hubN] using (@HubThreePartition.required_hub_eq m).symm
  · rw [nodeEquiv_leaf]
    simp [numberedDemand, leafN, required, satellite]

theorem numberedService_eq {m : ℕ} (a : HubThreePartition.Item m → ℕ) (v : Vertex m) :
    numberedService a v = HubThreePartition.service a (nodeEquiv m v) := by
  rcases vertex_cases v with rfl | rfl | ⟨i, rfl⟩
  · rw [nodeEquiv_depot]
    simp [numberedService, depotN, HubThreePartition.service, depot]
  · rw [nodeEquiv_hub]
    simp [numberedService, hubN, HubThreePartition.service, hub]
  · rw [nodeEquiv_leaf]
    simp [numberedService, leafN, HubThreePartition.service, satellite]

def NumberedRoutingFeasible {m : ℕ} (a : HubThreePartition.Item m → ℕ) (B : ℕ) : Prop :=
  ExactFeasible (depotN m) (numberedFlow m) (numberedDemand m) m (numberedService a) (B : ℚ)

/-- Numbered and Option/Option instances agree without source-instance promises. -/
theorem numbered_routing_iff {m : ℕ} (a : HubThreePartition.Item m → ℕ) (B : ℕ) :
    NumberedRoutingFeasible a B ↔ HubThreePartition.RoutingFeasible a B := by
  unfold NumberedRoutingFeasible HubThreePartition.RoutingFeasible
  have hf : numberedFlow m = fun u v =>
      canonicalFlow m (fun _ => 1) (nodeEquiv m u) (nodeEquiv m v) := by
    funext u v; exact numberedFlow_eq m u v
  have hd : numberedDemand m = fun v => required m (fun _ => 1) (nodeEquiv m v) := by
    funext v; exact numberedDemand_eq m v
  have hs : numberedService a = fun v => HubThreePartition.service a (nodeEquiv m v) := by
    funext v; exact numberedService_eq a v
  rw [hf, hd, hs]
  simpa using Relabel.exactFeasible_iff (nodeEquiv m) (depotN m)
    (canonicalFlow m (fun _ => 1)) (required m (fun _ => 1)) m
    (HubThreePartition.service a) (B : ℚ)

end UAVProof.HubNumberedInstance
