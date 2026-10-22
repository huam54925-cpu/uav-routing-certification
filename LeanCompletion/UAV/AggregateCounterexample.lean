import LeanCompletion.UAV.LPBridge

namespace UAVProof.Research.AggregateCounterexample

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Node := Fin 4

def depot : Node := 0

def required (i : Node) : Nat :=
  if i = depot then 0 else 1

def prescribedDegree (i : Node) : Nat :=
  if i = depot then 2 else required i

-- Unit flow on 0->1->0 and 0->2->3->0.
def witness (i j : Node) : Nat :=
  if (i = 0 ∧ j = 1) ∨
     (i = 1 ∧ j = 0) ∨
     (i = 0 ∧ j = 2) ∨
     (i = 2 ∧ j = 3) ∨
     (i = 3 ∧ j = 0)
  then 1 else 0

def position (i : Node) : Rat :=
  i.val

-- Speed is 1, so distance equals flight time.
def flightCost (e : Prod Node Node) : Rat :=
  abs (position e.1 - position e.2)

def totalFlight (x : Node -> Node -> Nat) : Rat :=
  (LPBridge.arcSet (V := Node)).sum
    (fun e => flightCost e * LPBridge.flow x e)

def totalService : Rat :=
  (Finset.univ : Finset Node).sum
    (fun i => 3 * (required i : Rat))

-- These are the existing LPBridge constraints.
-- The cut quantifier ranges over ALL finite subsets.
def BaseConstraints (x : Node -> Node -> Nat) : Prop :=
  (forall i, x i i = 0) ∧
  (forall e : Prod Node Node,
    0 <= LPBridge.flow x e ∧
    LPBridge.flow x e <=
      LPBridge.capacity prescribedDegree e) ∧
  (forall h : Sum Node Node,
    (LPBridge.arcSet (V := Node)).sum
      (fun e => LPBridge.eqMatrix h e * LPBridge.flow x e) =
        LPBridge.rhs prescribedDegree h) ∧
  (forall S : Finset Node,
    LPBridge.ValidCut depot required S ->
      1 <= (LPBridge.arcSet (V := Node)).sum
        (fun e => LPBridge.cutMatrix S e * LPBridge.flow x e))

theorem witness_base_constraints :
    BaseConstraints witness := by
  unfold BaseConstraints LPBridge.ValidCut
  decide +kernel

theorem witness_flight :
    totalFlight witness = 8 := by
  decide +kernel

theorem service_total :
    totalService = 9 := by
  decide +kernel

theorem witness_total_time :
    totalFlight witness + totalService = 17 := by
  rw [witness_flight, service_total]
  norm_num

theorem witness_total_budget :
    totalFlight witness + totalService <= (2 : Rat) * 9 := by
  rw [witness_total_time]
  norm_num

theorem aggregate_witness :
    BaseConstraints witness ∧
      totalFlight witness + totalService <= (2 : Rat) * 9 := by
  exact ⟨witness_base_constraints, witness_total_budget⟩

#print axioms witness_base_constraints
#print axioms aggregate_witness

-- Flight time of an actual legal route.
def routeFlight (r : LegalRoute depot) : Rat :=
  (Finset.univ : Finset (Prod Node Node)).sum
    (fun e =>
      flightCost e *
        (routeFlow r.vertices e.1 e.2 : Rat))

-- Each visit requires exactly three hours of service.
def routeTime (r : LegalRoute depot) : Rat :=
  routeFlight r + 3 * (r.visits.length : Rat)

theorem routeFlight_nonneg (r : LegalRoute depot) :
    0 <= routeFlight r := by
  unfold routeFlight
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · unfold flightCost
    exact abs_nonneg _
  · exact Nat.cast_nonneg _

theorem service_time_le_routeTime (r : LegalRoute depot) :
    3 * (r.visits.length : Rat) <= routeTime r := by
  have hf := routeFlight_nonneg r
  unfold routeTime
  linarith

theorem timed_route_length_le_three
    (r : LegalRoute depot)
    (htime : routeTime r <= 9) :
    r.visits.length <= 3 := by
  have hs := service_time_le_routeTime r
  have hlength : (r.visits.length : Rat) <= (3 : Rat) := by
    linarith
  exact_mod_cast hlength

#print axioms timed_route_length_le_three


end UAVProof.Research.AggregateCounterexample
