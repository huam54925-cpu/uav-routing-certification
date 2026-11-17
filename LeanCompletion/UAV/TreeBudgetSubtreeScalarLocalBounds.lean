import LeanCompletion.UAV.TreeBudgetSubtreeScalarExecutor

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
open TreeBudgetSubtreeResourceSeed TreeBudgetSubtreeIntegerWitnessSeed TreeFlowExistence
variable {N m : Nat}

@[simp] theorem logicalWork_add (s t : DPStats) :
    logicalWork (s.add t) = logicalWork s + logicalWork t := by
  simp only [logicalWork, DPStats.add]; omega

@[simp] theorem payloadWork_add (s t : PayloadStats) :
    (s.add t).work = s.work+t.work := by simp only [PayloadStats.work, PayloadStats.add]; omega

@[simp] theorem logicalWork_sum (xs : List DPStats) :
    logicalWork (sumStats xs) = (xs.map logicalWork).sum := by
  induction xs with
  | nil => rfl
  | cons s ss ih => simp only [sumStats, logicalWork_add, List.map_cons, List.sum_cons, ih]

@[simp] theorem payloadWork_sum (xs : List PayloadStats) :
    (sumPayload xs).work = (xs.map PayloadStats.work).sum := by
  induction xs with
  | nil => rfl
  | cons s ss ih => simp only [sumPayload, payloadWork_add, List.map_cons, List.sum_cons, ih]

@[simp] theorem collectR_work {α : Type} (xs : List (ResourceResult α)) :
    resourceWork (collectR xs) = (xs.map resourceWork).sum := by
  change logicalWork (sumStats (xs.map ResourceResult.keyStats))+
    (sumPayload (xs.map ResourceResult.payload)).work =
      (xs.map fun r => logicalWork r.keyStats+r.payload.work).sum
  simp only [logicalWork_sum, payloadWork_sum, List.map_map, Function.comp_def, List.sum_map_add]

theorem mapC_constant_ops {α β : Type} (f : α → Counted β) (xs : List α) (k : Nat)
    (h : ∀ x ∈ xs, (f x).ops = k) : (mapC f xs).ops = (k+3)*xs.length+1 := by
  induction xs with
  | nil => simp [mapC]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [mapC, List.length_cons]
    rw [hx, ht]
    ring

theorem filterC_bound {α : Type} (f : α → Counted Bool) (xs : List α) (k : Nat)
    (h : ∀ x ∈ xs, (f x).ops ≤ k) : (filterC f xs).ops ≤ (k+4)*xs.length+1 := by
  induction xs with
  | nil => simp [filterC]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [filterC, List.length_cons]; nlinarith

theorem crossC_ops {α β γ : Type} (f : α → β → Counted γ) (xs : List α) (ys : List β)
    (k : Nat) (h : ∀ x ∈ xs, ∀ y ∈ ys, (f x y).ops = k) :
    (flatMapC (fun x => mapC (f x) ys) xs).ops =
      (k+6)*(flatMapC (fun x => mapC (f x) ys) xs).value.length + 5*xs.length+1 := by
  induction xs with
  | nil => simp [flatMapC]
  | cons x xs ih =>
    have hx := mapC_constant_ops (f x) ys k (h x (by simp))
    have ht := ih (fun z hz => h z (by simp [hz]))
    simp only [flatMapC, (appendC_spec _ _).1, (appendC_spec _ _).2,
      List.length_append, mapC_value, List.length_map, List.length_cons] at *
    nlinarith

theorem dedupC_work_bound {α κ : Type} (key : α → κ) (eq : κ → κ → Counted Bool)
    (k : Nat) (hk : ∀ x y, (eq x y).ops ≤ k) (xs : List α) :
    (dedupC key eq xs).ops ≤ (k+14)*(1+resourceWork (dedupC key eq xs).value) := by
  have h := dedupC_bound key eq k hk xs
  apply h.trans
  apply Nat.mul_le_mul_left
  simp only [dedupC, resourceWork, logicalWork, PayloadStats.work]
  omega

theorem inside_step_arithmetic (m k t a e R D cr cf cp cd : Nat)
    (hi : cr ≤ 64*(m+1)*(k+1+R)) (hf : cf ≤ (9*m+7)*t+1) (he : e ≤ t)
    (hp : cp = (8*m+12)*a+5*e+1) (hd : cd ≤ (8*m+16)*(1+D)) :
    cr+cf+cp+cd+5 ≤ 64*(m+1)*(k+1+1+(R+t+(m+2)*a+D)) := by
  nlinarith [Nat.zero_le (m*m*a), Nat.zero_le (m*a), Nat.zero_le (m*t), Nat.zero_le (m*D)]

theorem roots_step_arithmetic (m k t L a z R D cr cp cf cd : Nat)
    (hi : cr ≤ 128*(m+1)*(k+1+L+R))
    (hp : cp = (17*m+15)*a+5*t+1) (hf : cf ≤ (7*m+7)*a+1)
    (hd : cd ≤ (16*m+19)*(1+D)) :
    cr+cp+cf+cd+5 ≤ 128*(m+1)*(k+1+1+(t+L)+(R+(m+2)*a+z+D)) := by
  nlinarith [Nat.zero_le (m*m*a), Nat.zero_le (m*a), Nat.zero_le (m*t),
    Nat.zero_le (m*D), Nat.zero_le (m*z)]

theorem rootKey_bound (x y : TreeBudgetSubtreeInteger.IntRoot m) :
    (rootEqC x y).ops ≤ 16*m+5 := fieldsEqC_bound x.used y.used x.cost y.cost

theorem stateKey_bound (x y : TreeBudgetSubtreeInteger.IntState m) :
    (stateEqC x y).ops ≤ 16*m+5 := fieldsEqC_bound x.active y.active x.cost y.cost

theorem insideC_bound (a : Vector Bool m) (base : Vector Int m)
    (ts : List (List (Entry N m))) :
    (insideC a base ts).ops ≤
      64*(m+1)*(ts.length+1+resourceWork (insideC a base ts).value) := by
  induction ts with
  | nil => simp [insideC, resourceWork, logicalWork, PayloadStats.work]; omega
  | cons t ts ih =>
    let r := insideC a base ts
    let eligible := filterC (fun e : Entry N m =>
      let c := subsetC e.key.active a; ⟨c.value, c.ops+1⟩) t
    let raw := flatMapC (fun e => mapC (insidePairC e) r.value.value) eligible.value
    let d := dedupC Inside.cost vectorEqC raw.value
    have hf : eligible.ops ≤ (9*m+7)*t.length+1 :=
      filterC_bound _ t (9*m+3) (by intro e _; exact Nat.add_le_add_right (subsetC_bound _ _) 1)
    have hlen : eligible.value.length ≤ t.length := by
      dsimp [eligible]; rw [filterC_value]; exact List.length_filter_le _ _
    have hp : raw.ops = (8*m+12)*raw.value.length+5*eligible.value.length+1 := by
      apply crossC_ops _ _ _ (8*m+6)
      intro e _ b _
      simp [insidePairC, addC]; omega
    have hd : d.ops ≤ (8*m+16)*(1+resourceWork d.value) :=
      dedupC_work_bound _ _ (8*m+2) vectorEqC_bound _
    have hw : resourceWork (insideC a base (t::ts)).value =
        resourceWork r.value+t.length+(m+2)*raw.value.length+resourceWork d.value := by
      change logicalWork (r.value.keyStats.add ((insideStep m t.length raw.value.length).add d.value.keyStats))+
        (r.value.payload.add (({pickCons := raw.value.length} : PayloadStats).add d.value.payload)).work = _
      simp only [logicalWork_add, payloadWork_add]
      simp only [resourceWork, insideStep, logicalWork, PayloadStats.work]
      ring
    rw [hw]
    change r.ops ≤ _ at ih
    change r.ops+eligible.ops+raw.ops+d.ops+5 ≤
      64*(m+1)*(ts.length+1+1+(resourceWork r.value+t.length+(m+2)*raw.value.length+resourceWork d.value))
    exact inside_step_arithmetic m ts.length t.length raw.value.length eligible.value.length
      (resourceWork r.value) (resourceWork d.value) r.ops eligible.ops raw.ops d.ops ih hf hlen hp hd

set_option maxHeartbeats 800000 in
theorem rootsC_bound (ts : List (List (Entry N m))) :
    (rootsC ts).ops ≤ 128*(m+1)*
      (ts.length+1+(ts.map List.length).sum+resourceWork (rootsC ts).value) := by
  induction ts with
  | nil => simp [rootsC, resourceWork, logicalWork, PayloadStats.work]; omega
  | cons t ts ih =>
    let r := rootsC ts
    let raw := flatMapC (fun e => mapC (rootPairC e) r.value.value) t
    let kept := filterC (fun r : Root N m => let c := capC r.key; ⟨c.value, c.ops+1⟩) raw.value
    let d := dedupC Root.key rootEqC kept.value
    have hp : raw.ops = (17*m+15)*raw.value.length+5*t.length+1 := by
      apply crossC_ops _ _ _ (17*m+9)
      intro e _ b _; simp [rootPairC]
    have hf : kept.ops ≤ (7*m+7)*raw.value.length+1 :=
      filterC_bound _ _ (7*m+3) (by intro r _; exact Nat.add_le_add_right (capC_bound _) 1)
    have hd : d.ops ≤ (16*m+19)*(1+resourceWork d.value) :=
      dedupC_work_bound Root.key rootEqC (16*m+5) rootKey_bound kept.value
    have hw : resourceWork (rootsC (t::ts)).value =
        resourceWork r.value+(m+2)*raw.value.length+
        (raw.value.length-kept.value.length)+resourceWork d.value := by
      change logicalWork (r.value.keyStats.add ((rootStep m raw.value.length kept.value.length).add d.value.keyStats))+
        (r.value.payload.add (({pickCons := raw.value.length} : PayloadStats).add d.value.payload)).work = _
      simp only [logicalWork_add, payloadWork_add]
      simp only [resourceWork, rootStep, logicalWork, PayloadStats.work]
      ring
    rw [hw]
    change r.ops ≤ _ at ih
    change r.ops+raw.ops+kept.ops+d.ops+5 ≤
      128*(m+1)*(ts.length+1+1+(t.length+(ts.map List.length).sum)+
        (resourceWork r.value+(m+2)*raw.value.length+
          (raw.value.length-kept.value.length)+resourceWork d.value))
    exact roots_step_arithmetic m ts.length t.length (ts.map List.length).sum raw.value.length
      (raw.value.length-kept.value.length) (resourceWork r.value) (resourceWork d.value)
      r.ops raw.ops kept.ops d.ops ih hp hf hd

end UAVProof.TreeBudgetSubtreeScalar
