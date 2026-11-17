import LeanCompletion.UAV.TreeBudgetSubtreeScalarLocalBounds

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeFlowExistence

theorem sum_map_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem composition_length_le_calls (m h : Nat) :
    (compositionsV m h).length ≤ (compositionProfile m h).compositionCalls := by
  induction m generalizing h with
  | zero => by_cases hh : h=0 <;> simp [compositionsV, compositionProfile, hh]
  | succ m ih =>
    have hh := sum_map_mono (List.range (h+1))
      (fun a => (compositionsV m (h-a)).length)
      (fun a => (compositionProfile m (h-a)).compositionCalls) (fun a _ => ih (h-a))
    simp only [compositionsV, compositionProfile, List.length_flatMap, List.length_map,
      DPStats.add, sumStats_compositionCalls, List.map_map, Function.comp_def]
    omega

theorem compositionsC_ops_step (m h : Nat) :
    (compositionsC (m+1) h).ops =
      ((List.range (h+1)).map fun a => (compositionsC m (h-a)).ops).sum +
      (8*m+15)*(compositionsV (m+1) h).length+13*(h+1)+5 := by
  simp only [compositionsC, flatMapC_ops, List.map_map, Function.comp_def,
    mapC_value, List.length_map, mapC_ops, mapWork_eq, consC_ops,
    compositionsC_value, compositionsStats_erase, List.length_range,
    compositionsV, List.length_flatMap, List.length_map]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.sum_map_add,
    List.sum_map_mul_left]
  simp only [Nat.mul_add, Nat.add_mul, List.sum_map_add, List.sum_map_mul_right,
    List.sum_map_mul_left, List.length_range]
  ring

theorem compositionsC_bound (m h : Nat) :
    (compositionsC m h).ops ≤ 32*(m+1)^2*(compositionProfile m h).compositionCalls := by
  induction m generalizing h with
  | zero => simp [compositionsC, compositionProfile]
  | succ m ih =>
    let S := ((List.range (h+1)).map fun a => (compositionProfile m (h-a)).compositionCalls).sum
    have hs := sum_map_mono (List.range (h+1))
      (fun a => (compositionsC m (h-a)).ops)
      (fun a => 32*(m+1)^2*(compositionProfile m (h-a)).compositionCalls) (fun a _ => ih _)
    rw [List.sum_map_mul_left] at hs
    change _ ≤ 32*(m+1)^2*S at hs
    have hcalls : (compositionProfile (m+1) h).compositionCalls = 1+S := by
      simp [compositionProfile, DPStats.add, sumStats_compositionCalls, List.map_map,
        Function.comp_def, S]
    have hout := composition_length_le_calls (m+1) h
    have hchoices : h+1 ≤ S := by
      have hh := sum_map_mono (List.range (h+1)) (fun _ => 1)
        (fun a => (compositionProfile m (h-a)).compositionCalls) (by
          intro a _
          change 1 ≤ (compositionProfile m (h-a)).compositionCalls
          have hc := compositionProfile_choices m (h-a); omega)
      simpa [S] using hh
    have hout' : (compositionsV (m+1) h).length ≤ S := by
      have hh := sum_map_mono (List.range (h+1))
        (fun a => (compositionsV m (h-a)).length)
        (fun a => (compositionProfile m (h-a)).compositionCalls)
        (fun a _ => composition_length_le_calls m (h-a))
      simpa [compositionsV, S, List.length_flatMap] using hh
    rw [compositionsC_ops_step, hcalls]
    have ht := Nat.mul_le_mul_left (8*m+15) hout'
    nlinarith [Nat.zero_le (m*S)]

theorem candidatesC_bound {N : Nat} (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) :
    (candidatesC R H m v).ops ≤ 64*(m+1)^2*(1+logicalWork (candidatesC R H m v).value.stats) := by
  let r := compositionsC m (H v)
  have hr := compositionsC_bound m (H v)
  have hf := filterC_bound (candidateCapC R v) r.value.value (7*m+5)
    (fun q _ => candidateCapC_bound R v q)
  have hc : (compositionProfile m (H v)).compositionCalls ≤ logicalWork r.value.stats := by
    simp only [r, compositionsC_value, compositionsStats_count, logicalWork]
    omega
  change r.ops ≤ _ at hr
  have hr' : r.ops ≤ 32*(m+1)^2*logicalWork r.value.stats :=
    hr.trans (Nat.mul_le_mul_left _ hc)
  have hw : logicalWork (candidatesC R H m v).value.stats =
      logicalWork r.value.stats+r.value.value.length+
        (filterC (candidateCapC R v) r.value.value).value.length := by
    change logicalWork (r.value.stats.add _) = _
    rw [logicalWork_add]
    change logicalWork r.value.stats +
      logicalWork { columnsGenerated := r.value.value.length, columnsAccepted := (filterC (candidateCapC R v) r.value.value).value.length } = _
    simp only [logicalWork]; omega
  rw [hw]
  change r.ops + (filterC (candidateCapC R v) r.value.value).ops + 3 ≤ _
  have hr'' := hr'.trans (Nat.mul_le_mul_right (logicalWork r.value.stats)
    (by nlinarith : 32*(m+1)^2 ≤ 64*(m+1)^2))
  have hf' := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right r.value.value.length
    (by nlinarith : 7*m+9 ≤ 64*(m+1)^2)) 1)
  have hz := Nat.zero_le (64*(m+1)^2*(filterC (candidateCapC R v) r.value.value).value.length)
  nlinarith only [hr'', hf', hz, Nat.zero_le (m^2), Nat.zero_le m]

theorem glueC_work_bound {N m : Nat} (v : Fin N) (q : Vector Nat m)
    (es : List (Entry N m)) : (glueC v q es).ops ≤ 10*(glueCharge N m es.length).work := by
  rw [glueC_ops]
  simp only [glueCharge, PayloadStats.work]
  nlinarith [Nat.zero_le (m*N), Nat.zero_le (m*(N-1)*es.length)]

theorem node_run_arithmetic (m k L R G ci ce : Nat)
    (hi : ci ≤ 64*(m+1)*(k+1+R)) (hl : L ≤ G)
    (he : ce ≤ L*(7*m+6)+10*G) :
    (7*m+1)+(9*m+1)+ci+(ce+3*L+1)+4 ≤ 128*(m+1)*(k+1+(R+m+G)) := by
  have hh := Nat.mul_le_mul_left (7*m+9) hl
  nlinarith [Nat.zero_le (m*k), Nat.zero_le (m*R), Nat.zero_le (m*G)]

theorem nodeRunC_bound {N m : Nat} (v : Fin N) (w : Int) (ts : List (List (Entry N m)))
    (q : Vector Nat m) : (nodeRunC v w ts q).ops ≤
      128*(m+1)*(ts.length+1+resourceWork (nodeRunC v w ts q).value) := by
  let r := insideC (supportC q).value (scaleC w q).value ts
  let gs := r.value.value.map (fun b => glueCharge N m b.picks.length)
  have hi := insideC_bound (supportC q).value (scaleC w q).value ts
  have he := sum_map_mono r.value.value (fun b => (entryC v q b).ops)
    (fun b => 7*m+6+10*(glueCharge N m b.picks.length).work) (by
      intro b _
      have hg := glueC_work_bound v q b.picks
      have ha := (vector_arithmetic_ops (0 : Int) q (Vector.replicate m 0) (Vector.replicate m 0)).1
      simp only [entryC]
      rw [ha]
      omega)
  have hl : r.value.value.length ≤ (sumPayload gs).work := by
    have hh := sum_map_mono r.value.value (fun _ => 1)
      (fun b => (glueCharge N m b.picks.length).work) (by
        intro b _; simp [glueCharge, PayloadStats.work]; omega)
    simpa [gs, List.map_map, Function.comp_def] using hh
  simp only [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate,
    smul_eq_mul] at he
  change r.ops ≤ _ at hi
  change (supportC q).ops+(scaleC w q).ops+r.ops+(mapC (entryC v q) r.value.value).ops+4 ≤ _
  rw [mapC_ops, mapWork_eq]
  have hv := vector_arithmetic_ops w q (Vector.replicate m 0) (Vector.replicate m 0)
  rw [hv.1, hv.2.2]
  have hwork : resourceWork (nodeRunC v w ts q).value =
      resourceWork r.value+m+(sumPayload gs).work := by
    change logicalWork (r.value.keyStats.add {ratMuls:=m})+
      (r.value.payload.add (sumPayload gs)).work = _
    simp only [logicalWork_add, payloadWork_add]
    simp only [logicalWork, resourceWork]; omega
  rw [hwork]
  have hg : (sumPayload gs).work =
      (r.value.value.map fun b => (glueCharge N m b.picks.length).work).sum := by simp [gs, Function.comp_def]
  rw [← hg] at he
  exact node_run_arithmetic m ts.length r.value.value.length (resourceWork r.value)
    (sumPayload gs).work r.ops (r.value.value.map (fun b => (entryC v q b).ops)).sum hi hl he

end UAVProof.TreeBudgetSubtreeScalar
