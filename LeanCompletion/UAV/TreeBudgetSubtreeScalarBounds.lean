import LeanCompletion.UAV.TreeBudgetSubtreeScalarCandidateBounds

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeBudgetSubtreeState TreeFlowExistence
variable {N m : Nat}

theorem flattenC_ops {α : Type} (xs : List (List α)) :
    (flatMapC (fun t => ⟨t, 1⟩) xs).ops =
      3*(flatMapC (fun t => ⟨t, 1⟩) xs).value.length+5*xs.length+1 := by
  induction xs with
  | nil => simp [flatMapC]
  | cons x xs ih => simp only [flatMapC, (appendC_spec _ _).1, (appendC_spec _ _).2,
      List.length_append, List.length_cons] at *; omega

theorem node_arithmetic (m k A B D L F cq cs cd : Nat)
    (hq : cq ≤ 64*(m+1)^2*(1+A))
    (hs : cs ≤ 128*(m+1)*(L*(k+1)+B))
    (hd : cd ≤ (16*m+19)*(1+D)) (hl : L ≤ A) (hf : F ≤ D) :
    cq+(cs+3*L+1)+(3*F+5*L+1)+cd+5 ≤
      512*(m+1)^2*(k+1)*(1+(A+B+D)) := by
  let K := 512*(m+1)^2*(k+1)
  have ha : 64*(m+1)^2+128*(m+1)*(k+1)+8 ≤ K := by
    dsimp [K]; nlinarith [Nat.zero_le (m*m*k), Nat.zero_le (m*k)]
  have hb : 128*(m+1) ≤ K := by dsimp [K]; nlinarith
  have hc : 16*m+22 ≤ K := by dsimp [K]; nlinarith
  have hz : 64*(m+1)^2+16*m+26 ≤ K := by dsimp [K]; nlinarith
  have ht := Nat.mul_le_mul_left (128*(m+1)*(k+1)+8) hl
  have hu := Nat.mul_le_mul_left 3 hf
  have hA := Nat.mul_le_mul_right A ha
  have hB := Nat.mul_le_mul_right B hb
  have hD := Nat.mul_le_mul_right D hc
  change _ ≤ K*(1+(A+B+D))
  nlinarith only [hq, hs, hd, ht, hu, hA, hB, hD, hz]

theorem nodeC_bound (R : RootedTree (Fin N)) (H : Fin N → Nat) (w : Fin N → Int)
    (m : Nat) (v : Fin N) (ts : List (List (Entry N m))) :
    (nodeC R H w m v ts).ops ≤
      512*(m+1)^2*(ts.length+1)*(1+resourceWork (nodeC R H w m v ts).value) := by
  let qs := candidatesC R H m v
  let rs := qs.value.value.map (nodeRunC v (w v) ts)
  let runs := collectC rs
  let flat := flatMapC (fun t => ⟨t, 1⟩) runs.value.value
  let d := dedupC Entry.key stateEqC flat.value
  have hq := candidatesC_bound R H m v
  change qs.ops ≤ 64*(m+1)^2*(1+logicalWork qs.value.stats) at hq
  have hs := sum_map_mono qs.value.value (fun q => (nodeRunC v (w v) ts q).ops)
    (fun q => 128*(m+1)*(ts.length+1+resourceWork (nodeRunC v (w v) ts q).value))
    (fun q _ => nodeRunC_bound v (w v) ts q)
  have hw : resourceWork runs.value = (rs.map fun r => resourceWork r.value).sum := by
    simp [runs, collectC, List.map_map, Function.comp_def]
  have hs' : (rs.map Counted.ops).sum ≤
      128*(m+1)*(qs.value.value.length*(ts.length+1)+resourceWork runs.value) := by
    simpa [rs, hw, List.sum_map_mul_left, List.sum_map_add, List.map_map,
      Function.comp_def] using hs
  have hl : qs.value.value.length ≤ logicalWork qs.value.stats := by
    change (candidatesC R H m v).value.value.length ≤ logicalWork (candidatesC R H m v).value.stats
    dsimp only [candidatesC]
    rw [logicalWork_add]
    simp only [logicalWork]; omega
  have hdl : flat.value.length ≤ resourceWork d.value := by
    simp only [d, dedupC, resourceWork, logicalWork, PayloadStats.work]; omega
  have hd : d.ops ≤ (16*m+19)*(1+resourceWork d.value) :=
    dedupC_work_bound Entry.key stateEqC (16*m+5) stateKey_bound flat.value
  have hf := flattenC_ops runs.value.value
  change flat.ops = 3*flat.value.length+5*runs.value.value.length+1 at hf
  have hlen : runs.value.value.length = qs.value.value.length := by
    simp [runs, rs, collectC, collectR]
  rw [hlen] at hf
  have hop : runs.ops = (rs.map Counted.ops).sum+3*qs.value.value.length+1 := by
    simp [runs, collectC, rs]
  have he : resourceWork (nodeC R H w m v ts).value =
      logicalWork qs.value.stats+resourceWork runs.value+resourceWork d.value := by
    change logicalWork (qs.value.stats.add (runs.value.keyStats.add d.value.keyStats))+
      (runs.value.payload.add d.value.payload).work = _
    simp only [logicalWork_add, payloadWork_add, resourceWork]; omega
  rw [he]
  change qs.ops+runs.ops+flat.ops+d.ops+5 ≤ _
  rw [hop, hf]
  exact node_arithmetic m ts.length (logicalWork qs.value.stats)
    (resourceWork runs.value) (resourceWork d.value) qs.value.value.length flat.value.length
    qs.ops (rs.map Counted.ops).sum d.ops hq hs' hd hl hdl

theorem children_length_le (R : RootedTree (Fin N)) (v : Fin N) :
    (childrenList R v).length ≤ N := by
  simpa [childrenList] using List.length_filter_le
    (fun w : Fin N => decide (w ≠ R.root ∧ R.parent w = v)) (List.finRange N)

/-- Universal DP factor; independent of service values, costs, and candidate mass. -/
def dpFactor (N m : Nat) : Nat := 2048*(N+1)*(m+1)^2

theorem computeC_bound (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) :
    (computeC R H w m v).ops ≤ dpFactor N m*resourceWork (computeC R H w m v).value := by
  let ch := childrenC R v
  let rs := ch.value.attach.map (fun u => computeC R H w m u.val)
  let cs := collectC rs
  let r := nodeC R H w m v cs.value.value
  have hs := sum_map_mono ch.value.attach
    (fun u => (computeC R H w m u.val).ops)
    (fun u => dpFactor N m*resourceWork (computeC R H w m u.val).value)
    (fun u _ => computeC_bound R H w m u.val)
  have hcs : cs.ops ≤ dpFactor N m*resourceWork cs.value+3*ch.value.length+1 := by
    simpa [cs, rs, collectC, collectR, resourceWork, logicalWork_sum, payloadWork_sum,
      List.map_map, Function.comp_def, List.sum_map_mul_left, List.sum_map_add,
      Nat.add_assoc] using Nat.add_le_add_right hs (3*ch.value.length+1)
  have hcl : ch.value.length ≤ N := by simpa [ch] using children_length_le R v
  have ht : cs.value.value.length = ch.value.length := by simp [cs, rs, collectC, collectR]
  have hn := nodeC_bound R H w m v cs.value.value
  change r.ops ≤ _ at hn
  rw [ht] at hn
  have hn' : r.ops ≤ 512*(m+1)^2*(N+1)*(1+resourceWork r.value) :=
    hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcl 1)))
  rw [computeC]
  change ch.ops+cs.ops+r.ops+5 ≤ dpFactor N m*
    (logicalWork (({nodeCalls:=1} : DPStats).add (cs.value.keyStats.add r.value.keyStats))+
      (cs.value.payload.add r.value.payload).work)
  have hc : ch.ops = 12*N+2 := childrenC_ops R v
  rw [hc]
  have he : logicalWork (({nodeCalls:=1} : DPStats).add (cs.value.keyStats.add r.value.keyStats))+
      (cs.value.payload.add r.value.payload).work = 1+resourceWork cs.value+resourceWork r.value := by
    simp only [logicalWork_add, payloadWork_add]
    simp only [resourceWork, logicalWork]; omega
  rw [he]
  unfold dpFactor at *
  have hbase : 12*N+2+3*ch.value.length+1+5 ≤ 1536*(N+1)*(m+1)^2 := by
    nlinarith [Nat.zero_le (N*m*m), Nat.zero_le (N*m)]
  have hmult := Nat.mul_le_mul_right (resourceWork r.value)
    (by nlinarith : 512*(m+1)^2*(N+1) ≤ 2048*(N+1)*(m+1)^2)
  nlinarith only [hcs, hn', hbase, hmult]
termination_by R.rank v
decreasing_by
  apply R.child_rank
  apply (mem_childrenList R v u.val).mp
  simpa [ch] using u.property

theorem computeC_output_le_work (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (v : Fin N) :
    (computeC R H w m v).value.value.length ≤ resourceWork (computeC R H w m v).value := by
  rw [computeC]
  simp only [nodeC, dedupC, resourceWork, logicalWork, DPStats.add, PayloadStats.work,
    PayloadStats.add]
  omega

theorem findC_bound {α : Type} (p : α → Counted Bool) (k : Nat)
    (hk : ∀ x, (p x).ops ≤ k) (xs : List α) :
    (findC p xs).ops ≤ (k+4)*(findC p xs).value.2+1 := by
  induction xs with
  | nil => simp [findC]
  | cons x xs ih =>
    have hh := hk x
    simp only [findC]; split <;> dsimp only <;> nlinarith

theorem finishC_bound (R : RootedTree (Fin N)) (r : Option (Root N m)) :
    (finishC R r).ops ≤ 16*(1+(finishC R r).value.2.work) := by
  cases r with
  | none => simp [finishC, PayloadStats.work]
  | some x =>
    have hz : (tabulateC (fun _ : Fin m => (⟨0, 1⟩ : Counted Nat))).ops = 6*m+1 := by
      simp; omega
    have hg := glueC_work_bound R.root (Vector.ofFn (fun _ : Fin m => 0)) x.picks
    simp only [finishC, hz, tabulateC_value, payloadWork_add]
    simp only [PayloadStats.work, glueCharge] at *
    omega

theorem solveC_ops_le_resource (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (w : Fin N → Int) (m : Nat) (B : Int) :
    (solveC R H w m B).ops ≤ 2*dpFactor N m*(1+resourceWork (solveR R H w m B)) := by
  let ch := childrenC R R.root
  let rs := ch.value.map (computeC R H w m)
  let cs := collectC rs
  let r := rootsC cs.value.value
  let f := findC (fun x : Root N m => let c := acceptC B x.key; ⟨c.value, c.ops+1⟩) r.value.value
  let out := finishC R f.value.1
  have hs := sum_map_mono ch.value (fun u => (computeC R H w m u).ops)
    (fun u => dpFactor N m*resourceWork (computeC R H w m u).value)
    (fun u _ => computeC_bound R H w m u)
  have hcs : cs.ops ≤ dpFactor N m*resourceWork cs.value+3*ch.value.length+1 := by
    simpa [cs, rs, collectC, collectR, resourceWork, List.map_map, Function.comp_def,
      List.sum_map_mul_left, List.sum_map_add, Nat.add_assoc] using
      Nat.add_le_add_right hs (3*ch.value.length+1)
  have hcl : ch.value.length ≤ N := by simpa [ch] using children_length_le R R.root
  have ht : cs.value.value.length = ch.value.length := by simp [cs, rs, collectC, collectR]
  have hl : (cs.value.value.map List.length).sum ≤ resourceWork cs.value := by
    have hh := sum_map_mono ch.value (fun u => (computeC R H w m u).value.value.length)
      (fun u => resourceWork (computeC R H w m u).value)
      (fun u _ => computeC_output_le_work R H w m u)
    simpa [cs, rs, collectC, collectR, resourceWork, List.map_map, Function.comp_def,
      List.sum_map_add] using hh
  have hr := rootsC_bound cs.value.value
  change r.ops ≤ 128*(m+1)*(cs.value.value.length+1+
    (cs.value.value.map List.length).sum+resourceWork r.value) at hr
  rw [ht] at hr
  have hf : f.ops ≤ (10*m+7)*f.value.2+1 :=
    findC_bound _ (10*m+3) (fun x => Nat.add_le_add_right (acceptC_bound B x.key) 1) _
  have ho := finishC_bound R f.value.1
  change out.ops ≤ 16*(1+out.value.2.work) at ho
  have he : resourceWork (solveC R H w m B).value =
      resourceWork cs.value+resourceWork r.value+f.value.2+out.value.2.work := by
    change logicalWork (cs.value.keyStats.add (r.value.keyStats.add {acceptCalls:=f.value.2}))+
      (cs.value.payload.add (r.value.payload.add out.value.2)).work = _
    simp only [logicalWork_add, payloadWork_add]
    simp only [resourceWork, logicalWork]; omega
  rw [← solveC_value, he]
  change ch.ops+cs.ops+r.ops+f.ops+out.ops+7 ≤ _
  have hc : ch.ops = 12*N+2 := childrenC_ops R R.root
  rw [hc]
  have hr' : r.ops ≤ 128*(m+1)*(N+1+resourceWork cs.value+resourceWork r.value) :=
    hr.trans (Nat.mul_le_mul_left _ (by omega))
  let D := dpFactor N m
  have hB : D+128*(m+1) ≤ 2*D := by dsimp [D, dpFactor]; nlinarith
  have hA : 128*(m+1) ≤ 2*D := by dsimp [D, dpFactor]; nlinarith
  have hF : 10*m+7 ≤ 2*D := by dsimp [D, dpFactor]; nlinarith
  have hO : 16 ≤ 2*D := by dsimp [D, dpFactor]; nlinarith
  have hz : 15*N+27+128*(m+1)*(N+1) ≤ 2*D := by
    dsimp [D, dpFactor]; nlinarith [Nat.zero_le (N*m*m), Nat.zero_le (N*m)]
  have hb := Nat.mul_le_mul_right (resourceWork cs.value) hB
  have ha := Nat.mul_le_mul_right (resourceWork r.value) hA
  have hff := Nat.mul_le_mul_right f.value.2 hF
  have hoo := Nat.mul_le_mul_right out.value.2.work hO
  change cs.ops ≤ D*resourceWork cs.value+3*ch.value.length+1 at hcs
  change _ ≤ 2*D*(1+(resourceWork cs.value+resourceWork r.value+f.value.2+out.value.2.work))
  nlinarith only [hcs, hr', hf, ho, hcl, hz, hb, ha, hff, hoo]

def dpUpper (N m U P : Nat) : Nat :=
  2*dpFactor N m*(1+64*(N+1)^2*(m+1)*(U+1)*P^2)

theorem solveC_auto_bound (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m U : Nat) (T : Rat) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    (solveC R H (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) m
      (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).budget).ops ≤
      dpUpper N m U (globalProduct R H m) := by
  apply (solveC_ops_le_resource R H _ m _).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (solveAutoR_resourceWork_le R H s m U T hU) 1)

end UAVProof.TreeBudgetSubtreeScalar
