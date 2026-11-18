import LeanCompletion.UAV.TreeBudgetRepresentationBridge
import LeanCompletion.UAV.TreeBudgetSubtreeCountsExact

/-! Expand a row in childrenList order. A positive child receives its entire
subtree on the first crossing and only two-edge returns thereafter. -/
namespace UAVProof.TreeBudgetSubtreeRouteOutput
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable TreeBudgetRow

/-- Endpoint indices make concatenation skip the shared vertex. -/
inductive Walk {V : Type} : V → V → Type where
  | stay (v : V) : Walk v v
  | step {a b c : V} (ne : a ≠ b) (rest : Walk b c) : Walk a c

namespace Walk
variable {V : Type} {a b c : V}

def append {a b c : V} : Walk a b → Walk b c → Walk a c
  | .stay _, q => q
  | .step ne p, q => .step ne (append p q)

def arrivals {a b : V} : Walk a b → List V
  | .stay _ => []
  | .step (b := u) _ p => u :: arrivals p

def weight (f : V → V → Nat) {a b : V} : Walk a b → Nat
  | .stay _ => 0
  | .step (a := u) (b := v) _ p => f u v + weight f p

@[simp] theorem weight_append (f : V → V → Nat) (p : Walk a b) (q : Walk b c) :
    (p.append q).weight f = p.weight f + q.weight f := by
  induction p <;> simp [append, weight, *, Nat.add_assoc]

def join (v : V) : List (Walk v v) → Walk v v
  | [] => .stay v
  | p :: ps => p.append (join v ps)

theorem weight_join (f : V → V → Nat) (v : V) (ps : List (Walk v v)) :
    (join v ps).weight f = (ps.map (weight f)).sum := by
  induction ps <;> simp [join, weight, *]

def bounce (ne : a ≠ b) : Nat → Walk a a
  | 0 => .stay a
  | n+1 => .step ne (.step ne.symm (bounce ne n))

theorem weight_bounce (f : V → V → Nat) (ne : a ≠ b) (n : Nat) :
    (bounce ne n).weight f = n * (f a b + f b a) := by
  induction n <;> simp [bounce, weight, *, Nat.succ_mul]
  omega

def visit (ne : a ≠ b) (n : Nat) (inside : Unit → Walk b b) : Walk a a :=
  match n with
  | 0 => .stay a
  | k+1 => .step ne ((inside ()).append (.step ne.symm (bounce ne k)))

theorem weight_visit (f : V → V → Nat) (ne : a ≠ b) (n : Nat) (p : Unit → Walk b b) :
    (visit ne n p).weight f =
      n*(f a b + f b a) + (if n = 0 then 0 else (p ()).weight f) := by
  cases n <;> simp [visit, weight, weight_bounce, Nat.succ_mul]
  omega

theorem length_arrivals (p : Walk a b) : p.arrivals.length = p.weight (fun _ _ => 1) := by
  induction p <;> simp [arrivals, weight, *, Nat.add_comm]

theorem flow_arrivals [DecidableEq V] (p : Walk a b) (i j : V) :
    routeFlow (a :: p.arrivals) i j = p.weight (fun u v => if (u,v) = (i,j) then 1 else 0) := by
  induction p with
  | stay => simp [arrivals, routeFlow, weight]
  | @step a b c h rest ih =>
    simp only [arrivals, weight, routeFlow, List.tail_cons, List.zip_cons_cons,
      List.count_cons] at *
    split <;> split <;> simp_all [beq_iff_eq, Nat.add_comm]

theorem chain (p : Walk a b) : (a :: p.arrivals).IsChain (· ≠ ·) := by
  induction p with
  | stay => simp [arrivals]
  | step ne _ ih => exact List.isChain_cons_cons.mpr ⟨ne, ih⟩

theorem ends (p : Walk a b) : (a :: p.arrivals).getLast? = some b := by
  induction p with
  | stay => rfl
  | step _ _ ih => exact ih

theorem count_arrivals [DecidableEq V] (p : Walk a b) (x : V) :
    p.arrivals.count x = p.weight (fun _ v => if v = x then 1 else 0) := by
  induction p with
  | stay => rfl
  | @step a b c _ p ih => by_cases h : b = x <;> simp [arrivals, weight, ih, h, Nat.add_comm]

end Walk

variable {N : Nat}

private theorem child_ne (R : RootedTree (Fin N)) (v : Fin N) (u : {u // u ∈ childrenList R v}) :
    v ≠ u.val := by
  have h := R.child_rank ((mem_childrenList _ _ _).mp u.property)
  exact fun he => (ne_of_lt h) (congrArg R.rank he.symm)

def tour (R : RootedTree (Fin N)) (p : Fin N → Nat) (v : Fin N) : Walk v v :=
  Walk.join v ((childrenList R v).attach.map fun u =>
    Walk.visit (child_ne R v u) (p u.val) (fun _ => tour R p u.val))
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

private theorem zero_below (R : RootedTree (Fin N)) (p : Fin N → Nat)
    (ha : AncestorClosed R p) {v x : Fin N} (hv : v ≠ R.root) (hz : p v = 0)
    (hx : InSubtree R v x) : p x = 0 := by
  induction hx with
  | self => exact hz
  | step hn parent ih =>
    by_contra! hp
    have h := ha _ hn (by omega) (subtree_ne_root hv parent)
    omega

private def edgeWeight (R : RootedTree (Fin N)) (p : Fin N → Nat)
    (f : Fin N → Fin N → Nat) (u : Fin N) := p u * (f (R.parent u) u + f u (R.parent u))

private theorem tour_weight_children (R : RootedTree (Fin N)) (p : Fin N → Nat)
    (ha : AncestorClosed R p) (f : Fin N → Fin N → Nat) (v : Fin N) :
    (tour R p v).weight f = ∑ u ∈ R.children v, ∑ x ∈ subtree R u, edgeWeight R p f x := by
  rw [tour, Walk.weight_join, List.map_map]
  have blocks (u : {u // u ∈ childrenList R v}) :
      (Walk.visit (child_ne R v u) (p u.val) (fun _ => tour R p u.val)).weight f =
        ∑ x ∈ subtree R u.val, edgeWeight R p f x := by
    have hu := (R.mem_children _ _).mp ((mem_childrenList _ _ _).mp u.property)
    rw [Walk.weight_visit]
    by_cases hz : p u.val = 0
    · simp only [hz, zero_mul, if_true, Nat.zero_add]
      symm
      exact Finset.sum_eq_zero fun x hx => by
        simp [edgeWeight, zero_below R p ha hu.1 hz ((mem_subtree _ _ _).mp hx)]
    · rw [if_neg hz, tour_weight_children R p ha f u.val, sum_subtree R u.val]
      simp [edgeWeight, hu.2]
  simp only [Function.comp_def]
  rw [List.map_congr_left (fun u _ => blocks u), List.attach_map_val (f := fun u => ∑ x ∈ subtree R u, edgeWeight R p f x), childrenList_sum]
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem tour_weight (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p)
    (f : Fin N → Fin N → Nat) : (tour R p R.root).weight f =
      ∑ x ∈ Finset.univ.erase R.root, p x * (f (R.parent x) x + f x (R.parent x)) :=
  (tour_weight_children R p ha f _).trans (TreeBudgetSubtreeStats.root_children_sum R _)

private theorem sum_endpoint (R : RootedTree (Fin N)) (p : Fin N → Nat)
    (i j : Fin N) :
    (∑ x ∈ Finset.univ.erase R.root, (if R.parent x = i ∧ x = j then p x else 0)) =
      if j ≠ R.root ∧ R.parent j = i then p j else 0 := by
  by_cases h : j = R.root
  · subst j
    simp only [ne_eq, not_true_eq_false, false_and, if_false]
    exact Finset.sum_eq_zero fun x hx => by simp [(Finset.mem_erase.mp hx).1]
  · rw [Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)]
    · simp [h]
    · intro x _ hx
      simp [hx]

theorem tour_flow (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p)
    (i j : Fin N) : routeFlow (R.root :: (tour R p R.root).arrivals) i j = edgeFlow R p i j := by
  rw [Walk.flow_arrivals, tour_weight R p ha]
  simp only [Nat.mul_add, Prod.mk.injEq, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  rw [sum_endpoint, edgeFlow]
  congr 1
  simpa only [and_comm] using sum_endpoint R p j i

theorem tour_length (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p) :
    (tour R p R.root).arrivals.length = 2 * ∑ x ∈ Finset.univ.erase R.root, p x := by
  rw [Walk.length_arrivals, tour_weight R p ha]
  simp [Finset.mul_sum, Nat.mul_comm]

private theorem depot_count (R : RootedTree (Fin N)) (p : Fin N → Nat)
    (ha : AncestorClosed R p) (hk : rootDegree R p = 1) :
    (tour R p R.root).arrivals.count R.root = 1 := by
  rw [Walk.count_arrivals, tour_weight R p ha]
  apply Eq.trans _ hk
  unfold rootDegree
  rw [Finset.sum_congr rfl (g := fun x => if R.parent x = R.root then p x else 0)]
  · rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  · intro x hx
    have hn := (Finset.mem_erase.mp hx).1
    by_cases hp : R.parent x = R.root <;> simp [hn,hp]

/-- The depot occurs only at the final arrival. The nonempty interior and
adjacency properties therefore hold for the computed vertex list itself. -/
def route (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p)
    (hk : rootDegree R p = 1) : LegalRoute R.root := by
  let t := tour R p R.root
  have count : t.arrivals.count R.root = 1 := depot_count R p ha hk
  have hs : t.arrivals ≠ [] := by intro he; simp [he] at count
  have last : t.arrivals.getLast? = some R.root := by
    simpa only [List.getLast?_cons_of_ne_nil hs] using t.ends
  have shape : t.arrivals.dropLast ++ [R.root] = t.arrivals := by
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp last
    simp [hl]
  have hc : (depotRoute R.root t.arrivals.dropLast).IsChain (· ≠ ·) := by
    simpa only [depotRoute, List.cons_append, shape] using t.chain
  refine ⟨t.arrivals.dropLast, ?_, ?_, hc⟩
  · intro he
    simp [he, depotRoute] at hc
  · have h : t.arrivals.dropLast.count R.root = 0 := by
      rw [← shape, List.count_append] at count
      simpa using count
    exact List.count_eq_zero.mp h

theorem route_vertices (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p)
    (hk : rootDegree R p = 1) :
    (route R p ha hk).vertices = R.root :: (tour R p R.root).arrivals := by
  let t := tour R p R.root
  change (R.root :: t.arrivals.dropLast) ++ [R.root] = R.root :: t.arrivals
  have hs : t.arrivals ≠ [] := by
    intro he
    have hc := depot_count R p ha hk
    change t.arrivals.count _ = _ at hc
    simp [he] at hc
  have last : t.arrivals.getLast? = some R.root := by
    simpa only [List.getLast?_cons_of_ne_nil hs] using t.ends
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp last
  simp [hl]

open TreeBudgetRepresentationBridge TreeBudgetPatterns in
theorem round_trip (R : RootedTree (Fin N)) (p : Fin N → Nat) (ha : AncestorClosed R p)
    (hk : rootDegree R p = 1) :
    let r := route R p ha hk
    projectRow R r = normalize R p ∧ (∀ v, r.visits.count v = rowVisits R p v) ∧
      ∀ s, ResourceCuts.routeServiceIn r Finset.univ s = cost R p s := by
  have hf (i j) : routeFlow (route R p ha hk).vertices i j = edgeFlow R p i j := by
    rw [route_vertices]
    exact tour_flow R p ha i j
  exact ⟨projectRow_of_flow R p _ hf, counts_of_flow R p _ hf, fun s =>
    (service_of_flow R p _ hf s).trans (cost_eq R p s).symm⟩

open TreeBudgetCertificate

/-- Expand each row with its certificate multiplicity in certificate order. -/
def vertices (R : RootedTree (Fin N)) (c : Certificate (Fin N)) : List (List (Fin N)) :=
  (List.finRange c.size).flatMap fun i =>
    List.replicate (c.count i) (R.root :: (tour R (c.row i) R.root).arrivals)

theorem output_size (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) (c : Certificate (Fin N)) (hc : checkCertificate R H m s T c = true) :
    (vertices R c).length = m ∧
    ((vertices R c).map List.length).sum = 2*(∑ x ∈ Finset.univ.erase R.root, H x) + m := by
  obtain ⟨rows, fleet, columns⟩ := (checkCertificate_eq_true_iff ..).mp hc
  have lengths (i : Fin c.size) := tour_length R (c.row i) (rows i).2.2.2.1
  have mass : (∑ i, c.count i * ∑ x ∈ Finset.univ.erase R.root, c.row i x) =
      ∑ x ∈ Finset.univ.erase R.root, H x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x hx => columns x (Finset.mem_erase.mp hx).1
  constructor
  · simpa [vertices, List.length_flatMap, Function.comp_def, ← List.ofFn_eq_map,
      List.sum_ofFn] using fleet
  · have sumWords {α : Type} (xs : List α) (g : α → List (List (Fin N))) :
        ((xs.flatMap g).map List.length).sum = (xs.map fun x => ((g x).map List.length).sum).sum := by
      induction xs <;> simp [*]
    simp only [vertices, sumWords, List.map_replicate, List.sum_replicate,
      List.length_cons, lengths, nsmul_eq_mul, ← List.ofFn_eq_map, List.sum_ofFn]
    simp only [Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib, ← fleet, ← mass, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by simp [Nat.mul_comm, Nat.mul_assoc]

theorem output_moves (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) (c : Certificate (Fin N)) (hc : checkCertificate R H m s T c = true) :
    ((vertices R c).map (fun word => word.length - 1)).sum =
      2 * ∑ x ∈ Finset.univ.erase R.root, H x := by
  have nonempty (w) (hw : w ∈ vertices R c) : w ≠ [] := by
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hw
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hi
    simp
  have sizes (ws : List (List (Fin N))) (hn : ∀ w ∈ ws, w ≠ []) :
      (ws.map (fun w => w.length-1)).sum + ws.length = (ws.map List.length).sum := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      have hp := List.length_pos_iff.mpr (hn w (by simp))
      have ht := ih (fun w hw => hn w (by simp [hw]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have hs := sizes (vertices R c) nonempty
  obtain ⟨hm, hv⟩ := output_size R H s m T c hc
  omega

/-- Each expanded word realizes its own checked row, with the prescribed budget. -/
theorem output_word (R : RootedTree (Fin N)) (H : Fin N → Nat) (s : Fin N → Rat)
    (m : Nat) (T : Rat) (c : Certificate (Fin N)) (hc : checkCertificate R H m s T c = true)
    (w : List (Fin N)) (hw : w ∈ vertices R c) :
    ∃ i, 0 < c.count i ∧ ∃ r : LegalRoute R.root, r.vertices = w ∧
      TreeBudgetRepresentationBridge.projectRow R r = c.row i ∧
      ResourceCuts.routeServiceIn r Finset.univ s ≤ T := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hw
  obtain ⟨hn, wh⟩ := List.mem_replicate.mp hi
  have row := ((checkCertificate_eq_true_iff ..).mp hc).1 i
  have ha := row.2.2.2.1
  have hk : rootDegree R (c.row i) = 1 := by
    simpa only [TreeBudgetPatterns.rootCount_eq] using row.2.2.1
  obtain ⟨hp, _, hfees⟩ := round_trip R (c.row i) ha hk
  have norm : TreeBudgetPatterns.normalize R (c.row i) = c.row i := by
    funext v
    by_cases h : v = R.root <;> simp [TreeBudgetPatterns.normalize, h, row.1]
  exact ⟨i, by omega, route R _ ha hk, (route_vertices R _ ha hk).trans wh.symm,
    hp.trans norm, (hfees s).le.trans row.2.2.2.2⟩

end UAVProof.TreeBudgetSubtreeRouteOutput
