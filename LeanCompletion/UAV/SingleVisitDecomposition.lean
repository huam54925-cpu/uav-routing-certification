import LeanCompletion.UAV.ResourceCuts

namespace UAVProof.SingleVisitDecomposition

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]



omit [DecidableEq V] in
/-- A natural-number family summing to one has exactly one unit entry;
all other entries are zero. -/
theorem exists_unit_of_sum_one
    (f : V → ℕ)
    (hsum : ∑ v, f v = 1) :
    ∃ v, f v = 1 ∧ ∀ w, w ≠ v → f w = 0 := by
  have hpos : 0 < ∑ v, f v := by
    omega
  obtain ⟨v, hv, hvpos⟩ := Finset.sum_pos_iff.mp hpos
  have hvle : f v ≤ ∑ w, f w :=
    Finset.single_le_sum (fun w _ => Nat.zero_le (f w)) hv
  have hvone : f v = 1 := by
    omega
  refine ⟨v, hvone, ?_⟩
  intro w hw
  have hpair : f v + f w ≤ ∑ u, f u :=
    Finset.add_le_sum
      (fun u _ => Nat.zero_le (f u))
      hv
      (Finset.mem_univ w)
      (Ne.symm hw)
  omega
omit [DecidableEq V] in
/-- Outgoing degree one determines the entire outgoing row. -/
theorem outFlow_one_row
    (x : V → V → ℕ) (v : V)
    (hout : outFlow Finset.univ x v = 1) :
    ∃ w, x v w = 1 ∧ ∀ u, u ≠ w → x v u = 0 := by
  apply exists_unit_of_sum_one (fun w => x v w)
  simpa [outFlow] using hout
omit [DecidableEq V] in
/-- Incoming degree one determines the entire incoming column. -/
theorem inFlow_one_column
    (x : V → V → ℕ) (v : V)
    (hin : inFlow Finset.univ x v = 1) :
    ∃ u, x u v = 1 ∧ ∀ w, w ≠ u → x w v = 0 := by
  apply exists_unit_of_sum_one (fun u => x u v)
  simpa [inFlow] using hin
omit [DecidableEq V] in
/-- A vertex of outgoing degree one has a unique positive-flow successor. -/
theorem exists_unique_successor
    (x : V → V → ℕ) (v : V)
    (hout : outFlow Finset.univ x v = 1) :
    ∃! w, 0 < x v w := by
  obtain ⟨w, hwone, hwzero⟩ := outFlow_one_row x v hout
  refine ⟨w, by omega, ?_⟩
  intro u hu
  by_contra hne
  have hzero : x v u = 0 := hwzero u hne
  omega
omit [DecidableEq V] in
/-- A vertex of incoming degree one has a unique positive-flow predecessor. -/
theorem exists_unique_predecessor
    (x : V → V → ℕ) (v : V)
    (hin : inFlow Finset.univ x v = 1) :
    ∃! u, 0 < x u v := by
  obtain ⟨u, huone, huzero⟩ := inFlow_one_column x v hin
  refine ⟨u, by omega, ?_⟩
  intro w hw
  by_contra hne
  have hzero : x w v = 0 := huzero w hne
  omega


/-- If every positive-flow edge starting in S ends in S,
then the outgoing cut flow is zero. -/
theorem outCutFlow_zero_of_closed
    (x : V → V → ℕ) (S : Finset V)
    (hclosed : ∀ i ∈ S, ∀ j, 0 < x i j → j ∈ S) :
    outCutFlow S x = 0 := by
  unfold outCutFlow
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hjoutside : j ∉ S := (Finset.mem_filter.mp hj).2
  by_contra hne
  have hjinside : j ∈ S :=
    hclosed i hi j (Nat.pos_of_ne_zero hne)
  exact hjoutside hjinside

/-- Positive depot-free cuts exclude nonempty task sets
closed under all positive-flow edges. -/
theorem no_closed_task_set
    (x : V → V → ℕ) (depot : V)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (S : Finset V)
    (hne : S.Nonempty)
    (hdepot : depot ∉ S) :
    ¬ (∀ i ∈ S, ∀ j, 0 < x i j → j ∈ S) := by
  intro hclosed
  have hzero : outCutFlow S x = 0 :=
    outCutFlow_zero_of_closed x S hclosed
  have hpositive : 1 ≤ outCutFlow S x :=
    hconn S hne hdepot
  omega

/-- In a nonempty depot-free set, some task's unique successor
lies outside the set. Its outgoing edge has flow exactly one. -/
theorem exists_unit_successor_exit
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (S : Finset V)
    (hne : S.Nonempty)
    (hdepot : depot ∉ S) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ x i j = 1 ∧
      ∀ k, k ≠ j → x i k = 0 := by
  have hpos : 0 < outCutFlow S x :=
    hconn S hne hdepot
  unfold outCutFlow at hpos
  obtain ⟨i, hi, hinner⟩ := Finset.sum_pos_iff.mp hpos
  obtain ⟨j, hj, hij⟩ := Finset.sum_pos_iff.mp hinner
  have hjoutside : j ∉ S := (Finset.mem_filter.mp hj).2
  have hidepot : i ≠ depot := by
    intro heq
    subst i
    exact hdepot hi
  obtain ⟨w, hwone, hwzero⟩ :=
    outFlow_one_row x i (hout i hidepot)
  have hjw : j = w := by
    by_contra hne'
    have hzero : x i j = 0 := hwzero j hne'
    omega
  subst j
  exact ⟨i, hi, w, hjoutside, hwone, hwzero⟩

/-- Follow a successor function for a given number of steps. -/
def successorWalk (next : V → V) (start : V) : ℕ → V
  | 0 => start
  | n + 1 => next (successorWalk next start n)

/-- If next follows positive-flow edges at every task vertex,
then its walk reaches the depot in finitely many steps. -/
theorem successorWalk_reaches_depot
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start : V) :
    ∃ n, successorWalk next start n = depot := by
  classical
  by_contra hnever
  let S : Finset V :=
    Finset.univ.filter
      (fun v => ∃ n, successorWalk next start n = v)
  have hstart : start ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ start, ⟨0, rfl⟩⟩
  have hdepot : depot ∉ S := by
    intro hd
    have hreach : ∃ n, successorWalk next start n = depot :=
      (Finset.mem_filter.mp hd).2
    exact hnever hreach
  apply no_closed_task_set x depot hconn S ⟨start, hstart⟩ hdepot
  intro i hi j hij
  have hidepot : i ≠ depot := by
    intro heq
    subst i
    exact hdepot hi
  obtain ⟨w, _, hunique⟩ :=
    exists_unique_successor x i (hout i hidepot)
  have hjnext : j = next i :=
    (hunique j hij).trans
      (hunique (next i) (hnext i hidepot)).symm
  have hiwalk : ∃ n, successorWalk next start n = i :=
    (Finset.mem_filter.mp hi).2
  obtain ⟨n, hn⟩ := hiwalk
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ j, ⟨n + 1, ?_⟩⟩
  change next (successorWalk next start n) = j
  rw [hn]
  exact hjnext.symm

/-- Starting at a task vertex, there is a first arrival at the depot.
Before that arrival, every step follows a positive-flow edge and
consecutive vertices are distinct under the no-self-loop assumption. -/
theorem exists_first_return_segment
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start : V)
    (hstart : start ≠ depot) :
    ∃ n : ℕ,
      0 < n ∧
      successorWalk next start n = depot ∧
      (∀ k, k < n → successorWalk next start k ≠ depot) ∧
      (∀ k, k < n →
        0 < x (successorWalk next start k)
          (successorWalk next start (k + 1)) ∧
        successorWalk next start k ≠
          successorWalk next start (k + 1)) := by
  classical
  have hexists :
      ∃ n, successorWalk next start n = depot :=
    successorWalk_reaches_depot
      x depot hout hconn next hnext start
  let n : ℕ := Nat.find hexists
  have hhit : successorWalk next start n = depot :=
    Nat.find_spec hexists
  have hbefore :
      ∀ k, k < n → successorWalk next start k ≠ depot := by
    intro k hk
    exact Nat.find_min hexists hk
  have hnpositive : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    have hbad : start = depot := by
      simpa only [hnzero, successorWalk] using hhit
    exact hstart hbad
  refine ⟨n, hnpositive, hhit, hbefore, ?_⟩
  intro k hk
  have hedge :
      0 < x (successorWalk next start k)
        (successorWalk next start (k + 1)) := by
    change 0 < x (successorWalk next start k)
      (next (successorWalk next start k))
    exact hnext _ (hbefore k hk)
  refine ⟨hedge, ?_⟩
  intro heq
  have hself :
      0 < x (successorWalk next start k)
        (successorWalk next start k) := by
    rw [← heq] at hedge
    exact hedge
  rw [hloop] at hself
  omega
/-- Every positive-flow depot departure extends to a legal route
following the successor walk. Every consecutive edge has positive
flow in x. Exact edge multiplicities are not asserted here. -/
theorem exists_legalRoute_of_departure
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start : V)
    (hdepart : 0 < x depot start) :
    ∃ n : ℕ, 0 < n ∧
      successorWalk next start n = depot ∧
      (∀ k, k < n →
        successorWalk next start k ≠ depot) ∧
      ∃ r : LegalRoute depot,
        r.visits =
          List.ofFn (fun i : Fin n =>
            successorWalk next start i.val) ∧
        r.vertices.IsChain (fun i j => 0 < x i j) := by
  classical
  have hstart : start ≠ depot := by
    intro heq
    subst start
    have hz := hloop depot
    omega
  obtain ⟨n, hn, hhit, hbefore, hsteps⟩ :=
    exists_first_return_segment
      x depot hout hconn hloop next hnext start hstart
  let visits : List V :=
    List.ofFn (fun i : Fin n =>
      successorWalk next start i.val)
  have hnonempty : visits ≠ [] := by
    have hlength : visits.length = n := by
      simp [visits]
    intro hempty
    rw [hempty] at hlength
    simp only [List.length_nil] at hlength
    omega
  have hnodepot : depot ∉ visits := by
    have hall : ∀ v ∈ visits, v ≠ depot :=
      (List.forall_mem_ofFn_iff
        (f := fun i : Fin n =>
          successorWalk next start i.val)
        (P := fun v : V => v ≠ depot)).mpr
          (fun i => hbefore i.val i.isLt)
    intro hmem
    exact hall depot hmem rfl
  have hpath :
      visits ++ [depot] =
        List.ofFn (fun i : Fin (n + 1) =>
          successorWalk next start i.val) := by
    rw [List.ofFn_succ']
    simp [List.concat_eq_append, visits, hhit]
  have hchain :
      (visits ++ [depot]).IsChain
        (fun i j => 0 < x i j) := by
    rw [hpath, List.isChain_iff_getElem]
    intro k hk
    have hk' : k < n := by
      simp only [List.length_ofFn] at hk
      omega
    simpa only [List.getElem_ofFn] using (hsteps k hk').1
  have hhead :
      (visits ++ [depot]).head? = some start := by
    rw [hpath, List.ofFn_succ]
    rfl
  have hfull :
      (depotRoute depot visits).IsChain
        (fun i j => 0 < x i j) := by
    change (depot :: (visits ++ [depot])).IsChain
      (fun i j => 0 < x i j)
    apply hchain.cons
    intro v hv
    rw [hhead] at hv
    have hvstart : start = v := by
      simpa only [Option.mem_some_iff] using hv
    subst v
    exact hdepart
  have hne :
      (depotRoute depot visits).IsChain (· ≠ ·) := by
    apply hfull.imp
    intro a b hab heq
    subst b
    have hz := hloop a
    omega
  let r : LegalRoute depot :=
    { visits := visits
      visits_nonempty := hnonempty
      depot_not_mem := hnodepot
      adjacent_ne := hne }
  refine ⟨n, hn, hhit, hbefore, r, rfl, ?_⟩
  exact hfull
/-- Incoming degree one forces any two positive-flow predecessors
of the same vertex to coincide. -/

theorem positive_predecessors_eq
    (x : V → V → ℕ) (v : V)
    (hin : inFlow Finset.univ x v = 1)
    {a b : V}
    (ha : 0 < x a v)
    (hb : 0 < x b v) :
    a = b := by
  obtain ⟨u, _, hunique⟩ :=
    exists_unique_predecessor x v hin
  exact (hunique a ha).trans (hunique b hb).symm

/-- Two successor walks starting on positive depot departures
can meet before returning only at the same step and with the
same starting vertex. -/
theorem successorWalk_collision
    (x : V → V → ℕ) (depot : V)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start other : V)
    (hdepartStart : 0 < x depot start)
    (hdepartOther : 0 < x depot other)
    (i j : ℕ)
    (hleft : ∀ k, k ≤ i →
      successorWalk next start k ≠ depot)
    (hright : ∀ k, k ≤ j →
      successorWalk next other k ≠ depot)
    (hmeet :
      successorWalk next start i =
        successorWalk next other j) :
    i = j ∧ start = other := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero =>
          exact ⟨rfl, hmeet⟩
      | succ j =>
          have hs : start ≠ depot :=
            hleft 0 (by omega)
          have hp :
              successorWalk next other j ≠ depot :=
            hright j (by omega)
          change
            start = next (successorWalk next other j)
            at hmeet
          have hedge :
              0 < x (successorWalk next other j) start := by
            rw [hmeet]
            exact hnext _ hp
          have hpred :
              successorWalk next other j = depot :=
            positive_predecessors_eq
              x start (hin start hs)
              hedge hdepartStart
          exact (hp hpred).elim
  | succ i ih =>
      cases j with
      | zero =>
          have ht : other ≠ depot :=
            hright 0 (by omega)
          have hp :
              successorWalk next start i ≠ depot :=
            hleft i (by omega)
          change
            next (successorWalk next start i) = other
            at hmeet
          have hedge :
              0 < x (successorWalk next start i) other := by
            rw [← hmeet]
            exact hnext _ hp
          have hpred :
              successorWalk next start i = depot :=
            positive_predecessors_eq
              x other (hin other ht)
              hedge hdepartOther
          exact (hp hpred).elim
      | succ j =>
          have htarget :
              successorWalk next start (i + 1) ≠ depot :=
            hleft (i + 1) (by omega)
          have hedgeLeft :
              0 < x (successorWalk next start i)
                (successorWalk next start (i + 1)) := by
            exact hnext _ (hleft i (by omega))
          have hedgeRight :
              0 < x (successorWalk next other j)
                (successorWalk next start (i + 1)) := by
            rw [hmeet]
            exact hnext _ (hright j (by omega))
          have hprevious :
              successorWalk next start i =
                successorWalk next other j :=
            positive_predecessors_eq
              x (successorWalk next start (i + 1))
              (hin _ htarget)
              hedgeLeft hedgeRight
          obtain ⟨hij, hstarts⟩ :=
            ih j
              (fun k hk => hleft k (by omega))
              (fun k hk => hright k (by omega))
              hprevious
          exact ⟨by omega, hstarts⟩
/-- A successor-walk prefix before returning to the depot
contains no repeated vertices. -/
theorem successorVisits_nodup
    (x : V → V → ℕ) (depot : V)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start : V)
    (hdepart : 0 < x depot start)
    (n : ℕ)
    (hbefore : ∀ k, k < n →
      successorWalk next start k ≠ depot) :
    (List.ofFn (fun i : Fin n =>
      successorWalk next start i.val)).Nodup := by
  change
    (List.ofFn (fun i : Fin n =>
      successorWalk next start i.val)).Pairwise
        (fun a b : V => a ≠ b)
  apply (List.pairwise_ofFn
    (f := fun i : Fin n =>
      successorWalk next start i.val)
    (R := fun a b : V => a ≠ b)).mpr
  intro i j hij hmeet
  have hcollision :=
    successorWalk_collision
      x depot hin next hnext
      start start hdepart hdepart
      i.val j.val
      (fun k hk =>
        hbefore k (lt_of_le_of_lt hk i.isLt))
      (fun k hk =>
        hbefore k (lt_of_le_of_lt hk j.isLt))
      hmeet
  have heq : i.val = j.val := hcollision.1
  have hlt : i.val < j.val := hij
  omega

/-- Prefixes from distinct positive-flow depot departures
have no common task vertex before returning to the depot. -/
theorem successorVisits_no_common
    (x : V → V → ℕ) (depot : V)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (start other : V)
    (hdepartStart : 0 < x depot start)
    (hdepartOther : 0 < x depot other)
    (hdifferent : start ≠ other)
    (n m : ℕ)
    (hbeforeStart : ∀ k, k < n →
      successorWalk next start k ≠ depot)
    (hbeforeOther : ∀ k, k < m →
      successorWalk next other k ≠ depot) :
    ∀ v,
      v ∈ List.ofFn (fun i : Fin n =>
        successorWalk next start i.val) →
      v ∉ List.ofFn (fun j : Fin m =>
        successorWalk next other j.val) := by
  intro v hvStart hvOther
  obtain ⟨i, hi⟩ :=
    (List.mem_ofFn'
      (fun i : Fin n =>
        successorWalk next start i.val) v).mp hvStart
  obtain ⟨j, hj⟩ :=
    (List.mem_ofFn'
      (fun j : Fin m =>
        successorWalk next other j.val) v).mp hvOther
  have hmeet :
      successorWalk next start i.val =
        successorWalk next other j.val :=
    hi.trans hj.symm
  have hcollision :=
    successorWalk_collision
      x depot hin next hnext
      start other hdepartStart hdepartOther
      i.val j.val
      (fun k hk =>
        hbeforeStart k (lt_of_le_of_lt hk i.isLt))
      (fun k hk =>
        hbeforeOther k (lt_of_le_of_lt hk j.isLt))
      hmeet
  exact hdifferent hcollision.2

/-- On a vertex set with balanced flow, outgoing and incoming
cut flows agree. Incoming cut flow is expressed using transposition. -/
theorem outCutFlow_eq_transpose
    (x : V → V → ℕ) (S : Finset V)
    (hbalance : ∀ v ∈ S,
      outFlow Finset.univ x v =
        inFlow Finset.univ x v) :
    outCutFlow S x =
      outCutFlow S (fun i j => x j i) := by
  classical
  have hsplit (y : V → V → ℕ) :
      (∑ i ∈ S, outFlow Finset.univ y i) =
        (∑ i ∈ S, ∑ j ∈ S, y i j) +
          outCutFlow S y := by
    unfold outCutFlow
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hfilter :
        Finset.univ.filter (fun j : V => j ∈ S) = S := by
      ext j
      simp
    have hrow :=
      Finset.sum_filter_add_sum_filter_not
        Finset.univ
        (fun j : V => j ∈ S)
        (fun j => y i j)
    rw [hfilter] at hrow
    simpa only [outFlow] using hrow.symm
  have htotal :
      (∑ i ∈ S, outFlow Finset.univ x i) =
        ∑ i ∈ S,
          outFlow Finset.univ (fun a b => x b a) i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hbalance i hi
  have hinternal :
      (∑ i ∈ S, ∑ j ∈ S, x j i) =
        ∑ i ∈ S, ∑ j ∈ S, x i j := by
    exact Finset.sum_comm
  rw [hsplit x, hsplit (fun a b => x b a)] at htotal
  rw [hinternal] at htotal
  omega

/-- A forward-closed predicate containing the depot holds at
every vertex under task degree balance and positive depot-free cuts. -/
theorem all_vertices_of_forward_closed
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (P : V → Prop)
    (hdepot : P depot)
    (hclosed : ∀ i j, P i → 0 < x i j → P j) :
    ∀ v, P v := by
  classical
  intro v
  by_contra hv
  let S : Finset V :=
    Finset.univ.filter (fun i => ¬ P i)
  have hvS : v ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have hdepotS : depot ∉ S := by
    intro hd
    exact (Finset.mem_filter.mp hd).2 hdepot
  have hbalance : ∀ i ∈ S,
      outFlow Finset.univ x i =
        inFlow Finset.univ x i := by
    intro i hi
    have hidepot : i ≠ depot := by
      intro heq
      subst i
      exact hdepotS hi
    rw [hout i hidepot, hin i hidepot]
  have hreverseClosed :
      ∀ i ∈ S, ∀ j, 0 < x j i → j ∈ S := by
    intro i hi j hji
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, ?_⟩
    intro hj
    exact (Finset.mem_filter.mp hi).2
      (hclosed j i hj hji)
  have hinzero :
      outCutFlow S (fun i j => x j i) = 0 :=
    outCutFlow_zero_of_closed
      (fun i j => x j i) S hreverseClosed
  have hcutEq :
      outCutFlow S x =
        outCutFlow S (fun i j => x j i) :=
    outCutFlow_eq_transpose x S hbalance
  have hpositive : 1 ≤ outCutFlow S x :=
    hconn S ⟨v, hvS⟩ hdepotS
  omega

/-- Finite successor-walk prefixes, one for every positive depot
departure and each ending at the depot, cover every task vertex. -/
theorem successorPrefixes_cover
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (next : V → V)
    (hnext : ∀ v, v ≠ depot → 0 < x v (next v))
    (length : V → ℕ)
    (hlength : ∀ start, 0 < x depot start →
      0 < length start)
    (hreturn : ∀ start, 0 < x depot start →
      successorWalk next start (length start) = depot) :
    ∀ v, v ≠ depot →
      ∃ start, 0 < x depot start ∧
        ∃ k, k < length start ∧
          successorWalk next start k = v := by
  classical
  let P : V → Prop := fun v =>
    v = depot ∨
      ∃ start, 0 < x depot start ∧
        ∃ k, k < length start ∧
          successorWalk next start k = v
  have hPdepot : P depot := Or.inl rfl
  have hclosed :
      ∀ i j, P i → 0 < x i j → P j := by
    intro i j hiP hij
    by_cases hjDepot : j = depot
    · exact Or.inl hjDepot
    apply Or.inr
    by_cases hiDepot : i = depot
    · have hdeparture : 0 < x depot j := by
        simpa only [hiDepot] using hij
      exact ⟨j, hdeparture, 0,
        hlength j hdeparture, rfl⟩
    rcases hiP with hi | ⟨start, hs, k, hk, hki⟩
    · exact (hiDepot hi).elim
    · obtain ⟨w, _, hunique⟩ :=
        exists_unique_successor x i (hout i hiDepot)
      have hjnext : j = next i :=
        (hunique j hij).trans
          (hunique (next i) (hnext i hiDepot)).symm
      have hstep :
          successorWalk next start (k + 1) = j := by
        change next (successorWalk next start k) = j
        rw [hki]
        exact hjnext.symm
      have hinside : k + 1 < length start := by
        by_contra h
        have hlast : k + 1 = length start := by
          omega
        have hhit :
            successorWalk next start (k + 1) = depot := by
          rw [hlast]
          exact hreturn start hs
        exact hjDepot (hstep.symm.trans hhit)
      exact ⟨start, hs, k + 1, hinside, hstep⟩
  have hcover : ∀ v, P v :=
    all_vertices_of_forward_closed
      x depot hout hin hconn P hPdepot hclosed
  intro v hv
  rcases hcover v with hdepot | hvisited
  · exact (hv hdepot).elim
  · exact hvisited

/-- Construct a finite family indexed by positive depot departures.
Every route is legal and has no repeated visits; all route edges
lie in the support of x; every task belongs to exactly one route. -/
theorem exists_singleVisit_route_family
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0) :
    ∃ routes :
        {start : V // 0 < x depot start} → LegalRoute depot,
      (∀ d, (routes d).visits.Nodup) ∧
      (∀ d, (routes d).vertices.IsChain
        (fun i j => 0 < x i j)) ∧
      (∀ v, v ≠ depot →
        ∃! d, v ∈ (routes d).visits) := by
  classical
  have hnextExists :
      ∀ v : V, ∃ w : V, v ≠ depot → 0 < x v w := by
    intro v
    by_cases hv : v = depot
    · refine ⟨depot, ?_⟩
      intro hne
      exact (hne hv).elim
    · obtain ⟨w, hw, _⟩ :=
        exists_unique_successor x v (hout v hv)
      exact ⟨w, fun _ => hw⟩
  choose next hnext using hnextExists
  let D := {start : V // 0 < x depot start}
  have hexists :
      ∀ d : D,
        ∃ n : ℕ, 0 < n ∧
          successorWalk next d.val n = depot ∧
          (∀ k, k < n →
            successorWalk next d.val k ≠ depot) ∧
          ∃ r : LegalRoute depot,
            r.visits =
              List.ofFn (fun i : Fin n =>
                successorWalk next d.val i.val) ∧
            r.vertices.IsChain (fun i j => 0 < x i j) := by
    intro d
    exact exists_legalRoute_of_departure
      x depot hout hconn hloop next hnext d.val d.property
  choose n hn hreturn hbefore routes hVisits hChain
    using hexists
  let length : V → ℕ := fun v =>
    if h : 0 < x depot v then n ⟨v, h⟩ else 0
  have hlength :
      ∀ v, 0 < x depot v → 0 < length v := by
    intro v hv
    simpa [length, hv] using hn ⟨v, hv⟩
  have hreturnLength :
      ∀ v, 0 < x depot v →
        successorWalk next v (length v) = depot := by
    intro v hv
    simpa [length, hv] using hreturn ⟨v, hv⟩
  refine ⟨routes, ?_, hChain, ?_⟩
  · intro d
    rw [hVisits d]
    exact successorVisits_nodup
      x depot hin next hnext
      d.val d.property (n d) (hbefore d)
  · intro v hv
    obtain ⟨start, hs, k, hk, hkv⟩ :=
      successorPrefixes_cover
        x depot hout hin hconn next hnext
        length hlength hreturnLength v hv
    let d : D := ⟨start, hs⟩
    have hkn : k < n d := by
      simpa [length, hs, d] using hk
    have hmem : v ∈ (routes d).visits := by
      rw [hVisits d]
      apply (List.mem_ofFn'
        (fun i : Fin (n d) =>
          successorWalk next d.val i.val) v).mpr
      exact ⟨⟨k, hkn⟩, hkv⟩
    refine ⟨d, hmem, ?_⟩
    intro e he
    by_contra hed
    have hne : e.val ≠ d.val := by
      intro heq
      exact hed (Subtype.ext heq)
    have heVisits :
        v ∈ List.ofFn (fun i : Fin (n e) =>
          successorWalk next e.val i.val) := by
      rw [← hVisits e]
      exact he
    have hdVisits :
        v ∈ List.ofFn (fun i : Fin (n d) =>
          successorWalk next d.val i.val) := by
      rw [← hVisits d]
      exact hmem
    exact successorVisits_no_common
      x depot hin next hnext
      e.val d.val e.property d.property hne
      (n e) (n d) (hbefore e) (hbefore d)
      v heVisits hdVisits

omit [DecidableEq V] in
/-- Two natural-valued families summing to one coincide if
the second vanishes wherever the first vanishes. -/
theorem unit_sum_eq_of_zero_support
    (f g : V → ℕ)
    (hf : ∑ v, f v = 1)
    (hg : ∑ v, g v = 1)
    (hsupport : ∀ v, f v = 0 → g v = 0) :
    ∀ v, g v = f v := by
  classical
  obtain ⟨w, hwone, hwzero⟩ :=
    exists_unit_of_sum_one f hf

  have hgzero : ∀ v, v ≠ w → g v = 0 := by
    intro v hv
    exact hsupport v (hwzero v hv)

  have hsum : (∑ v, g v) = g w := by
    apply Finset.sum_eq_single
    · intro v hv hne
      exact hgzero v hne
    · intro hw
      exact (hw (Finset.mem_univ w)).elim

  have hgw : g w = 1 := by
    omega

  intro v
  by_cases hv : v = w
  · subst v
    exact hgw.trans hwone.symm
  · rw [hgzero v hv, hwzero v hv]

omit [DecidableEq V] in
/-- Unit task degrees and support containment determine the entire
flow, provided the original flow has no depot self-loop. -/
theorem flow_eq_of_unit_degrees_and_support
    (x y : V → V → ℕ) (depot : V)
    (hxout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hxin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hyout : ∀ v, v ≠ depot →
      outFlow Finset.univ y v = 1)
    (hyin : ∀ v, v ≠ depot →
      inFlow Finset.univ y v = 1)
    (hdepotLoop : x depot depot = 0)
    (hsupport : ∀ i j, x i j = 0 → y i j = 0) :
    ∀ i j, y i j = x i j := by
  intro i j
  by_cases hi : i = depot

  · subst i
    by_cases hj : j = depot
    · subst j
      exact (hsupport depot depot hdepotLoop).trans
        hdepotLoop.symm

    · have hcolumn : ∀ v, y v j = x v j :=
        unit_sum_eq_of_zero_support
          (fun v => x v j)
          (fun v => y v j)
          (by simpa only [inFlow] using hxin j hj)
          (by simpa only [inFlow] using hyin j hj)
          (fun v hv => hsupport v j hv)
      exact hcolumn depot

  · have hrow : ∀ v, y i v = x i v :=
      unit_sum_eq_of_zero_support
        (fun v => x i v)
        (fun v => y i v)
        (by simpa only [outFlow] using hxout i hi)
        (by simpa only [outFlow] using hyout i hi)
        (fun v hv => hsupport i v hv)
    exact hrow j

omit [Fintype V] [DecidableEq V] in
/-- Every consecutive edge in a positive-flow chain has positive flow. -/
theorem chain_edge_positive
    (x : V → V → ℕ) (route : List V)
    (hchain : route.IsChain (fun i j => 0 < x i j))
    {i j : V}
    (hedge : (i, j) ∈ route.zip route.tail) :
    0 < x i j := by
  induction route with
  | nil =>
      simp at hedge
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hedge
      | cons b tail =>
          obtain ⟨hab, hrest⟩ :=
            List.isChain_cons_cons.mp hchain
          simp only [
            List.tail_cons,
            List.zip_cons_cons,
            List.mem_cons
          ] at hedge
          rcases hedge with heq | hedge
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact hab
          · exact ih hrest hedge

omit [Fintype V] in
/-- Unique route membership and no repeated visits give
total inspection count exactly one at every task. -/
theorem totalVisitCount_eq_one_of_partition
    {ι : Type*} [Fintype ι]
    (depot : V)
    (routes : ι → LegalRoute depot)
    (hnodup : ∀ d, (routes d).visits.Nodup)
    (hcover : ∀ v, v ≠ depot →
      ∃! d, v ∈ (routes d).visits) :
    ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = 1 := by
  classical
  intro v hv
  obtain ⟨d, hd, hunique⟩ := hcover v hv
  have hcount : (routes d).visits.count v = 1 :=
    List.count_eq_one_of_mem (hnodup d) hd
  unfold totalVisitCount
  calc
    (∑ e, (routes e).visits.count v) =
        (routes d).visits.count v := by
      apply Finset.sum_eq_single d
      · intro e he hed
        apply List.count_eq_zero.mpr
        intro hmem
        exact hed (hunique e hmem)
      · intro hdnot
        exact (hdnot (Finset.mem_univ d)).elim
    _ = 1 := hcount

/-- Unit task degrees, no self-loops, and positive depot-free cuts
yield an exact legal route decomposition. Every task is visited
exactly once, and the number of routes equals the depot outflow. -/
theorem exists_exact_singleVisit_decomposition
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0) :
    ∃ routes :
        {start : V // 0 < x depot start} → LegalRoute depot,
      (∀ d, (routes d).visits.Nodup) ∧
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = 1) ∧
      (∀ i j,
        totalRouteFlow Finset.univ routes i j = x i j) ∧
      Fintype.card {start : V // 0 < x depot start} =
        outFlow Finset.univ x depot := by
  classical
  obtain ⟨routes, hnodup, hchain, hcover⟩ :=
    exists_singleVisit_route_family
      x depot hout hin hconn hloop
  have hcounts :
      ∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = 1 :=
    totalVisitCount_eq_one_of_partition
      depot routes hnodup hcover
  have hsupport :
      ∀ i j, x i j = 0 →
        totalRouteFlow Finset.univ routes i j = 0 := by
    intro i j hzero
    unfold totalRouteFlow
    apply Finset.sum_eq_zero
    intro d hd
    unfold routeFlow
    apply List.count_eq_zero.mpr
    intro hedge
    have hpositive : 0 < x i j :=
      chain_edge_positive
        x (routes d).vertices (hchain d) hedge
    omega
  have hyout :
      ∀ v, v ≠ depot →
        outFlow Finset.univ
          (totalRouteFlow Finset.univ routes) v = 1 := by
    intro v hv
    exact
      (total_outFlow_eq_visit_count
        Finset.univ routes v hv).trans
          (hcounts v hv)
  have hyin :
      ∀ v, v ≠ depot →
        inFlow Finset.univ
          (totalRouteFlow Finset.univ routes) v = 1 := by
    intro v hv
    exact
      (total_inFlow_eq_visit_count
        Finset.univ routes v hv).trans
          (hcounts v hv)
  have hExact :
      ∀ i j,
        totalRouteFlow Finset.univ routes i j = x i j :=
    flow_eq_of_unit_degrees_and_support
      x (totalRouteFlow Finset.univ routes) depot
      hout hin hyout hyin (hloop depot) hsupport
  have hflowEq :
      totalRouteFlow Finset.univ routes = x :=
    funext (fun i => funext (hExact i))
  refine ⟨routes, hnodup, hcounts, hExact, ?_⟩
  have hcard :=
    total_outFlow_depot_eq_card Finset.univ routes
  rw [hflowEq] at hcard
  simpa only [Finset.card_univ] using hcard.symm

/-- A task absent from a route has no incoming or outgoing
route flow. -/
theorem routeFlow_zero_at_missing_task
    (depot : V) (r : LegalRoute depot)
    (v : V)
    (hv : v ≠ depot)
    (hmissing : v ∉ r.visits) :
    ∀ u,
      routeFlow r.vertices v u = 0 ∧
      routeFlow r.vertices u v = 0 := by
  intro u
  have hdegree : r.degree v = 0 := by
    simp [LegalRoute.degree, hv,
      List.count_eq_zero.mpr hmissing]
  have hout :
      routeFlow r.vertices v u ≤ r.degree v :=
    (r.routeFlow_bounds v u).2.trans (min_le_left _ _)
  have hin :
      routeFlow r.vertices u v ≤ r.degree v :=
    (r.routeFlow_bounds u v).2.trans (min_le_right _ _)
  rw [hdegree] at hout hin
  omega

/-- A legal route exits its complete task set exactly once.
Repeated task visits are allowed in this lemma. -/
theorem route_own_visit_cut_eq_one
    (depot : V) (r : LegalRoute depot) :
    outCutFlow r.visits.toFinset (routeFlow r.vertices) = 1 := by
  classical
  let S : Finset V := r.visits.toFinset
  change outCutFlow S (routeFlow r.vertices) = 1
  have hdepot : depot ∉ S := by
    intro hd
    exact r.depot_not_mem (List.mem_toFinset.mp hd)
  have hrow (i : V) :
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
        routeFlow r.vertices i j) =
      routeFlow r.vertices i depot := by
    apply Finset.sum_eq_single depot
    · intro j hj hjdepot
      have hmissing : j ∉ r.visits := by
        intro hm
        exact (Finset.mem_filter.mp hj).2
          (List.mem_toFinset.mpr hm)
      exact
        (routeFlow_zero_at_missing_task
          depot r j hjdepot hmissing i).2
    · intro hnot
      apply hnot.elim
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ depot, hdepot⟩
  calc
    outCutFlow S (routeFlow r.vertices) =
        ∑ i ∈ S, routeFlow r.vertices i depot := by
      unfold outCutFlow
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i
    _ = inFlow Finset.univ (routeFlow r.vertices) depot := by
      unfold inFlow
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hnot
      by_cases hidepot : i = depot
      · subst i
        exact r.routeFlow_self_eq_zero depot
      · have hmissing : i ∉ r.visits := by
          intro hm
          exact hnot (List.mem_toFinset.mpr hm)
        exact
          (routeFlow_zero_at_missing_task
            depot r i hidepot hmissing depot).1
    _ = 1 := r.inFlow_depot_eq_one

/-- Under exact single-visit coverage, the aggregate flow exits
the task set of each selected route exactly once. -/
theorem family_route_visit_cut_eq_one
    {ι : Type*} [Fintype ι]
    (depot : V)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = 1)
    (d : ι) :
    outCutFlow (routes d).visits.toFinset
      (totalRouteFlow Finset.univ routes) = 1 := by
  classical
  let S : Finset V := (routes d).visits.toFinset
  change outCutFlow S (totalRouteFlow Finset.univ routes) = 1
  have hdepot : depot ∉ S := by
    intro hd
    exact (routes d).depot_not_mem
      (List.mem_toFinset.mp hd)
  have hmissing
      (e : ι) (hed : e ≠ d)
      (i : V) (hi : i ∈ S) :
      i ∉ (routes e).visits := by
    intro hevisit
    have hiDepot : i ≠ depot := by
      intro heq
      subst i
      exact hdepot hi
    have hdvisit : i ∈ (routes d).visits :=
      List.mem_toFinset.mp hi
    have hdpos : 0 < (routes d).visits.count i :=
      List.count_pos_iff.mpr hdvisit
    have hepos : 0 < (routes e).visits.count i :=
      List.count_pos_iff.mpr hevisit
    have hpair :
        (routes d).visits.count i +
          (routes e).visits.count i ≤
        totalVisitCount Finset.univ routes i :=
      Finset.add_le_sum
        (fun k _ => Nat.zero_le ((routes k).visits.count i))
        (Finset.mem_univ d)
        (Finset.mem_univ e)
        (Ne.symm hed)
    rw [hcounts i hiDepot] at hpair
    omega
  have hother (e : ι) (hed : e ≠ d) :
      outCutFlow S (routeFlow (routes e).vertices) = 0 := by
    unfold outCutFlow
    apply Finset.sum_eq_zero
    intro i hi
    have hiDepot : i ≠ depot := by
      intro heq
      subst i
      exact hdepot hi
    apply Finset.sum_eq_zero
    intro j hj
    exact
      (routeFlow_zero_at_missing_task
        depot (routes e) i hiDepot
        (hmissing e hed i hi) j).1
  calc
    outCutFlow S (totalRouteFlow Finset.univ routes) =
        ∑ e, outCutFlow S (routeFlow (routes e).vertices) :=
      ResourceCuts.cutFlow_sum Finset.univ routes S
    _ = outCutFlow S (routeFlow (routes d).vertices) := by
      apply Finset.sum_eq_single d
      · intro e he hed
        exact hother e hed
      · intro hdnot
        exact (hdnot (Finset.mem_univ d)).elim
    _ = 1 := route_own_visit_cut_eq_one depot (routes d)



/-- For a route without repeated visits, occurrence-based service
equals the sum of service fees over its task set. -/
theorem routeService_eq_task_sum
    (depot : V) (r : LegalRoute depot)
    (service : V → ℚ)
    (hnodup : r.visits.Nodup) :
    ResourceCuts.routeServiceIn r Finset.univ service =
      ∑ v ∈ r.visits.toFinset, service v := by
  classical
  let S : Finset V := r.visits.toFinset
  unfold ResourceCuts.routeServiceIn
  change
    (∑ v, service v * (r.visits.count v : ℚ)) =
      ∑ v ∈ S, service v
  calc
    (∑ v, service v * (r.visits.count v : ℚ)) =
        ∑ v ∈ S, service v * (r.visits.count v : ℚ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v hv hnot
      have hmissing : v ∉ r.visits := by
        intro hm
        exact hnot (List.mem_toFinset.mpr hm)
      rw [List.count_eq_zero.mpr hmissing]
      simp
    _ = ∑ v ∈ S, service v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hcount : r.visits.count v = 1 :=
        List.count_eq_one_of_mem hnodup
          (List.mem_toFinset.mp hv)
      rw [hcount]
      simp

/-- A rounded capacity bound of one implies that the work
fits within one positive budget. -/
theorem service_le_of_ceil_div_le_one
    (W T : ℚ)
    (hT : 0 < T)
    (hceil : Int.ceil (W / T) ≤ (1 : ℤ)) :
    W ≤ T := by
  have hquot : W / T ≤ (1 : ℚ) := by
    simpa using (Int.ceil_le.mp hceil)
  have hmul : W ≤ (1 : ℚ) * T :=
    (div_le_iff₀ hT).mp hquot
  simpa using hmul

/-- In the single-visit model, positive depot-free connectivity
and all rounded service-capacity cuts yield an exact legal route
decomposition satisfying every individual service budget. -/
theorem exists_budget_feasible_singleVisit_decomposition
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0)
    (service : V → ℚ) (T : ℚ)
    (hT : 0 < T)
    (hcuts : ∀ S : Finset V,
      S.Nonempty → depot ∉ S →
      Int.ceil ((∑ v ∈ S, service v) / T) ≤
        (outCutFlow S x : ℤ)) :
    ∃ routes :
        {start : V // 0 < x depot start} → LegalRoute depot,
      (∀ d, (routes d).visits.Nodup) ∧
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = 1) ∧
      (∀ i j,
        totalRouteFlow Finset.univ routes i j = x i j) ∧
      (Fintype.card {start : V // 0 < x depot start} =
        outFlow Finset.univ x depot) ∧
      (∀ d,
        ResourceCuts.routeServiceIn
          (routes d) Finset.univ service ≤ T) := by
  classical
  obtain ⟨routes, hnodup, hcounts, hExact, hcard⟩ :=
    exists_exact_singleVisit_decomposition
      x depot hout hin hconn hloop
  have hflowEq :
      totalRouteFlow Finset.univ routes = x :=
    funext (fun i => funext (hExact i))
  refine ⟨routes, hnodup, hcounts, hExact, hcard, ?_⟩
  intro d
  let S : Finset V := (routes d).visits.toFinset
  have hnonempty : S.Nonempty := by
    cases hlist : (routes d).visits with
    | nil =>
        exact ((routes d).visits_nonempty hlist).elim
    | cons a rest =>
        exact ⟨a, by simp [S, hlist]⟩
  have hdepot : depot ∉ S := by
    intro hd
    exact (routes d).depot_not_mem
      (List.mem_toFinset.mp hd)
  have hcut : outCutFlow S x = 1 := by
    rw [← hflowEq]
    exact family_route_visit_cut_eq_one
      depot routes hcounts d
  have hrounded :
      Int.ceil ((∑ v ∈ S, service v) / T) ≤ (1 : ℤ) := by
    have h := hcuts S hnonempty hdepot
    simpa only [hcut, Nat.cast_one] using h
  have hbudget : (∑ v ∈ S, service v) ≤ T :=
    service_le_of_ceil_div_le_one
      (∑ v ∈ S, service v) T hT hrounded
  rw [routeService_eq_task_sum
    depot (routes d) service (hnodup d)]
  exact hbudget
/-- Nonnegative fees ensure that service on a subset does not
exceed the route's total service. -/
theorem routeServiceIn_le_univ_of_nonneg
    (depot : V) (r : LegalRoute depot)
    (S : Finset V) (service : V → ℚ)
    (hservice : ∀ v, 0 ≤ service v) :
    ResourceCuts.routeServiceIn r S service ≤
      ResourceCuts.routeServiceIn r Finset.univ service := by
  unfold ResourceCuts.routeServiceIn
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ S)
  intro v hv hnot
  exact mul_nonneg (hservice v) (Nat.cast_nonneg _)

/-- Exact coverage, exact edge-flow recovery, and individual
service budgets imply every depot-free rounded capacity cut.
This direction allows any finite route index type. -/
theorem rounded_service_cuts_of_exact_family
    {ι : Type*} [Fintype ι]
    (x : V → V → ℕ) (depot : V)
    (routes : ι → LegalRoute depot)
    (service : V → ℚ) (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = 1)
    (hExact : ∀ i j,
      totalRouteFlow Finset.univ routes i j = x i j)
    (hbudget : ∀ d,
      ResourceCuts.routeServiceIn
        (routes d) Finset.univ service ≤ T) :
    ∀ S : Finset V, depot ∉ S →
      Int.ceil ((∑ v ∈ S, service v) / T) ≤
        (outCutFlow S x : ℤ) := by
  classical
  intro S hdepot
  have hflowEq :
      totalRouteFlow Finset.univ routes = x :=
    funext (fun i => funext (hExact i))
  have hchain :=
    ResourceCuts.requiredService_integer_capacity_chain
      Finset.univ routes S service
      (fun _ => 1)
      (fun _ => 0)
      T 0
      hdepot
      hcounts
      (by simpa only [sub_zero] using hT)
      (by
        intro d hd
        have hsub :=
          routeServiceIn_le_univ_of_nonneg
            depot (routes d) S service hservice
        simpa only [add_zero] using
          hsub.trans (hbudget d))
      (by
        intro d hd hserves
        exact le_refl (0 : ℚ))
  have hceil := hchain.1.trans hchain.2
  simpa only [
    ResourceCuts.requiredServiceIn,
    Nat.cast_one,
    mul_one,
    sub_zero,
    hflowEq
  ] using hceil

/-- Under the single-visit structural assumptions and nonnegative
service fees, all rounded service cuts are equivalent to the
existence of a budget-feasible exact legal route decomposition. -/
theorem rounded_service_cuts_iff_exact_decomposition
    (x : V → V → ℕ) (depot : V)
    (hout : ∀ v, v ≠ depot →
      outFlow Finset.univ x v = 1)
    (hin : ∀ v, v ≠ depot →
      inFlow Finset.univ x v = 1)
    (hconn : ∀ S : Finset V,
      S.Nonempty → depot ∉ S → 1 ≤ outCutFlow S x)
    (hloop : ∀ v, x v v = 0)
    (service : V → ℚ) (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T) :
    (∀ S : Finset V,
      S.Nonempty → depot ∉ S →
      Int.ceil ((∑ v ∈ S, service v) / T) ≤
        (outCutFlow S x : ℤ)) ↔
    (∃ routes :
        {start : V // 0 < x depot start} → LegalRoute depot,
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = 1) ∧
      (∀ i j,
        totalRouteFlow Finset.univ routes i j = x i j) ∧
      (∀ d,
        ResourceCuts.routeServiceIn
          (routes d) Finset.univ service ≤ T)) := by
  constructor
  · intro hcuts
    obtain ⟨routes, hnodup, hcounts, hExact, hcard, hbudget⟩ :=
      exists_budget_feasible_singleVisit_decomposition
        x depot hout hin hconn hloop service T hT hcuts
    exact ⟨routes, hcounts, hExact, hbudget⟩
  · rintro ⟨routes, hcounts, hExact, hbudget⟩
    intro S hnonempty hdepot
    exact rounded_service_cuts_of_exact_family
      x depot routes service T hservice hT
      hcounts hExact hbudget S hdepot




end UAVProof.SingleVisitDecomposition

#print axioms UAVProof.SingleVisitDecomposition.exists_unit_of_sum_one
#print axioms UAVProof.SingleVisitDecomposition.outFlow_one_row
#print axioms UAVProof.SingleVisitDecomposition.inFlow_one_column
#print axioms UAVProof.SingleVisitDecomposition.exists_unique_successor
#print axioms UAVProof.SingleVisitDecomposition.exists_unique_predecessor
#print axioms UAVProof.SingleVisitDecomposition.outCutFlow_zero_of_closed
#print axioms UAVProof.SingleVisitDecomposition.no_closed_task_set
#print axioms UAVProof.SingleVisitDecomposition.exists_unit_successor_exit
#print axioms UAVProof.SingleVisitDecomposition.successorWalk_reaches_depot
#print axioms UAVProof.SingleVisitDecomposition.exists_first_return_segment
#print axioms UAVProof.SingleVisitDecomposition.exists_legalRoute_of_departure
#print axioms UAVProof.SingleVisitDecomposition.positive_predecessors_eq
#print axioms UAVProof.SingleVisitDecomposition.successorWalk_collision
#print axioms UAVProof.SingleVisitDecomposition.successorVisits_nodup
#print axioms UAVProof.SingleVisitDecomposition.successorVisits_no_common
#print axioms UAVProof.SingleVisitDecomposition.outCutFlow_eq_transpose
#print axioms UAVProof.SingleVisitDecomposition.all_vertices_of_forward_closed
#print axioms UAVProof.SingleVisitDecomposition.successorPrefixes_cover
#print axioms UAVProof.SingleVisitDecomposition.exists_singleVisit_route_family
#print axioms UAVProof.SingleVisitDecomposition.unit_sum_eq_of_zero_support
#print axioms UAVProof.SingleVisitDecomposition.flow_eq_of_unit_degrees_and_support
#print axioms UAVProof.SingleVisitDecomposition.chain_edge_positive
#print axioms UAVProof.SingleVisitDecomposition.totalVisitCount_eq_one_of_partition
#print axioms UAVProof.SingleVisitDecomposition.exists_exact_singleVisit_decomposition
#print axioms UAVProof.SingleVisitDecomposition.routeFlow_zero_at_missing_task
#print axioms UAVProof.SingleVisitDecomposition.route_own_visit_cut_eq_one
#print axioms UAVProof.SingleVisitDecomposition.family_route_visit_cut_eq_one
#print axioms UAVProof.SingleVisitDecomposition.routeService_eq_task_sum
#print axioms UAVProof.SingleVisitDecomposition.service_le_of_ceil_div_le_one
#print axioms UAVProof.SingleVisitDecomposition.exists_budget_feasible_singleVisit_decomposition
#print axioms UAVProof.SingleVisitDecomposition.routeServiceIn_le_univ_of_nonneg
#print axioms UAVProof.SingleVisitDecomposition.rounded_service_cuts_of_exact_family
#print axioms UAVProof.SingleVisitDecomposition.rounded_service_cuts_iff_exact_decomposition
