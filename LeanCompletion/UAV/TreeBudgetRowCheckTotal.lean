import LeanCompletion.UAV.TreeBudgetRowCheckLoop
import LeanCompletion.UAV.TreeBudgetRowCheckModelSpec

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2 A4RowCheckModel TreeBudgetParentArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem retained_store (P H row plus minus root tp tn ctx suffix : Bits) :
    retained (store P H row plus minus root tp tn ctx suffix)=
      store P H row plus minus root tp tn ctx suffix := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

def run_congr {a a' b b' : Configuration K (Label PC)} {t : ℕ}
    (ha : a=a') (hb : b=b') (r : Run instructions a b t) : Run instructions a' b' t :=
  ha ▸ hb ▸ r

def root_gate_run (P H plus minus tp tn ctx suffix : Bits) (rows : List ℕ) (root : ℕ)
    (hr : root<rows.length) :
    Execution (start P H (rows.flatMap encodeNat) plus minus root.bits tp tn ctx suffix)
      (if rows[root]=0 then cfg .prepP (store P H (rows.flatMap encodeNat) plus minus root.bits tp tn ctx suffix)
       else stopped false P H (rows.flatMap encodeNat) plus minus root.bits tp tn ctx suffix) := by
  let s := store P H (rows.flatMap encodeNat) plus minus root.bits tp tn ctx suffix
  have look := lookup_index_block .rootLookup .rootTest 0 true rfl s rows root hr rfl rfl
    (by intro k; rfl) rfl rfl
  have test := test_run instructions .rootTest .rootClear bad (reg 23) rfl (set s 23 rows[root].bits)
  change Run instructions (cfg .rootTest (set s 23 rows[root].bits))
    (cfg (if rows[root].bits.isEmpty then .rootClear else bad) (set s 23 rows[root].bits)) 1 at test
  simp only [TreeBudgetIntTM2.bits_empty_iff] at test
  by_cases hz : rows[root]=0
  · simp only [if_pos hz] at test
    have he : set s 23 rows[root].bits=s := by
      rw [hz]
      change Function.update s (reg 23) (s (reg 23))=s
      simp
    have clear := clear_run instructions .rootClear .prepP
      ⟨reg 23,reg 24,reg 26,by decide,by decide,by decide⟩ rfl s rfl
    have he' : Function.update s (reg 23) []=s := by
      change Function.update s (reg 23) (s (reg 23))=s
      simp
    rw [he'] at clear
    have clear' : Run instructions (cfg .rootClear (set s 23 rows[root].bits)) (cfg .prepP s)
        ((s (reg 23)).length+2) := run_congr (by rw [he]) rfl clear
    exact ⟨_,run_congr rfl (by simp [hz,s]) (seq instructions (seq instructions look.property test) clear')⟩
  · simp only [if_neg hz] at test
    let s' := set s 23 rows[root].bits
    have clean := cleanup_run false 25 0 rfl s' (workSize s')
      (by simp [s',set,reg,s,store]) (le_workSize s')
    have he : wipe s' 0=s := by
      funext k
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> simp [wipe,s',s,set,store,reg]
    rw [he] at clean
    exact ⟨_,run_congr rfl (by simp [hz,s,stopped]) (seq instructions (seq instructions look.property test) clean)⟩

theorem nodes_body {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) :
    body (nodes P H Ap An p) Node.parent=(P.parents.toList.map Fin.val).flatMap encodeNat ∧
    body (nodes P H Ap An p) Node.cap=H.toList.flatMap encodeNat ∧
    body (nodes P H Ap An p) Node.coord=p.toList.flatMap encodeNat ∧
    body (nodes P H Ap An p) Node.plus=Ap.toList.flatMap encodeNat ∧
    body (nodes P H Ap An p) Node.minus=An.toList.flatMap encodeNat := by
  have toList_eq {α : Type} (xs : Vector α n) : xs.toList=List.ofFn fun v : Fin n => xs[v] := by
    simpa only [Vector.toList_ofFn] using
      congrArg Vector.toList (Vector.ofFn_getElem (xs := xs)).symm
  simp [body,nodes,List.map_ofFn,Function.comp_def,toList_eq]

def row_run {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n)
    (budget : ℤ) (ctx suffix : Bits) :
    Execution
      (start ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
        (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix)
      (stopped (rowResult P H Ap An p budget)
        ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
        (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix) := by
  let s := store ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
    (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
    P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix
  have first := root_gate_run ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
    (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat) budget.toNat.bits (-budget).toNat.bits ctx suffix
    p.toList P.root.val (by simpa using P.root.isLt)
  have prep := prepare_run ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
    (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
    P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix
  have loop := loop_run s p.toList Ap.toList An.toList P.root.val rfl rfl rfl rfl
    (nodes P H Ap An p) ((-budget).toNat.bits,budget.toNat.bits,[]) (by
      intro v hv
      simp only [nodes,List.mem_ofFn] at hv
      obtain ⟨i,rfl⟩ := hv
      simpa using (show (P.parents[i]).val<n ∧ (P.parents[i]).val<n ∧ (P.parents[i]).val<n from
        ⟨(P.parents[i]).isLt,(P.parents[i]).isLt,(P.parents[i]).isLt⟩))
  have bodies := nodes_body P H Ap An p
  have hret : retained s=s := retained_store _ _ _ _ _ _ _ _ _ _
  have hroot_eq : p.toList[P.root.val]=p[P.root] := by simp
  by_cases hz : p[P.root]=0
  · have hz' : p[(P.root : ℕ)]=0 := hz
    have firstProp : Run instructions (start ((P.parents.toList.map Fin.val).flatMap encodeNat)
        (H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat)
        (An.toList.flatMap encodeNat) P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix)
        (cfg .prepP s) first.val :=
      run_congr rfl (by simp [hroot_eq,hz,s]) first.property
    have loopProp : Run instructions (cfg .loop (ready s ((P.parents.toList.map Fin.val).flatMap encodeNat)
        (H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat)
        (An.toList.flatMap encodeNat) (-budget).toNat.bits budget.toNat.bits []))
        (stopped (rowResult P H Ap An p budget) ((P.parents.toList.map Fin.val).flatMap encodeNat)
          (H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat)
          (An.toList.flatMap encodeNat) P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix)
        loop.val :=
      run_congr (by simp [loopState,bodies.1,bodies.2.1,bodies.2.2.1,bodies.2.2.2.1,bodies.2.2.2.2])
        (by simp [hret,rowResult,hz',stopped,s]) loop.property
    exact ⟨_, seq instructions (seq instructions firstProp prep.property) loopProp⟩
  · have hn : p[(P.root : ℕ)]≠0 := hz
    exact ⟨first.val, run_congr rfl (by simp [hroot_eq,rowResult,hn]) first.property⟩

end UAVProof.A4RowCheck
