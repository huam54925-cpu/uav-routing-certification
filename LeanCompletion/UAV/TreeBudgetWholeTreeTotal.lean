import LeanCompletion.UAV.TreeBudgetWholeTreeRuns

namespace UAVProof.TreeBudgetWholeTreeTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray
open Turing StateTransition

def suffix {n : ℕ} (P : ParentArray n) (i : ℕ) : Bool :=
  (List.finRange n).all (fun v => decide (i ≤ v.val → follow P n v = P.root))

theorem suffix_end {n : ℕ} (P : ParentArray n) : suffix P n = true := by
  simp only [suffix,List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq]
  intro v hv
  omega

theorem suffix_step {n : ℕ} (P : ParentArray n) (v : Fin n) :
    suffix P v.val = (decide (follow P n v = P.root) && suffix P (v.val+1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [suffix,List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq,Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨h v le_rfl,fun w hw => h w (by omega)⟩
  · rintro ⟨h,hs⟩ w hw
    by_cases he : w.val = v.val
    · simpa [Fin.ext he] using h
    · exact hs w (by omega)

def hopBound {n : ℕ} (P : ParentArray n) : ℕ :=
  32*(2*((TreeBudgetParentWalkTM2.body P).length+2*n.size+1)+1)^2
def iterationBound {n : ℕ} (P : ParentArray n) : ℕ :=
  n*hopBound P+3*(TreeBudgetParentWalkTM2.body P).length+4*n.size+2*n+
    3*(encodeNat P.root.val).length+20
def setupBound {n : ℕ} (P : ParentArray n) : ℕ :=
  hopBound P+5*(TreeBudgetParentWalkTM2.body P).length+2*n+5*(encodeNat P.root.val).length+16
def totalBound {n : ℕ} (P : ParentArray n) := setupBound P+n*iterationBound P+1

def typed_call {n : ℕ} (P : ParentArray n) (v : Fin n) (ticks : Bits) (root : Bool) (d : Data) :
    Run (cfg (callEntry root) {d with
        q := TreeBudgetParentWalkTM2.query P v
        r := encodeNat P.root.val
        t := ticks})
      (called root d (TreeBudgetWalkRootTM2.finish ticks (TreeBudgetParentWalkTM2.query P v)
        (encodeNat P.root.val) [])) (ticks.length*hopBound P+(encodeNat P.root.val).length+3) := by
  apply weaken (endpoint_run root {d with
    q := TreeBudgetParentWalkTM2.query P v
    r := encodeNat P.root.val
    t := ticks})
  have h := TreeBudgetParentWalkTM2.query_width P v
  dsimp only [hopBound]
  gcongr

theorem called_preserved {n : ℕ} (P : ParentArray n) (ctx : Bits) (i left : ℕ)
    (root : Bool) (c : TreeBudgetWalkRootTM2.Cfg) :
    Preserved P ctx (called root (ready P ctx i left) c) := ⟨rfl,rfl,rfl⟩

/-- Loop invariant: the next binary index is i, there are left tokens, and
i+left=n. Every recursive call reuses the saved table, root and context. -/
theorem loop_run {n : ℕ} (P : ParentArray n) (ctx : Bits) (left i : ℕ) (hi : i+left=n) :
    ∃ out, Nonempty (Run (cfg (ctl .test) (ready P ctx i left)) out
      (left*iterationBound P+1)) ∧ out.l = none ∧ out.var.2 = suffix P i ∧ Preserved P ctx out := by
  induction left generalizing i with
  | zero =>
    have hin : i=n := by omega
    subst i
    refine ⟨stop (ready P ctx n 0) true,⟨weaken (once ?_) (by simp)⟩,rfl,?_,⟨rfl,rfl,rfl⟩⟩
    · simp only [machine,FinTM2.step,TM2.step,cfg,ctl,program,TM2.stepAux,
        TreeBudgetStackRoutine.scan,stop]
      change some (⟨none,(none,true),Function.update (store (ready P ctx n 0)) queue
        (store (ready P ctx n 0) queue)⟩ : Cfg) = some ⟨none,(none,true),store (ready P ctx n 0)⟩
      rw [Function.update_eq_self]
    · exact (suffix_end P).symm
  | succ left ih =>
    let v : Fin n := ⟨i,by omega⟩
    let d := ready P ctx i left
    let c := TreeBudgetWalkRootTM2.finish (List.replicate n true)
      (TreeBudgetParentWalkTM2.query P v) (encodeNat P.root.val) []
    have hs : i.bits.length ≤ n.size := by
      simpa only [Nat.size_eq_bits_len] using (Nat.size_le_size (show i ≤ n by omega))
    have a := prepare_vertex P ctx v left
    have b := once (call_step (vertexReady P ctx v left))
    have e := typed_call P v (List.replicate n true) false d
    have seq := EvalsToInTime.trans machine.step _ _ _ _ _ a b
    have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq e
    have hc : c.l = none := TreeBudgetWalkRootTM2.finish_terminal ..
    have hv : c.var.2 = decide (follow P n v = P.root) := by
      simpa only [c,TreeBudgetCostedInput.followCost_value,List.length_replicate] using
        TreeBudgetWalkRootTM2.endpoint_is_root P (List.replicate n true) [] v
    cases hf : c.var.2 with
    | false =>
      have last := once (reject_step false d c hc hf)
      refine ⟨{called false d c with l := none},⟨weaken
        (EvalsToInTime.trans machine.step _ _ _ _ _ seq last) ?_⟩,rfl,?_,called_preserved P ctx i left false c⟩
      · simp only [List.length_replicate,iterationBound,Nat.add_mul,Nat.one_mul]
        dsimp only [v]
        omega
      · change c.var.2 = suffix P v.val
        rw [suffix_step,← hv,hf]
        rfl
    | true =>
      have hr := successful_return P v (List.replicate n true) false d hf
      change called false d c = _ at hr
      rw [hr] at seq
      have recyc := recycle_vertex P ctx i left
      have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq recyc
      obtain ⟨out,⟨tail⟩,hl,hval,hkeep⟩ := ih (i+1) (by omega)
      refine ⟨out,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq tail) ?_⟩,hl,?_,hkeep⟩
      · simp only [List.length_replicate,Nat.add_mul,Nat.one_mul]
        dsimp only [iterationBound,v]
        omega
      · rw [hval]
        change suffix P (v.val+1) = suffix P v.val
        rw [suffix_step,← hv,hf]
        rfl

/-- Complete tree validation from a parsed parent table. This theorem also
covers invalid parent functions (cycles or a nonfixed root). -/
theorem whole_tree_run {n : ℕ} (P : ParentArray n) (ctx : Bits) :
    ∃ out, Nonempty (Run (start P ctx) out (totalBound P)) ∧ out.l = none ∧
      out.var.2 = (TreeBudgetCostedInput.validateCost P).value ∧ Preserved P ctx out := by
  let d := ready P ctx 0 n
  let c := TreeBudgetWalkRootTM2.finish [true] (TreeBudgetParentWalkTM2.query P P.root)
    (encodeNat P.root.val) []
  have a := prepare_root P ctx
  have b := once (root_call_step (rootReady P ctx))
  have e := typed_call P P.root [true] true d
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ a b
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq e
  have hc : c.l = none := TreeBudgetWalkRootTM2.finish_terminal ..
  have hv : c.var.2 = decide (parent P P.root = P.root) := by
    simpa [c,TreeBudgetCostedInput.followCost_value,follow] using
      TreeBudgetWalkRootTM2.endpoint_is_root P [true] [] P.root
  have spec : (TreeBudgetCostedInput.validateCost P).value = (c.var.2 && suffix P 0) := by
    rw [TreeBudgetCostedInput.validateCost_value,hv]
    simp [validateB,suffix]
  cases hf : c.var.2 with
  | false =>
    have last := once (reject_step true d c hc hf)
    refine ⟨{called true d c with l := none},⟨weaken
      (EvalsToInTime.trans machine.step _ _ _ _ _ seq last) ?_⟩,rfl,?_,called_preserved P ctx 0 n true c⟩
    · simp only [totalBound,setupBound,List.length_cons,List.length_nil]
      omega
    · change c.var.2 = _
      rw [spec,hf]
      rfl
  | true =>
    have hr := successful_return P P.root [true] true d hf
    change called true d c = _ at hr
    rw [hr] at seq
    have dispatch := once (return_step true {d with q := TreeBudgetParentWalkTM2.body P})
    have clear := clear_job .rootClear {d with q := TreeBudgetParentWalkTM2.body P}
    simp only [replace,source,dest,next] at clear
    have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq dispatch
    have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq clear
    obtain ⟨out,⟨tail⟩,hl,hval,hkeep⟩ := loop_run P ctx n 0 (by omega)
    refine ⟨out,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq tail) ?_⟩,hl,?_,hkeep⟩
    · simp only [totalBound,setupBound,List.length_cons,List.length_nil]
      omega
    · rw [spec,hf,hval]
      rfl

theorem vertices_le_body {n : ℕ} (P : ParentArray n) :
    n ≤ (TreeBudgetParentWalkTM2.body P).length := by
  have h := length_le_flatMap encodeNat encodeNat_nonempty (TreeBudgetParentWalkTM2.table P)
  simpa [TreeBudgetParentWalkTM2.table,TreeBudgetParentWalkTM2.body] using h

/-- A bound in the actual entry data length B+R; context is never scanned. -/
theorem totalBound_polynomial {n : ℕ} (P : ParentArray n) :
    totalBound P ≤ 4096*((TreeBudgetParentWalkTM2.body P).length+(encodeNat P.root.val).length+1)^4 := by
  let B := (TreeBudgetParentWalkTM2.body P).length
  let R := (encodeNat P.root.val).length
  let S := B+R+1
  have hn : n ≤ B := vertices_le_body P
  have hs : n.size ≤ n := TreeBudgetCostedCodec.nat_size_le n
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hB : B ≤ S := by dsimp [S]; omega
  have hR : R ≤ S := by dsimp [S]; omega
  have hN : n ≤ S := hn.trans hB
  have hsize : n.size ≤ S := hs.trans hN
  have hQ : 2*(B+2*n.size+1)+1 ≤ 7*S := by dsimp [S]; omega
  have hH : hopBound P ≤ 1568*S^2 := by
    calc
      hopBound P = 32*(2*(B+2*n.size+1)+1)^2 := rfl
      _ ≤ 32*(7*S)^2 := by gcongr
      _ = _ := by ring
  have hp2 : S ≤ S^2 := Nat.le_self_pow (by decide) S
  have hp3 : S^2 ≤ S^3 := by nlinarith
  have hp4 : S^3 ≤ S^4 := by nlinarith
  have hC : iterationBound P ≤ 1600*S^3 := by
    have hprod : n*hopBound P ≤ S*(1568*S^2) := Nat.mul_le_mul hN hH
    change n*hopBound P+3*B+4*n.size+2*n+3*R+20 ≤ _
    nlinarith
  have hA : setupBound P ≤ 1596*S^2 := by
    change hopBound P+5*B+2*n+5*R+16 ≤ _
    nlinarith
  have hprod : n*iterationBound P ≤ S*(1600*S^3) := Nat.mul_le_mul hN hC
  change setupBound P+n*iterationBound P+1 ≤ 4096*S^4
  nlinarith

theorem whole_tree_polynomial {n : ℕ} (P : ParentArray n) (ctx : Bits) :
    ∃ out, Nonempty (Run (start P ctx) out
      (4096*((TreeBudgetParentWalkTM2.body P).length+(encodeNat P.root.val).length+1)^4)) ∧
      out.l = none ∧ out.var.2 = (TreeBudgetCostedInput.validateCost P).value ∧ Preserved P ctx out := by
  obtain ⟨out,⟨run⟩,hl,hv,hp⟩ := whole_tree_run P ctx
  exact ⟨out,⟨weaken run (totalBound_polynomial P)⟩,hl,hv,hp⟩

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetWholeTreeTM2
