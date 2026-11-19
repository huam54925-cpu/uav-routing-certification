import LeanCompletion.UAV.TreeBudgetParentWalkTotal

/-! Compare the actual returned address of a bounded parent walk with a
caller-supplied root code. The body after the address is not part of the test. -/
namespace UAVProof.TreeBudgetWalkRootTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray Turing StateTransition
open Turing.TM2.Stmt
abbrev K := TreeBudgetParentWalkTM2.K ⊕ Unit
abbrev L := TreeBudgetParentWalkTM2.L ⊕ Fin 2
abbrev Cfg := Configuration K L
abbrev cursor : K := .inl TreeBudgetParentWalkTM2.src
abbrev rootCode : K := .inr ()
def endWith (b : Bool) : Statement K L := load (fun _ => (none,b)) halt

def program : L → Statement K L
  | .inl l => compile Sum.inl (.inr 0) (TreeBudgetParentWalkTM2.program l)
  | .inr l => if l = 0 then branch Prod.snd (load (fun _ => (none,true)) (goto fun _ => .inr 1)) halt
    else pop rootCode (fun _ b => (b,true))
      (branch (fun v => v.1.isNone) (endWith true)
        (pop cursor (fun v b => (none,b == v.1))
          (branch Prod.snd (goto (fun _ => .inr 1)) (endWith false))))

def machine : FinTM2 where
  K := K
  k₀ := cursor
  k₁ := rootCode
  Γ _ := Bool
  Λ := L
  main := .inl (.inr 7)
  σ := State
  initialState := (none,true)
  m := program

def called (r : Bits) := embed (K := TreeBudgetParentWalkTM2.K) (Λ := TreeBudgetParentWalkTM2.L)
  Sum.inl (Sum.inr (0 : Fin 2)) (fun _ : Unit => r)
def checkCfg (base : K → Bits) (q r : Bits) : Cfg :=
  ⟨some (.inr 1),(none,true),Function.update (Function.update base cursor q) rootCode r⟩

def prefixTest : Bits → Bits → Bool
  | [], _ => true
  | _::_, [] => false
  | b::r,d::q => (b == d) && prefixTest r q

/-- The number of symbols consumed on a mismatch is immaterial to the caller. -/
def finishCheck (base : K → Bits) : Bits → Bits → Cfg
  | [], q => {checkCfg base q [] with l := none,var := (none,true)}
  | _::r, [] => {checkCfg base [] r with l := none,var := (none,false)}
  | b::r, d::q => if b = d then finishCheck base r q else
      {checkCfg base q r with l := none,var := (none,false)}

local macro "check_step" : tactic => `(tactic|
  (simp [machine,FinTM2.step,TM2.step,TM2.stepAux,checkCfg,program,endWith,Function.update_apply]
   all_goals congr 2
   all_goals funext k; by_cases hc : k = cursor <;> by_cases hr : k = rootCode <;> simp_all [Function.update_apply]))

def compare_run (base : K → Bits) (r q : Bits) :
    EvalsToInTime machine.step (checkCfg base q r) (some (finishCheck base r q)) (r.length+1) := by
  induction r generalizing q with
  | nil => simp only [finishCheck]; apply once; check_step
  | cons b r ih =>
    cases q with
    | nil =>
      simp only [finishCheck]
      apply weaken (once ?_) (by simp)
      cases b <;> check_step
    | cons d q =>
      by_cases hb : b = d
      · subst d
        simp only [finishCheck]
        apply prepend _ (ih q)
        cases b <;> check_step
      · simp only [finishCheck,if_neg hb]
        apply weaken (once ?_) (by simp)
        cases b <;> cases d <;> first | contradiction | check_step

theorem compare_value (base : K → Bits) (r q : Bits) :
    (finishCheck base r q).var.2 = prefixTest r q := by
  induction r generalizing q with
  | nil => rfl
  | cons b r ih =>
    cases q with
    | nil => rfl
    | cons d q =>
      by_cases h : b = d <;> simp [finishCheck,prefixTest,h,ih]

theorem at_root_code (v root : ℕ) (tail : Bits) :
    prefixTest (encodeNat root) (encodeNat v ++ tail) = decide (v = root) := by
  have code (a b : Bits) : prefixTest (word a) (word b ++ tail) = decide (a = b) := by
    induction a generalizing b with
    | nil => cases b <;> rfl
    | cons c a ih =>
      cases b with
      | nil => rfl
      | cons d b =>
        by_cases h : c = d
        · subst d; simpa [word,prefixTest] using ih b
        · cases c <;> cases d <;> first | contradiction | simp [word,prefixTest]
  rw [encodeNat,encodeNat,code]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; simpa using (congrArg value h).symm
  · rintro rfl; rfl

def start (ticks q root ctx : Bits) := called root (TreeBudgetParentWalkTM2.cfg 7 q [] [] [] ticks ctx)
def finish (ticks q root ctx : Bits) : Cfg :=
  let c := TreeBudgetParentWalkTM2.walkEnd ticks q ctx
  if c.var.2 then finishCheck (called root c).stk root (c.stk TreeBudgetParentWalkTM2.src)
  else {called root c with l := none}

def root_run (ticks q root ctx : Bits) : EvalsToInTime machine.step (start ticks q root ctx)
    (some (finish ticks q root ctx)) (ticks.length*(32*(2*q.length+1)^2)+root.length+3) := by
  let c := TreeBudgetParentWalkTM2.walkEnd ticks q ctx
  have hw := call_run (R := Unit) Sum.inl (Sum.inr (0 : Fin 2)) (fun _ => root)
    TreeBudgetParentWalkTM2.program program (fun _ => rfl) (TreeBudgetParentWalkTM2.total_run ticks q ctx)
  have hl : c.l = none := TreeBudgetParentWalkTM2.terminal ..
  cases hf : c.var.2 with
  | false =>
    have step : machine.step (called root c) = some (finish ticks q root ctx) := by
      change _ = some (if c.var.2 then _ else {called root c with l := none})
      simp [machine,FinTM2.step,TM2.step,TM2.stepAux,called,embed,hl,hf,program]
    exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ hw (once step)) (by omega)
  | true =>
    have step : machine.step (called root c) =
        some (checkCfg (called root c).stk (c.stk TreeBudgetParentWalkTM2.src) root) := by
      simp [machine,FinTM2.step,TM2.step,TM2.stepAux,called,embed,hl,hf,program,checkCfg]
      all_goals congr 2
      all_goals funext k; by_cases hc : k = cursor <;> by_cases hr : k = rootCode <;>
        simp_all [Function.update_apply,banks]
    have run := EvalsToInTime.trans machine.step _ _ _ _ _ hw (once step)
    have endRun := compare_run (called root c).stk root (c.stk TreeBudgetParentWalkTM2.src)
    change EvalsToInTime machine.step _ (some (if c.var.2 then _ else _)) _
    rw [if_pos hf]
    exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ run endRun) (by omega)

theorem root_refines (ticks q root ctx : Bits) : (finish ticks q root ctx).var.2 =
    (TreeBudgetParentWalkTM2.walkQuery ticks q).any (prefixTest root) := by
  have h := (TreeBudgetParentWalkTM2.arbitrary_refines ticks q ctx).1
  rw [← h]
  cases hf : (TreeBudgetParentWalkTM2.walkEnd ticks q ctx).var.2 <;>
    simp [finish,hf,TreeBudgetParentWalkTM2.read,called,embed,compare_value]

theorem typed_walk {n : ℕ} (P : ParentArray n) (ticks : Bits) (v : Fin n) :
    TreeBudgetParentWalkTM2.walkQuery ticks (TreeBudgetParentWalkTM2.query P v) =
      some (TreeBudgetParentWalkTM2.query P (follow P ticks.length v)) := by
  induction ticks generalizing v with
  | nil => rfl
  | cons b left ih =>
    let xs := TreeBudgetParentWalkTM2.table P
    have hi : v.val < xs.length := by simp [xs,TreeBudgetParentWalkTM2.table]
    let pre := xs.take v.val
    let tail := (xs.drop (v.val+1)).flatMap encodeNat
    have hb : pre.flatMap encodeNat ++ (encodeNat xs[v.val] ++ tail) = TreeBudgetParentWalkTM2.body P := by
      change (xs.take v.val).flatMap encodeNat ++ (encodeNat xs[v.val] ++ _) = _
      rw [← List.flatMap_cons,← List.flatMap_append,List.getElem_cons_drop,List.take_append_drop]; rfl
    have ha : xs[v.val] = (parent P v).val := by simp [xs,TreeBudgetParentWalkTM2.table,parent]
    have he : TreeBudgetParentWalkTM2.query P v = encodeNats pre ++ (encodeNat xs[v.val] ++ tail) := by
      simp only [TreeBudgetParentWalkTM2.query,encodeNats,encodeList,List.append_assoc,hb]
      rw [show pre.length = v.val by simp [pre,Nat.min_eq_left hi.le]]
    have hp : TreeBudgetParentWalkTM2.parts (TreeBudgetParentWalkTM2.query P v) = some (pre,xs[v.val],tail) := by
      rw [he]; simp [TreeBudgetParentWalkTM2.parts,parseNat_append]
    simp only [TreeBudgetParentWalkTM2.walkQuery,hp,Option.bind_some,TreeBudgetParentWalkTM2.nextQuery,follow]
    rw [hb,ha]
    exact ih (parent P v)

theorem endpoint_is_root {n : ℕ} (P : ParentArray n) (ticks ctx : Bits) (v : Fin n) :
    (finish ticks (TreeBudgetParentWalkTM2.query P v) (encodeNat P.root.val) ctx).var.2 =
      decide ((TreeBudgetCostedInput.followCost P ticks.length v).value = P.root) := by
  rw [root_refines,typed_walk,TreeBudgetCostedInput.followCost_value]
  change prefixTest (encodeNat P.root.val) (encodeNat _ ++ _) = _
  rw [at_root_code]
  simp [Fin.ext_iff]

/-- Pointwise connection to the materialized-tree validator. The outer
enumeration of vertices is a separate caller. -/
theorem validate_tests {n : ℕ} (P : ParentArray n) (ctx : Bits) :
    (TreeBudgetCostedInput.validateCost P).value = true ↔
      (finish [true] (TreeBudgetParentWalkTM2.query P P.root) (encodeNat P.root.val) ctx).var.2 = true ∧
      ∀ v, (finish (List.replicate n true) (TreeBudgetParentWalkTM2.query P v)
        (encodeNat P.root.val) ctx).var.2 = true := by
  simp only [endpoint_is_root,TreeBudgetCostedInput.validateCost_value,validateB_eq_true,
    TreeBudgetCostedInput.followCost_value,List.length_replicate,List.length_cons,List.length_nil,
    decide_eq_true_eq,Valid]
  rfl

end UAVProof.TreeBudgetWalkRootTM2
