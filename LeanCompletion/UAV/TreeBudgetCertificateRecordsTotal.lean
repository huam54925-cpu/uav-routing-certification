import LeanCompletion.UAV.TreeBudgetCertificateRecordsGuard
import LeanCompletion.UAV.TreeBudgetCertificateRecordsLoop

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

def initial (n k : ℕ) (body ctx : Bits) : Data :=
  {body := body, count := List.replicate k true, ctx := ctx, dim := n.bits}

theorem prepared_guard (n k : ℕ) (body ctx : Bits) :
    Guard.lift n.bits (TreeBudgetListGuardTM2.atLabel 9 body [] [] []
      (List.replicate k true) ctx) = cfg (.guardCall 9) (initial n k body ctx) := by
  unfold Guard.lift embed TreeBudgetListGuardTM2.atLabel cfg
  congr 1
  funext p
  rcases p with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

def prepare_run (n k : ℕ) (body ctx : Bits) :
    Run (Guard.lift n.bits (TreeBudgetListGuardTM2.atLabel 9 body [] [] []
        (List.replicate k true) ctx))
      (cfg .tick (work (initial n k body ctx) k body)) (2*body.length+2*k+5) := by
  rw [prepared_guard]
  let d := initial n k body ctx
  have a : Run (cfg (.guardCall 9) d) (cfg (.job .saveBody .reverse) d) 1 := once (by rfl)
  have b := copy_job .saveBody d rfl
  have c := copy_job .copyTokens (copied .saveBody d) rfl
  have allRun := seq (seq a b) c
  exact weaken (by simpa [d,initial,copied,replace,source,dest,next,work] using allRun) (by omega)

def guard_failure (dim : Bits) (c : TreeBudgetListGuardTM2.Cfg) (hl : c.l = some 10) :
    Run (Guard.lift dim c) {Guard.lift dim c with l := none, var := (none,false)} 1 := by
  apply once
  simp [machine,FinTM2.step,TM2.step,Guard.lift,embed,hl,program,reject,TM2.stepAux]
  rfl

theorem guard_result (s ctx : Bits) :
    (TreeBudgetListGuardTM2.reference s = none ∧
      (TreeBudgetListGuardTM2.outcome s ctx).l = some 10 ∧
      (TreeBudgetListGuardTM2.outcome s ctx).stk 5 = ctx) ∨
    ∃ k r, parseNat s = some (k,r) ∧ k ≤ r.length ∧
      TreeBudgetListGuardTM2.outcome s ctx = TreeBudgetListGuardTM2.atLabel 9 r [] [] []
        (List.replicate k true) ctx := by
  cases hp : parseNat s with
  | none =>
    have h := TreeBudgetListGuardTM2.header_invalid s ctx hp
    left
    exact ⟨by simp [TreeBudgetListGuardTM2.reference,hp],
      by simpa [TreeBudgetListGuardTM2.outcome,hp] using h.1,
      by simpa [TreeBudgetListGuardTM2.outcome,hp] using h.2⟩
  | some pair =>
    obtain ⟨k,r⟩ := pair
    have h := TreeBudgetListGuardTM2.guard_contract r k.bits [] ctx
    by_cases hg : k ≤ r.length
    · right
      exact ⟨k,r,rfl,hg,by simpa [TreeBudgetListGuardTM2.outcome,hp,hg] using h⟩
    · left
      simp [hg] at h
      exact ⟨by simp [TreeBudgetListGuardTM2.reference,hp,hg],
        by simpa [TreeBudgetListGuardTM2.outcome,hp] using h.1,
        by simpa [TreeBudgetListGuardTM2.outcome,hp] using h.2⟩

/-- General bounded execution of the supplied candidate, including every
rejecting input. This proves the proposition, rather than merely defining it. -/
theorem records_polynomial : RecordsPolynomialSpec := by
  intro n y ctx
  have pre := Guard.precheck_run n.bits y ctx
  unfold Guard.GRun at pre
  rw [← Guard.start_eq] at pre
  rcases guard_result y ctx with bad | ⟨k,r,hp,hk,he⟩
  · obtain ⟨href,hl,hctx⟩ := bad
    let out : Cfg := {Guard.lift n.bits (TreeBudgetListGuardTM2.outcome y ctx)
      with l := none, var := (none,false)}
    have run := seq pre (guard_failure n.bits (TreeBudgetListGuardTM2.outcome y ctx) hl)
    refine ⟨out, ⟨weaken run ?_⟩, rfl, ?_, ?_, rfl, ?_⟩
    · simp only [recordBound]
      have pos := Nat.mul_le_mul (show 1 ≤ y.length+1 by omega)
        (show 1 ≤ y.length+n.bits.length+1 by omega)
      have nonneg := Nat.zero_le (24*y.length*(y.length+1)^2)
      nlinarith only [pos,nonneg]
    · rw [← packet_isSome]
      simp [out,packet,href]
    · exact hctx
    · intro xs h
      simp [packet,href] at h
  · rw [he] at pre
    have len := congrArg List.length (parseNat_canonical y r k hp)
    simp only [List.length_append] at len
    have hr : r.length ≤ y.length := by omega
    have hkW : k ≤ y.length := hk.trans hr
    let d := initial n k r ctx
    have prep := prepare_run n k r ctx
    obtain ⟨out,⟨loop⟩,hl,hv,hkeep,hcursor⟩ := loop_polynomial d n y.length k r rfl hr
    have run := seq (seq pre prep) loop
    refine ⟨out, ⟨weaken run ?_⟩, hl, ?_, hkeep.2.2.1, hkeep.2.2.2, ?_⟩
    · simp only [recordBound]
      have a := Nat.mul_le_mul_right ((y.length+1)^2)
        (Nat.mul_le_mul_left 24 hkW)
      have b := Nat.mul_le_mul_right (y.length+n.bits.length+1)
        (show 32*(r.length+1) ≤ 32*(y.length+1) by omega)
      have c := Nat.mul_le_mul_left (32*(y.length+1))
        (show 1 ≤ y.length+n.bits.length+1 by omega)
      have spare : 2*r.length+2*k+5 ≤ 32*(y.length+1)*(y.length+n.bits.length+1) := by omega
      nlinarith only [a,b,spare]
    · rw [← packet_isSome]
      cases h : sizedEntries n k r with
      | none => simpa [packet,TreeBudgetListGuardTM2.reference,hp,hk,tailFlag,h] using hv
      | some pair =>
        obtain ⟨xs,t⟩ := pair
        cases t <;> simpa [packet,TreeBudgetListGuardTM2.reference,hp,hk,tailFlag,h] using hv
    · intro xs h
      obtain ⟨hy,hs⟩ := (packet_iff n y xs).mp h
      have hp' : parseNat y = some (xs.length,xs.flatMap encodeEntry) := by
        rw [hy]
        exact parseNat_append _ _
      have eq := Option.some.inj (hp.symm.trans hp')
      have hk' : k=xs.length := congrArg Prod.fst eq
      have hr' : r=xs.flatMap encodeEntry := congrArg Prod.snd eq
      refine ⟨hkeep.2.1.trans (congrArg (fun k => List.replicate k true) hk'),
        hkeep.1.trans hr', hcursor xs [] ?_⟩
      rw [hk',hr']
      simpa only [List.append_nil] using sizedEntries_append n xs hs []

end UAVProof.A4CertRecords
