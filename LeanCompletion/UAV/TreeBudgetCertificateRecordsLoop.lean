import LeanCompletion.UAV.TreeBudgetCertificateRecordsRound

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2
open Turing StateTransition

def tailFlag (n k : ℕ) (s : Bits) : Bool :=
  (sizedEntries n k s).any (fun p => p.2.isEmpty)

def finish_run (d : Data) (s : Bits) :
    Run (cfg .tick (work d 0 s)) (stop (work d 0 s) s.isEmpty) 2 := by
  have h : machine.step (cfg .tick (work d 0 s)) = some (cfg .eof (work d 0 s)) := by
    simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,jump,
      TreeBudgetStackRoutine.jump,store,work]
    congr 2
    funext p
    rcases p with (i | (i | u)) | a
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · cases u; rfl
    · cases a <;> rfl
  exact seq (once h) (once (by cases s <;> rfl))

/-- All record counts, all input strings, and all three rejection paths.
The overhead is charged to disjoint consumed input segments. -/
theorem loop_polynomial (d : Data) (n W k : ℕ) (s : Bits)
    (hd : d.dim = n.bits) (hs : s.length ≤ W) :
    ∃ out, Nonempty (Run (cfg .tick (work d k s)) out
      (24*k*(W+1)^2 + 32*(s.length+1)*(W+n.bits.length+1))) ∧
      out.l = none ∧ out.var.2 = tailFlag n k s ∧ Kept d out ∧
      (∀ xs tail, sizedEntries n k s = some (xs,tail) → out.stk cursor = tail) := by
  induction k generalizing s with
  | zero =>
    refine ⟨stop (work d 0 s) s.isEmpty,
      ⟨weaken (finish_run d s) (by nlinarith)⟩, rfl, ?_, ⟨rfl,rfl,rfl,rfl⟩, ?_⟩
    · simp [stop,tailFlag,sizedEntries]
    · intro xs tail h
      simp only [sizedEntries,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
  | succ k ih =>
    cases hp : parseEntry s with
    | none =>
      obtain ⟨out,⟨run⟩,hl,hv,hkeep⟩ := entry_failure (work d k s) s hp
      have allRun := seq (once (tick_cons d k s)) run
      have sq : (s.length+1)^2 ≤ (W+1)^2 := by gcongr
      have bk : 24*(W+1)^2 ≤ 24*(k+1)*(W+1)^2 :=
        Nat.mul_le_mul_right _ (by omega)
      refine ⟨out, ⟨weaken allRun (by nlinarith only [sq,bk])⟩, hl, ?_, hkeep, ?_⟩
      · simp [hv,tailFlag,sizedEntries,hp]
      · intro xs tail h; simp [sizedEntries,hp] at h
    | some pair =>
      obtain ⟨e,t⟩ := pair
      have len := congrArg List.length (parseEntry_canonical s t e hp)
      simp only [List.length_append] at len
      have run := round_run d n W k s t e hd hs hp
      by_cases hr : e.2.length = n
      · rw [hr,equalEnd_same] at run
        obtain ⟨out,⟨rest⟩,hl,hv,hkeep,hcursor⟩ := ih t (by omega)
        have allRun := seq run rest
        refine ⟨out, ⟨weaken allRun ?_⟩, hl, ?_, hkeep, ?_⟩
        · rw [len]
          nlinarith only []
        · cases he : sizedEntries n k t <;>
            simpa [tailFlag,sizedEntries,hp,hr,he] using hv
        · intro xs tail h
          cases he : sizedEntries n k t with
          | none => simp [sizedEntries,hp,hr,he] at h
          | some pair =>
            obtain ⟨ys,u⟩ := pair
            have eq : (e::ys,u)=(xs,tail) := by
              simpa [sizedEntries,hp,hr,he] using h
            cases eq
            exact hcursor ys _ he
      · have neq : e.2.length.bits ≠ n.bits := fun h => hr ((bits_eq _ _).mp h)
        obtain ⟨hl,hv⟩ := equalEnd_different (work d k t) _ _ neq
        have bk : 24*(W+1)^2 ≤ 24*(k+1)*(W+1)^2 :=
          Nat.mul_le_mul_right _ (by omega)
        have bc := Nat.mul_le_mul_right (32*(W+n.bits.length+1))
          (show (encodeEntry e).length ≤ s.length+1 by omega)
        refine ⟨_, ⟨weaken run (by nlinarith only [bk,bc])⟩, hl, ?_,
          equalEnd_kept (work d k t) _ _, ?_⟩
        · simp [hv,tailFlag,sizedEntries,hp,hr]
        · intro xs tail h; simp [sizedEntries,hp,hr] at h

end UAVProof.A4CertRecords
