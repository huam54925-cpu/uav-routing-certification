import LeanCompletion.UAV.TreeBudgetCertificateRecordsData

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

def afterEntry (d : Data) (e : RawEntry) (tail : Bits) : Data :=
  {d with input := tail, row := e.2.flatMap encodeNat, mult := e.1.bits}

theorem entry_input (d : Data) (s : Bits) :
    embed ew L.entryCall .returned (store d) (TreeBudgetEntryTM2.start s []) =
      cfg (.entryCall (TreeBudgetEntryTM2.labels .marker))
        {d with input := s, row := [], mult := []} := by
  unfold embed TreeBudgetEntryTM2.start TreeBudgetFrameRoutineTM2.cfg cfg
  congr 1
  funext k
  rcases k with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

theorem entry_return (d : Data) (e : RawEntry) (tail : Bits) :
    embed ew L.entryCall .returned (store d) (TreeBudgetEntryTM2.returned e tail []) =
      cfg .returned (afterEntry d e tail) := by
  unfold embed TreeBudgetEntryTM2.returned cfg
  congr 1
  funext k
  rcases k with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

def entry_success (d : Data) (s tail : Bits) (e : RawEntry)
    (hp : parseEntry s = some (e,tail)) :
    Run (cfg (.entryCall (TreeBudgetEntryTM2.labels .marker))
        {d with input := s, row := [], mult := []})
      (cfg (.job .clearMult .clear) (afterEntry d e tail)) (24*(s.length+1)^2+1) := by
  have h := call_run ew L.entryCall .returned (store d) TreeBudgetEntryTM2.program
    program (fun _ => rfl) (TreeBudgetEntryTM2.entry_success_run s [] e tail hp)
  rw [entry_input, entry_return] at h
  exact seq h (once (by rfl))

theorem entry_failure (d : Data) (s : Bits) (hp : parseEntry s = none) :
    ∃ out, Nonempty (Run (cfg (.entryCall (TreeBudgetEntryTM2.labels .marker))
        {d with input := s, row := [], mult := []}) out (24*(s.length+1)^2+1)) ∧
      out.l = none ∧ out.var.2 = false ∧ Kept d out := by
  have h := call_run ew L.entryCall .returned (store d) TreeBudgetEntryTM2.program
    program (fun _ => rfl) (TreeBudgetEntryTM2.entry_run s [])
  rw [entry_input] at h
  let c := embed ew L.entryCall .returned (store d) (TreeBudgetEntryTM2.stopped s [])
  let out : Cfg := {c with l := none, var := (none,false)}
  have flag : (TreeBudgetEntryTM2.stopped s []).var.2 = false := by
    simpa only [hp, Option.isSome_none] using TreeBudgetEntryTM2.stopped_flag s []
  have last : machine.step c = some out := by
    simp [c, out, machine, FinTM2.step, TM2.step, embed, TreeBudgetEntryTM2.stopped_halted,
      program, TM2.stepAux, flag, reject]
  exact ⟨out, ⟨seq h (once last)⟩, rfl, rfl, ⟨rfl,rfl,rfl,rfl⟩⟩

end UAVProof.A4CertRecords
