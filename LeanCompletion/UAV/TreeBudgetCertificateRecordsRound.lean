import LeanCompletion.UAV.TreeBudgetCertificateRecordsCalls
import LeanCompletion.UAV.TreeBudgetCertificateRecordsRow

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2
open Turing StateTransition

def cleaned (d : Data) (tail : Bits) : Data :=
  {d with
    input := tail
    row := []
    mult := []
    amount := []
    dimCopy := []
    scratch := []}

theorem entry_size_bounds (e : RawEntry) :
    (e.2.flatMap encodeNat).length ≤ (encodeEntry e).length ∧
    e.1.bits.length ≤ (encodeEntry e).length ∧ e.2.length ≤ (encodeEntry e).length := by
  have h := length_le_flatMap encodeNat encodeNat_nonempty e.2
  simp only [encodeEntry, encodeNats, encodeList, List.length_append,
    encodeNat_length, Nat.size_eq_bits_len]
  omega

def row_check_run (d : Data) (n W : ℕ) (e : RawEntry) (tail : Bits)
    (hd : d.dim = n.bits) (ht : d.scratch = []) (ha : d.amount = [])
    (hc : d.dimCopy = []) (hlen : e.2.length ≤ W) :
    Run (cfg (.job .clearMult .clear) (afterEntry d e tail))
      (equalEnd (cleaned d tail) e.2.length.bits n.bits)
      (16*(encodeEntry e).length*(W+n.bits.length+1)) := by
  let d₁ := {afterEntry d e tail with mult := []}
  let d₂ := {d₁ with row := [], amount := e.2.length.bits}
  have a := clear_mult (afterEntry d e tail)
  have b : Run (cfg .row d₁) (cfg (.job .copyDim .reverse) d₂)
      ((e.2.flatMap encodeNat).length*(2*W+4)+1) := by
    simpa [d₁,d₂,afterEntry,ha] using row_fields d₁ 0 W e.2 ht (by simpa using hlen)
  have c : Run (cfg (.job .copyDim .reverse) d₂)
      (cfg .equalSize {cleaned d tail with amount := e.2.length.bits, dimCopy := n.bits})
      (2*n.bits.length+2) := by
    simpa [d₂,d₁,afterEntry,cleaned,copied,replace,source,dest,ht,ha,hc,hd]
      using copy_job .copyDim d₂ ht
  have z := equal_run (cleaned d tail) e.2.length.bits n.bits
  apply weaken (seq (seq (seq a b) c) z)
  obtain ⟨hb,hm,_⟩ := entry_size_bounds e
  have hpos := encodeEntry_nonempty e
  have hi : e.2.length.bits.length ≤ W := by
    simp only [Nat.size_eq_bits_len]
    exact (TreeBudgetCostedCodec.nat_size_le e.2.length).trans hlen
  have hb' := Nat.mul_le_mul_right (2*W+4) hb
  have hd' := Nat.mul_le_mul_right n.bits.length hpos
  have hw' := Nat.mul_le_mul_right W hpos
  change e.1.bits.length+1 + ((e.2.flatMap encodeNat).length*(2*W+4)+1) +
    (2*n.bits.length+2) + (e.2.length.bits.length+n.bits.length+1) ≤ _
  nlinarith only [hm,hi,hpos,hb',hd',hw']

theorem tick_cons (d : Data) (k : ℕ) (s : Bits) :
    machine.step (cfg .tick (work d (k+1) s)) =
      some (cfg (.entryCall (TreeBudgetEntryTM2.labels .marker)) (work d k s)) := by
  simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,jump,
    TreeBudgetStackRoutine.jump,store,work,List.replicate_succ]
  congr 2
  funext p
  rcases p with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

/-- One parsed record, charged to its consumed bits, including a wrong row size. -/
def round_run (d : Data) (n W k : ℕ) (s tail : Bits) (e : RawEntry)
    (hd : d.dim = n.bits) (hs : s.length ≤ W) (hp : parseEntry s = some (e,tail)) :
    Run (cfg .tick (work d (k+1) s))
      (equalEnd (work d k tail) e.2.length.bits n.bits)
      (24*(W+1)^2 + 32*(encodeEntry e).length*(W+n.bits.length+1)) := by
  have len := congrArg List.length (parseEntry_canonical s tail e hp)
  simp only [List.length_append] at len
  have he := entry_size_bounds e
  have a := once (tick_cons d k s)
  have b := entry_success (work d k s) s tail e hp
  have c := row_check_run (work d k s) n W e tail hd rfl rfl rfl (by omega)
  have all := seq (seq a b) c
  apply weaken (by simpa only [work,cleaned] using all)
  have sq : (s.length+1)^2 ≤ (W+1)^2 := by gcongr
  have pos := encodeEntry_nonempty e
  have charge : 1 ≤ (encodeEntry e).length*(W+n.bits.length+1) :=
    Nat.mul_le_mul pos (show 1 ≤ W+n.bits.length+1 by omega)
  nlinarith only [sq,charge]

end UAVProof.A4CertRecords
