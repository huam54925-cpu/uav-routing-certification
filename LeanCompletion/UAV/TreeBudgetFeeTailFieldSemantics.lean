import LeanCompletion.UAV.TreeBudgetFeeTailFields

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec

theorem readSigned_int (s : Bits) : readSigned s=
    (parseInt s).map (fun e => (encodeInt e.1,e.2)) := by
  cases s with
  | nil => rfl
  | cons b s =>
    cases b with
    | false =>
      simp only [readSigned,Bool.not_false,readWord_true]
      cases hp : parseNat s with
      | none => simp [parseInt,hp]
      | some e => obtain ⟨n,t⟩ := e; simp [parseInt,hp,encodeInt]
    | true =>
      simp only [readSigned,Bool.not_true,readWord_false]
      cases hp : parseNat s with
      | none => simp [parseInt,hp]
      | some e =>
        obtain ⟨n,t⟩ := e
        by_cases hn : n=0
        · simp [parseInt,hp,hn]
        · simp [parseInt,hp,hn,encodeInt,Nat.pos_of_ne_zero hn]

def guarded {α : Type} (p : Parser α) (enc : α → Bits) (ok : α → Bool) (s : Bits) : Option (Bits × Bits) :=
  (p s).bind (fun e => if ok e.1 then some (enc e.1,e.2) else none)

theorem parseMany_guarded {α : Type} (p : Parser α) (enc : α → Bits) (ok : α → Bool) (n : ℕ) (s : Bits) :
    parseMany (guarded p enc ok) n s = (parseMany p n s).bind
      (fun e => if e.1.all ok then some (e.1.map enc,e.2) else none) := by
  induction n generalizing s with
  | zero => simp [parseMany]
  | succ n ih =>
    cases hp : p s with
    | none => simp [parseMany,guarded,hp]
    | some e =>
      obtain ⟨x,t⟩ := e
      cases hx : ok x <;> cases ht : parseMany p n t <;>
        simp [parseMany,guarded,hp,hx,ih,ht]
      all_goals split_ifs <;> rfl

theorem parseMany_signed (n : ℕ) (s : Bits) :
    parseMany readSigned n s=(parseMany parseInt n s).map (fun e => (e.1.map encodeInt,e.2)) := by
  have h : readSigned=guarded parseInt encodeInt (fun _ => true) := by
    funext t
    rw [readSigned_int]
    unfold guarded
    cases parseInt t <;> rfl
  rw [h,parseMany_guarded]
  cases parseMany parseInt n s <;> simp

theorem parseMany_positive (n : ℕ) (s : Bits) :
    parseMany (readWord false) n s=(parseMany parseNat n s).bind
      (fun e => if e.1.all (fun d => decide (0<d)) then some (e.1.map encodeNat,e.2) else none) := by
  have h : readWord false=guarded parseNat encodeNat (fun d => decide (0<d)) := by
    funext t
    simp [guarded,readWord_false]
  rw [h,parseMany_guarded]

theorem readSigned_some (s w t : Bits) (h : readSigned s=some (w,t)) :
    ∃ z, parseInt s=some (z,t) ∧ w=encodeInt z := by
  rw [readSigned_int] at h
  obtain ⟨⟨z,u⟩,hz,he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨z,hz,rfl⟩

theorem readPositive_some (s w t : Bits) (h : readWord false s=some (w,t)) :
    ∃ q, parseNat s=some (q,t) ∧ 0<q ∧ w=encodeNat q := by
  rw [readWord_false] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨q,u⟩,hq,he⟩ := h
  dsimp only at he
  split_ifs at he with hp
  cases he
  exact ⟨q,hq,hp,rfl⟩

theorem manySigned_some (n : ℕ) (s t : Bits) (ws : List Bits)
    (h : parseMany readSigned n s=some (ws,t)) :
    ∃ zs, parseMany parseInt n s=some (zs,t) ∧ ws=zs.map encodeInt := by
  rw [parseMany_signed] at h
  obtain ⟨⟨zs,u⟩,hz,he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨zs,hz,rfl⟩

theorem manyPositive_some (n : ℕ) (s t : Bits) (ws : List Bits)
    (h : parseMany (readWord false) n s=some (ws,t)) :
    ∃ ds, parseMany parseNat n s=some (ds,t) ∧
      ds.all (fun d => decide (0<d))=true ∧ ws=ds.map encodeNat := by
  rw [parseMany_positive] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨ds,u⟩,hd,he⟩ := h
  dsimp only at he
  split_ifs at he with hp
  cases he
  exact ⟨ds,hd,hp,rfl⟩

end UAVProof.A4FeeTailMachine
