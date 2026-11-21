import LeanCompletion.UAV.TreeBudgetSparseCodec
import LeanCompletion.UAV.TreeBudgetCountHeaderTM2

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec

/-- Decode exactly k entries and check each row's dimension as it is read. -/
def sizedEntries (n : ℕ) : ℕ → Parser RawCertificate
  | 0, s => some ([],s)
  | k+1, s => do
      let (e,t) ← parseEntry s
      if e.2.length = n then
        let (es,u) ← sizedEntries n k t
        some (e::es,u)
      else none

theorem sizedEntries_append (n : ℕ) (es : RawCertificate) (hs : Sized n es) (t : Bits) :
    sizedEntries n es.length (es.flatMap encodeEntry ++ t) = some (es,t) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    have he := hs e (by simp)
    have ht : Sized n es := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    have hrec : sizedEntries n es.length (es.flatMap encodeEntry ++ t) = some (es,t) := by
      apply ih
      exact ht
    simp [sizedEntries,List.append_assoc,parseEntry_append,he,hrec]

theorem sizedEntries_sound (n k : ℕ) (s t : Bits) (es : RawCertificate)
    (h : sizedEntries n k s = some (es,t)) :
    es.length = k ∧ Sized n es ∧ s = es.flatMap encodeEntry ++ t := by
  induction k generalizing s es t with
  | zero =>
    simp only [sizedEntries,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨he,ht⟩
    subst es
    subst t
    simp [Sized]
  | succ k ih =>
    cases hp : parseEntry s with
    | none => simp [sizedEntries,hp] at h
    | some p =>
      obtain ⟨e,u⟩ := p
      by_cases hd : e.2.length = n
      · cases hq : sizedEntries n k u with
        | none => simp [sizedEntries,hp,hd,hq] at h
        | some q =>
          obtain ⟨xs,v⟩ := q
          have heq : some (e::xs,v) = some (es,t) := by simpa [sizedEntries,hp,hd,hq] using h
          have hh := Option.some.inj heq
          have hxs : es = e::xs := (congrArg Prod.fst hh).symm
          have htail : t = v := (congrArg Prod.snd hh).symm
          subst es
          subst t
          obtain ⟨hlen,hs,hu⟩ := ih (s := u) (t := v) (es := xs) hq
          refine ⟨by simp [hlen], ?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with ha | ha
            · subst a
              exact hd
            · exact hs a ha
          · rw [parseEntry_canonical s u e hp,hu]
            simp [List.append_assoc]
      · simp [sizedEntries,hp,hd] at h

def packet (n : ℕ) (y : Bits) : Option RawCertificate := do
  let (k,r) ← TreeBudgetListGuardTM2.reference y
  let (xs,u) ← sizedEntries n k r
  if u = [] then some xs else none

theorem packet_encode (n : ℕ) (xs : RawCertificate) (hs : Sized n xs) :
    packet n (encodeRaw xs) = some xs := by
  have hguard := length_le_flatMap encodeEntry encodeEntry_nonempty xs
  have hbody := sizedEntries_append n xs hs []
  rw [List.append_nil] at hbody
  simp only [List.length_flatMap] at hguard
  simp [packet, TreeBudgetListGuardTM2.reference, encodeRaw, encodeList,
    parseNat_append, hguard, hbody]

theorem packet_iff (n : ℕ) (y : Bits) (xs : RawCertificate) :
    packet n y = some xs ↔ y = encodeRaw xs ∧ Sized n xs := by
  constructor
  · intro h
    cases hn : parseNat y with
    | none => simp [packet,TreeBudgetListGuardTM2.reference,hn] at h
    | some p =>
      obtain ⟨k,r⟩ := p
      by_cases hg : k ≤ r.length
      · cases hs : sizedEntries n k r with
        | none => simp [packet,TreeBudgetListGuardTM2.reference,hn,hg,hs] at h
        | some q =>
          obtain ⟨us,t⟩ := q
          by_cases ht : t = []
          · subst t
            have he : us = xs := by
              simpa [packet,TreeBudgetListGuardTM2.reference,hn,hg,hs] using h
            subst xs
            obtain ⟨hlen,hd,hr⟩ := sizedEntries_sound n k r [] us hs
            refine ⟨?_,hd⟩
            rw [parseNat_canonical y r k hn,hr]
            simp [encodeRaw,encodeList,hlen]
          · simp [packet,TreeBudgetListGuardTM2.reference,hn,hg,hs,ht] at h
      · simp [packet,TreeBudgetListGuardTM2.reference,hn,hg] at h
  · rintro ⟨rfl,hs⟩
    exact packet_encode n xs hs

theorem packet_isSome (n : ℕ) (y : Bits) :
    (packet n y).isSome = (decodeCertificate n y).isSome := by
  cases hp : packet n y with
  | some xs =>
    obtain ⟨hy,hs⟩ := (packet_iff n y xs).mp hp
    have he : encodeCert (ofRaw n xs hs) = encodeRaw xs := by simp [encodeCert]
    simp only [hy, ← he, decodeCertificate_encode, Option.isSome_some]
  | none =>
    cases hc : decodeCertificate n y with
    | none => rfl
    | some C =>
      have hy := decodeCertificate_canonical y C hc
      have hp' := (packet_iff n y (toRaw C)).mpr ⟨hy,toRaw_sized C⟩
      rw [hp] at hp'
      cases hp'

end UAVProof.A4CertRecords
