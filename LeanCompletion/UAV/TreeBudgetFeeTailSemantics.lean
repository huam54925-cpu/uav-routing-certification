import LeanCompletion.UAV.TreeBudgetFeeTailBudget
import LeanCompletion.UAV.TreeBudgetFeeTailFieldSemantics

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem group_signed_some (n : ℕ) (s w t : Bits)
    (h : groupParse false n s=some (w,t)) :
    ∃ zs : List ℤ, zs.length=n ∧ s=encodeInts zs++t ∧ w=zs.flatMap encodeInt := by
  simp only [groupParse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨u,hu,⟨⟨ws,v⟩,hw,he⟩⟩ := h
  cases he
  obtain ⟨zs,hz,rfl⟩ := manySigned_some n u v ws hw
  have hl := parseMany_length parseInt n u zs v hz
  have hc := parseMany_canonical encodeInt parseInt parseInt_canonical n u v zs hz
  refine ⟨zs,hl,?_,rfl⟩
  rw [(stripHeader_iff _ _ _).mp hu,hc]
  simp [encodeInts,encodeList,hl,List.append_assoc]

theorem group_positive_some (n : ℕ) (s w t : Bits)
    (h : groupParse true n s=some (w,t)) :
    ∃ ds : List ℕ, ds.length=n ∧ s=encodeNats ds++t ∧
      (∀ d∈ds, 0<d) ∧ w=ds.flatMap encodeNat := by
  simp only [groupParse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨u,hu,⟨⟨ws,v⟩,hw,he⟩⟩ := h
  cases he
  obtain ⟨ds,hd,hpos,rfl⟩ := manyPositive_some n u v ws hw
  have hl := parseMany_length parseNat n u ds v hd
  have hc := parseMany_canonical encodeNat parseNat parseNat_canonical n u v ds hd
  refine ⟨ds,hl,?_,by simpa using hpos,rfl⟩
  rw [(stripHeader_iff _ _ _).mp hu,hc]
  simp [encodeNats,encodeList,hl,List.append_assoc]

theorem group_signed_append (zs : List ℤ) (t : Bits) :
    groupParse false zs.length (encodeInts zs++t)=some (zs.flatMap encodeInt,t) := by
  have hh : stripHeader (encodeNat zs.length) (encodeInts zs++t)=some (zs.flatMap encodeInt++t) := by
    apply (stripHeader_iff _ _ _).mpr
    simp [encodeInts,encodeList,List.append_assoc]
  simp only [groupParse,bind,hh,Option.bind_some,groupRead,Bool.false_eq_true,ite_false,
    parseMany_signed,parseMany_append encodeInt parseInt parseInt_append]
  rfl

theorem group_positive_append (ds : List ℕ) (t : Bits) (hp : ∀ d∈ds,0<d) :
    groupParse true ds.length (encodeNats ds++t)=some (ds.flatMap encodeNat,t) := by
  have hh : stripHeader (encodeNat ds.length) (encodeNats ds++t)=some (ds.flatMap encodeNat++t) := by
    apply (stripHeader_iff _ _ _).mpr
    simp [encodeNats,encodeList,List.append_assoc]
  simp only [groupParse,bind,hh,Option.bind_some,groupRead,ite_true,parseMany_positive,
    parseMany_append encodeNat parseNat parseNat_append]
  simp only [List.all_eq_true,decide_eq_true_eq]
  rw [if_pos hp]
  rfl

structure FeeWords where
  nums : Bits
  dens : Bits
  budgetNum : Bits
  budgetDen : Bits
  deriving DecidableEq, Repr

def wireWords (f : A4FeeTailSpec.Fields) : FeeWords :=
  ⟨f.nums.flatMap encodeInt,f.dens.flatMap encodeNat,encodeInt f.budgetNum,encodeNat f.budgetDen⟩

def readFeeWords (n : ℕ) (s : Bits) : Option FeeWords := do
  let (a,t) ← groupParse false n s
  let (d,u) ← groupParse true n t
  let (b,q) ← budgetParse u
  pure ⟨a,d,b,q⟩

theorem budget_some (s b q : Bits) (h : budgetParse s=some (b,q)) :
    ∃ z : ℤ, ∃ d : ℕ, 0<d ∧ s=encodeInt z++encodeNat d ∧ b=encodeInt z ∧ q=encodeNat d := by
  simp only [budgetParse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨bb,t⟩,hb,⟨⟨qq,u⟩,hq,he⟩⟩ := h
  dsimp only at he
  split_ifs at he with hu
  subst u
  cases he
  obtain ⟨z,hz,rfl⟩ := readSigned_some s _ t hb
  obtain ⟨d,hd,hp,rfl⟩ := readPositive_some t _ [] hq
  refine ⟨z,d,hp,?_,rfl,rfl⟩
  rw [parseInt_canonical _ _ _ hz,parseNat_canonical _ _ _ hd,List.append_nil]

theorem budget_append (z : ℤ) (d : ℕ) (hp : 0<d) :
    budgetParse (encodeInt z++encodeNat d)=some (encodeInt z,encodeNat d) := by
  have hq := parseNat_append d []
  simp only [List.append_nil] at hq
  simp [budgetParse,readSigned_int,parseInt_append,readWord_false,hq,hp]

theorem readFeeWords_some (n : ℕ) (s : Bits) (w : FeeWords)
    (h : readFeeWords n s=some w) :
    ∃ f, A4FeeTailSpec.read n s=some f ∧ w=wireWords f := by
  simp only [readFeeWords,bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨aa,t⟩,ha,⟨⟨dd,u⟩,hd,⟨⟨bb,qq⟩,hb,he⟩⟩⟩ := h
  cases he
  obtain ⟨zs,hzn,hs,rfl⟩ := group_signed_some n s aa t ha
  obtain ⟨ds,hdn,ht,hpos,rfl⟩ := group_positive_some n t dd u hd
  obtain ⟨z,d,hp,hu,rfl,rfl⟩ := budget_some u bb qq hb
  let f : A4FeeTailSpec.Fields := ⟨zs,ds,z,d⟩
  refine ⟨f,(A4FeeTailSpec.read_iff _ _ _).mpr ⟨?_,?_⟩,rfl⟩
  · simp only [hs,ht,hu,A4FeeTailSpec.wire,f,List.append_assoc]
  · exact (A4FeeTailSpec.good_iff _ _).mpr ⟨hzn,hdn,hp,hpos⟩

theorem readFeeWords_wire (n : ℕ) (f : A4FeeTailSpec.Fields) (hg : A4FeeTailSpec.good n f=true) :
    readFeeWords n (A4FeeTailSpec.wire f)=some (wireWords f) := by
  obtain ⟨hn,hd,hq,hpos⟩ := (A4FeeTailSpec.good_iff _ _).mp hg
  have h₁ := group_signed_append f.nums (encodeNats f.dens++encodeInt f.budgetNum++encodeNat f.budgetDen)
  rw [hn] at h₁
  have h₂ := group_positive_append f.dens (encodeInt f.budgetNum++encodeNat f.budgetDen) hpos
  rw [hd] at h₂
  simp only [List.append_assoc] at h₁ h₂
  simp [readFeeWords,A4FeeTailSpec.wire,List.append_assoc,h₁,h₂,budget_append _ _ hq,wireWords]

theorem readFeeWords_eq (n : ℕ) (s : Bits) :
    readFeeWords n s=(A4FeeTailSpec.read n s).map wireWords := by
  cases hr : A4FeeTailSpec.read n s with
  | none =>
    cases hw : readFeeWords n s with
    | none => rfl
    | some w =>
      obtain ⟨f,hf,_⟩ := readFeeWords_some n s w hw
      rw [hr] at hf
      cases hf
  | some f =>
    obtain ⟨rfl,hg⟩ := (A4FeeTailSpec.read_iff _ _ _).mp hr
    simpa using readFeeWords_wire n f hg

end UAVProof.A4FeeTailMachine
