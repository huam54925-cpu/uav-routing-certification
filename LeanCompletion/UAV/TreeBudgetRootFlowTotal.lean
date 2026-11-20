import LeanCompletion.UAV.TreeBudgetRootFlowRuns

namespace UAVProof.TreeBudgetRootFlowTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

/-- Earlier parsed fields and caller context remain available, even on rejection. -/
def SavedPrefix (s ctx : Bits) (out : Cfg) : Prop := out.stk context=ctx ∧
  ∀ a, TreeBudgetParentPrefix.parse s=some a → ∀ k,
    out.stk (.inl (.inr k))=TreeBudgetParentPrefixTM2.savedPrefix a ctx k

/-- H and the exact next-field suffix survive both acceptance and root-flow rejection. -/
def SavedH (s : Bits) (out : Cfg) : Prop := ∀ a hs t,
  TreeBudgetParentPrefix.accepted s=true → TreeBudgetParentPrefix.parse s=some a →
  parseNats a.rest=some (hs,t) → out.stk suffix=t ∧ out.stk demands=hs.flatMap encodeNat

theorem root_flow_polynomial (s ctx : Bits) :
    ∃ out, Nonempty (Run (start s ctx) out (32768*(s.length+1)^4)) ∧ out.l=none ∧
      out.var.2=TreeBudgetRootFlowSpec.accepted s ∧ SavedPrefix s ctx out ∧ SavedH s out := by
  obtain ⟨p,⟨pre⟩,pl,pv,pk⟩ := TreeBudgetParentPrefixTM2.prefix_polynomial s ctx
  have call := call_run prefixW L.prefix (.control .prefixed) (fun _ => [])
    TreeBudgetParentPrefixTM2.program program (fun _ => rfl) pre
  have hp₁ : s.length+1≤(s.length+1)^2 := by nlinarith
  have hp₂ : (s.length+1)^2≤(s.length+1)^4 := by nlinarith
  by_cases good : TreeBudgetParentPrefix.accepted s=true
  · have pe : p.var.2=true := pv.trans good
    obtain ⟨a,pa⟩ : ∃ a, TreeBudgetParentPrefix.parse s=some a := by
      cases he : TreeBudgetParentPrefix.parse s with
      | none => simp [TreeBudgetParentPrefix.accepted,he] at good
      | some a => exact ⟨a,rfl⟩
    obtain ⟨pm,pn,pr,pb,pt,pc⟩ := TreeBudgetParentPrefixTM2.saved_fields a ctx p (pk.2 a pa)
    have canonical := TreeBudgetParentPrefix.canonical s a pa
    obtain ⟨bpR,bm,bn,br,bp,bt⟩ := TreeBudgetParentPrefix.occupied a
    rw [← canonical] at bpR bm bn br bp bt
    have bodyBound : (TreeBudgetParentPrefix.body a).length ≤ s.length := by omega
    have listBound : (a.rest.length+1)^2≤(s.length+1)^2 := by gcongr
    have inputCopy := copy_job .input {p:=p.stk} rfl
    simp only [next] at inputCopy
    rw [list_input p.stk a.rest pt] at inputCopy
    have listRun := call_run listW L.list (.control .listed) (store {p:=p.stk})
      TreeBudgetListGuardTM2.program program (fun _ => rfl) (TreeBudgetCountedNatsTM2.list_halts a.rest [])
    have throughList := seq (seq (seq call (once (prefix_continue p pl pe))) inputCopy) listRun
    have layout := TreeBudgetIndexedZeroTM2.layout a.rest []
    cases ph : parseNats a.rest with
    | none =>
      simp only [ph] at layout
      let out : Cfg := {embed listW L.list (.control .listed) (store {p:=p.stk})
        (TreeBudgetCountedNatsTM2.stopped a.rest []) with l:=none}
      have last : machine.step (embed listW L.list (.control .listed) (store {p:=p.stk})
          (TreeBudgetCountedNatsTM2.stopped a.rest []))=some out := by
        simp [machine,FinTM2.step,TM2.step,embed,list_halted,program,TM2.stepAux,layout,out]
      refine ⟨out,⟨weaken (seq throughList (once last)) ?_⟩,rfl,?_,?_,?_⟩
      · simp only [source,pt]
        nlinarith only [bt,listBound,hp₁,hp₂]
      · simp [out,embed,layout,TreeBudgetRootFlowSpec.accepted,TreeBudgetRootFlowSpec.suffixOK,pa,ph]
      · exact ⟨pk.1,fun b hb k => pk.2 b hb k⟩
      · intro b hs t hg hb hh
        have ab : b=a := by simpa [pa] using hb.symm
        subst b
        simp [ph] at hh
    | some pair =>
      obtain ⟨hs,t⟩ := pair
      simp only [ph] at layout
      have hcode := parseList_canonical encodeNat parseNat parseNat_canonical a.rest t hs ph
      have bh : (hs.flatMap encodeNat).length ≤ s.length := by
        have small : (hs.flatMap encodeNat).length≤a.rest.length := by
          rw [hcode]
          simp only [encodeNats,encodeList,List.length_append]
          omega
        omega
      have prepare := prepare_run a hs p.stk (TreeBudgetCountedNatsTM2.stopped a.rest []).stk pb pr pm layout.2.2
      obtain ⟨out,⟨scan⟩,hl,hv,hp,ht⟩ := scan_call a hs p.stk
        (TreeBudgetCountedNatsTM2.stopped a.rest []).stk s.length bodyBound bh br bm bp
      have allRun := seq (seq (seq throughList (once (list_continue p.stk a.rest layout.1))) prepare) scan
      refine ⟨out,⟨weaken allRun ?_⟩,hl,?_,?_,?_⟩
      · simp only [source,pt]
        nlinarith only [bodyBound,bh,br,bm,bt,listBound,hp₁,hp₂]
      · simpa [TreeBudgetRootFlowSpec.accepted,TreeBudgetRootFlowSpec.suffixOK,good,pa,ph] using hv
      · exact ⟨(hp _).trans pk.1,fun b hb k => (hp _).trans (pk.2 b hb k)⟩
      · intro b ns tail hg hb hh
        have ab : b=a := by simpa [pa] using hb.symm
        subst b
        have eq : (ns,tail)=(hs,t) := by simpa [ph] using hh.symm
        cases eq
        exact ⟨(ht _).trans layout.2.1,(ht _).trans layout.2.2⟩
  · have bad : TreeBudgetParentPrefix.accepted s=false := Bool.eq_false_iff.mpr good
    have pe : p.var.2=false := pv.trans bad
    let out : Cfg := {embed prefixW L.prefix (.control .prefixed) (fun _ => []) p with l:=none}
    have last : machine.step (embed prefixW L.prefix (.control .prefixed) (fun _ => []) p)=some out := by
      simp [machine,FinTM2.step,TM2.step,embed,pl,program,TM2.stepAux,pe,out]
    refine ⟨out,⟨weaken (seq call (once last)) (by nlinarith only [hp₁,hp₂])⟩,rfl,?_,?_,?_⟩
    · simp [out,embed,pe,TreeBudgetRootFlowSpec.accepted,bad]
    · exact ⟨pk.1,fun a ha k => pk.2 a ha k⟩
    · intro a hs t hg; simp [bad] at hg

theorem saved_fields (s ctx : Bits) (out : Cfg) (hp : SavedPrefix s ctx out) (hh : SavedH s out)
    (a : TreeBudgetRootFlowSpec.Raw) (ha : TreeBudgetRootFlowSpec.parse s=some a)
    (hok : TreeBudgetParentPrefix.accepted s=true) :
    out.stk (.inl (.inr (.inr 0)))=a.routes.bits ∧
    out.stk (.inl TreeBudgetParentPrefixTM2.dimension)=a.vertices.bits ∧
    out.stk (.inl TreeBudgetParentPrefixTM2.parsedRoot)=a.root.bits ∧
    out.stk (.inl TreeBudgetParentPrefixTM2.parsedBody)=a.parents.flatMap encodeNat ∧
    out.stk demands=a.demands.flatMap encodeNat ∧ out.stk suffix=a.rest ∧ out.stk context=ctx := by
  have he := TreeBudgetRootFlowSpec.canonical s a ha
  subst s
  have pp := hp.2 (TreeBudgetRootFlowSpec.front a) (TreeBudgetParentPrefix.parse_encode _)
  have hl := hh (TreeBudgetRootFlowSpec.front a) a.demands a.rest hok
    (TreeBudgetParentPrefix.parse_encode _) (by simp [TreeBudgetRootFlowSpec.front])
  exact ⟨pp _,pp _,pp _,pp _,hl.2,hl.1,hp.1⟩

theorem init_eq (s : Bits) : initList machine s=start s [] := by
  rw [start,← TreeBudgetParentPrefixTM2.init_eq]
  simp only [initList,machine,embed]
  congr 1
  funext k
  rcases k with k | k | k
  · rcases k with ((((i | b) | u) | v) | z) | w
    · fin_cases i <;> rfl
    · cases b <;> rfl
    · cases u; rfl
    · cases v; rfl
    · fin_cases z <;> rfl
    · rcases w with (i | u) | z
      · fin_cases i <;> rfl
      · cases u; rfl
      · fin_cases z <;> rfl
  · rfl
  · rfl

theorem root_flow_from_init (s : Bits) :
    ∃ out, Nonempty (EvalsToInTime machine.step (initList machine s) (some out)
      (32768*(s.length+1)^4)) ∧ out.l=none ∧ out.var.2=TreeBudgetRootFlowSpec.accepted s ∧
      SavedPrefix s [] out ∧ SavedH s out := by
  rw [init_eq]
  exact root_flow_polynomial s []

def inputFields (m : ℕ) (raw : RawInput) (tail : Bits) : TreeBudgetRootFlowSpec.Raw :=
  ⟨m,raw.n,raw.root,raw.parents,raw.multiplicities,
    encodeInts raw.numerators ++ (encodeNats raw.denominators ++
      (encodeInt raw.budgetNumerator ++ (encodeNat raw.budgetDenominator ++ tail)))⟩

/-- The new prefix is the prefix of the repository's actual instance encoding. -/
theorem inputFields_encoding (m : ℕ) (raw : RawInput) (tail : Bits) :
    TreeBudgetRootFlowSpec.encode (inputFields m raw tail)=
      TreeBudgetSparseVerifier.encodeSpecified m raw ++ tail := by
  simp [TreeBudgetRootFlowSpec.encode,TreeBudgetRootFlowSpec.front,inputFields,
    TreeBudgetParentPrefix.encode,TreeBudgetSparseVerifier.encodeSpecified,encodeInput,List.append_assoc]

theorem parse_inputFields (m : ℕ) (raw : RawInput) (tail : Bits) :
    TreeBudgetRootFlowSpec.parse (TreeBudgetSparseVerifier.encodeSpecified m raw ++ tail)=
      some (inputFields m raw tail) := by
  rw [← inputFields_encoding,TreeBudgetRootFlowSpec.parse_encode]

end UAVProof.TreeBudgetRootFlowTM2
