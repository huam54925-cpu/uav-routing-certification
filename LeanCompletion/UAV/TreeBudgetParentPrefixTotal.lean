import LeanCompletion.UAV.TreeBudgetParentPrefixRanges

namespace UAVProof.TreeBudgetParentPrefixTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray
open Turing StateTransition
open TreeBudgetParentPrefix (Raw)

theorem tree_call (a : Raw) (ctx : Bits) (hr : a.root<a.parents.length)
    (hp : ∀ x∈a.parents,x<a.parents.length) :
    ∃ out, Nonempty (Run (cfg treeEntry (work a 0 []) (savedPrefix a ctx)) out
      (4096*((TreeBudgetParentPrefix.encode a).length+1)^4+1)) ∧ out.l=none ∧
      out.var.2=(decodeParents a.root a.parents).isSome ∧ kept (savedPrefix a ctx) out := by
  let P := TreeBudgetParentPrefix.typed a hr hp
  have hbP : TreeBudgetParentWalkTM2.body P=TreeBudgetParentPrefix.body a := TreeBudgetParentPrefix.typed_body a hr hp
  obtain ⟨out,⟨h⟩,hl,hv,hkeep⟩ := TreeBudgetWholeTreeTM2.whole_tree_polynomial P []
  have call := call_run L.tree (.control .halt) (savedPrefix a ctx)
    TreeBudgetWholeTreeTM2.program program (fun _ => rfl) h
  let final : Cfg := {embed L.tree (.control .halt) (savedPrefix a ctx) out with l:=none}
  have last : machine.step (embed L.tree (.control .halt) (savedPrefix a ctx) out) = some final := by
    simp [machine,FinTM2.step,TM2.step,embed,hl,program,TM2.stepAux,final]
  have init : embed L.tree (.control .halt) (savedPrefix a ctx) (TreeBudgetWholeTreeTM2.start P []) =
      cfg treeEntry (work a 0 []) (savedPrefix a ctx) := by
    simp only [embed,TreeBudgetWholeTreeTM2.start,TreeBudgetWholeTreeTM2.cfg,TreeBudgetWholeTreeTM2.initial,
      hbP,cfg,treeEntry,work,store]
    rfl
  rw [init] at call
  have bound : (TreeBudgetParentWalkTM2.body P).length+(encodeNat P.root.val).length ≤
      (TreeBudgetParentPrefix.encode a).length := by
    simpa only [hbP,show P.root.val=a.root from rfl,Nat.add_comm] using
      (TreeBudgetParentPrefix.occupied a).1
  have powBound : ((TreeBudgetParentWalkTM2.body P).length+(encodeNat P.root.val).length+1)^4 ≤
      ((TreeBudgetParentPrefix.encode a).length+1)^4 := by gcongr
  refine ⟨final,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _ call (once last)) (by omega)⟩,rfl,?_,?_⟩
  · simpa [final,embed,TreeBudgetParentPrefix.decode_typed a hr hp,P] using hv
  · intro k; rfl

theorem reject_root (a : Raw) (h : ¬a.root<a.vertices) : TreeBudgetParentPrefix.accepted (TreeBudgetParentPrefix.encode a)=false := by
  rw [TreeBudgetParentPrefix.accepted_encode]
  by_cases hn : a.vertices=a.parents.length
  · rw [hn] at h
    simp [hn,decodeParents_invalid_root a.root a.parents (by omega)]
  · simp [hn]

theorem reject_index (a : Raw) (h : ¬∀ x∈a.parents,x<a.vertices) :
    TreeBudgetParentPrefix.accepted (TreeBudgetParentPrefix.encode a)=false := by
  rw [TreeBudgetParentPrefix.accepted_encode]
  by_cases hn : a.vertices=a.parents.length
  · rw [hn] at h
    have he : ∃ x∈a.parents,a.parents.length≤x := by push Not at h; exact h
    simp [hn,decodeParents_invalid_index a.root a.parents he]
  · simp [hn]

def preparedBound (S : ℕ) := 4096*(S+1)^4+64*(S+1)^2

theorem prepared_total (a : Raw) (ctx : Bits) :
    ∃ out, Nonempty (Run (cfg (entry .table) {} (savedPrefix a ctx)) out
      (preparedBound (TreeBudgetParentPrefix.encode a).length)) ∧ out.l=none ∧
      out.var.2=TreeBudgetParentPrefix.accepted (TreeBudgetParentPrefix.encode a) ∧
      kept (savedPrefix a ctx) out := by
  let S := (TreeBudgetParentPrefix.encode a).length
  have pre := prepare_run a ctx
  obtain ⟨hbr,hm,hn,hr,hp,ht⟩ := TreeBudgetParentPrefix.occupied a
  have hb : (TreeBudgetParentPrefix.body a).length≤S := by dsimp [S]; omega
  have hpoly : S+1≤(S+1)^2 := by nlinarith
  by_cases rootOK : a.root<a.vertices
  · simp only [rootEnd,if_pos rootOK] at pre
    have rows := range_run a ctx S 0 a.parents hn (by simpa) hb
    have hrows := range_contract a ctx 0 a.parents
    have htime : 16*(S+1)*(a.parents.length+1) ≤ 16*(S+1)^2 := by
      dsimp [S]; nlinarith
    have before := EvalsToInTime.trans machine.step _ _ _ _ _ pre rows
    by_cases indexOK : ∀ x∈a.parents,x<a.vertices
    · simp only [if_pos indexOK,Nat.zero_add] at hrows
      rw [hrows.1] at before
      have dim := dimension_run a ctx
      have throughDimension := EvalsToInTime.trans machine.step _ _ _ _ _ before dim
      by_cases dimOK : a.parents.length=a.vertices
      · simp only [dimensionEnd,if_pos dimOK] at throughDimension
        obtain ⟨out,⟨tree⟩,hl,hv,hk⟩ := tree_call a ctx (by simpa [dimOK] using rootOK)
          (by simpa [dimOK] using indexOK)
        refine ⟨out,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _ throughDimension tree) ?_⟩,hl,?_,hk⟩
        · dsimp [preparedBound]; change _ ≤ 4096*(S+1)^4+64*(S+1)^2; nlinarith
        · simpa [TreeBudgetParentPrefix.accepted_encode,dimOK] using hv
      · refine ⟨dimensionEnd a ctx,⟨weaken throughDimension ?_⟩,?_,?_,?_⟩
        · dsimp [preparedBound]; change _ ≤ 4096*(S+1)^4+64*(S+1)^2; nlinarith
        · simp [dimensionEnd,dimOK,stop]
        · simp [dimensionEnd,dimOK,stop,TreeBudgetParentPrefix.accepted_encode,Ne.symm dimOK]
        · intro k; simp [dimensionEnd,dimOK,stop,store,banks]
    · simp only [if_neg indexOK] at hrows
      refine ⟨rangeEnd a ctx 0 a.parents,⟨weaken before ?_⟩,hrows.1.1,?_,hrows.2⟩
      · dsimp [preparedBound]; change _ ≤ 4096*(S+1)^4+64*(S+1)^2; nlinarith
      · rw [hrows.1.2,reject_index a indexOK]
  · refine ⟨rootEnd a ctx,⟨weaken pre ?_⟩,?_,?_,?_⟩
    · dsimp [preparedBound]; change _ ≤ 4096*(S+1)^4+64*(S+1)^2; nlinarith
    · simp [rootEnd,rootOK,stop]
    · simp [rootEnd,rootOK,stop,reject_root a rootOK]
    · intro k; simp [rootEnd,rootOK,stop,store,banks]

def Preserved (s ctx : Bits) (out : Cfg) : Prop := out.stk context=ctx ∧
  ∀ a, TreeBudgetParentPrefix.parse s=some a → kept (savedPrefix a ctx) out

/-- Arbitrary raw instance bits, actual TM2 transitions, and the exact acceptance
predicate. This starts before m,n,r and stops with the H suffix untouched. -/
theorem prefix_polynomial (s ctx : Bits) :
    ∃ out, Nonempty (Run (start s ctx) out (16384*(s.length+1)^4)) ∧ out.l=none ∧
      out.var.2=TreeBudgetParentPrefix.accepted s ∧ Preserved s ctx out := by
  have parsed := call_run_right L.parser (.control .parsed) (TreeBudgetWholeTreeTM2.store {})
    TreeBudgetParentPrefixParse.program program (fun _ => rfl) (TreeBudgetParentPrefixParse.parse_run s ctx)
  have halt := TreeBudgetParentPrefixParse.terminal s ctx
  have hpoly : s.length+1≤(s.length+1)^2 := by nlinarith
  have hpow : (s.length+1)^2≤(s.length+1)^4 := by nlinarith
  cases hp : TreeBudgetParentPrefix.parse s with
  | none =>
    have hf := TreeBudgetParentPrefixParse.failed_flag s ctx hp
    let out : Cfg := {embedRight L.parser (.control .parsed) (TreeBudgetWholeTreeTM2.store {})
      (TreeBudgetParentPrefixParse.stopped s ctx) with l:=none}
    have last : machine.step (embedRight L.parser (.control .parsed) (TreeBudgetWholeTreeTM2.store {})
        (TreeBudgetParentPrefixParse.stopped s ctx)) = some out := by
      simp [machine,FinTM2.step,TM2.step,embedRight,halt,program,hf,TM2.stepAux,out]
    refine ⟨out,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _ parsed (once last))
      (by nlinarith only [hpoly,hpow])⟩,rfl,?_,?_,?_⟩
    · simpa [out,embedRight,TreeBudgetParentPrefix.accepted,hp] using hf
    · exact TreeBudgetParentPrefixParse.context_preserved s ctx
    · intro a ha; simp [hp] at ha
  | some a =>
    have hs := TreeBudgetParentPrefix.canonical s a hp
    subst s
    rw [TreeBudgetParentPrefixParse.success_layout] at parsed
    have last : machine.step (cfg (.control .parsed) {} (savedPrefix a ctx)) =
        some (cfg (entry .table) {} (savedPrefix a ctx)) := rfl
    obtain ⟨out,⟨run⟩,hl,hv,hk⟩ := prepared_total a ctx
    refine ⟨out,⟨weaken (EvalsToInTime.trans machine.step _ _ _ _ _
      (EvalsToInTime.trans machine.step _ _ _ _ _ parsed (once last)) run) ?_⟩,hl,hv,?_,?_⟩
    · dsimp [preparedBound]; nlinarith only [hpoly,hpow]
    · exact hk (.inl (.inl 5))
    · intro b hb
      have he : b=a := by simpa [TreeBudgetParentPrefix.parse_encode] using hb.symm
      subst b; exact hk

/-- In particular, success retains m,n,r, the canonical parent body, the exact
unparsed suffix, and the caller context in their physical stacks. -/
theorem saved_fields (a : Raw) (ctx : Bits) (out : Cfg) (h : kept (savedPrefix a ctx) out) :
    out.stk (.inr (.inr 0))=a.routes.bits ∧ out.stk dimension=a.vertices.bits ∧
    out.stk parsedRoot=a.root.bits ∧ out.stk parsedBody=TreeBudgetParentPrefix.body a ∧
    out.stk suffix=a.rest ∧ out.stk context=ctx :=
  ⟨h _,h _,h _,h _,h _,h _⟩

def inputPrefix (m : ℕ) (raw : RawInput) (tail : Bits) : Raw :=
  ⟨m,raw.n,raw.root,raw.parents,encodeNats raw.multiplicities ++
    (encodeInts raw.numerators ++ (encodeNats raw.denominators ++
      (encodeInt raw.budgetNumerator ++ (encodeNat raw.budgetDenominator ++ tail))))⟩

/-- Connection to the repository's real instance encoder, without a Shape
assumption. In particular a mismatching declared n is still tested. -/
theorem inputPrefix_encoding (m : ℕ) (raw : RawInput) (tail : Bits) :
    TreeBudgetParentPrefix.encode (inputPrefix m raw tail) =
      TreeBudgetSparseVerifier.encodeSpecified m raw ++ tail := by
  simp [TreeBudgetParentPrefix.encode,inputPrefix,TreeBudgetSparseVerifier.encodeSpecified,
    encodeInput,List.append_assoc]

theorem parse_inputPrefix (m : ℕ) (raw : RawInput) (tail : Bits) :
    TreeBudgetParentPrefix.parse (TreeBudgetSparseVerifier.encodeSpecified m raw ++ tail) =
      some (inputPrefix m raw tail) := by
  rw [← inputPrefix_encoding,TreeBudgetParentPrefix.parse_encode]

theorem prefix_from_init (s : Bits) :
    ∃ out, Nonempty (EvalsToInTime machine.step (initList machine s) (some out)
      (16384*(s.length+1)^4)) ∧ out.l=none ∧
      out.var.2=TreeBudgetParentPrefix.accepted s ∧ Preserved s [] out := by
  rw [init_eq]
  exact prefix_polynomial s []

end UAVProof.TreeBudgetParentPrefixTM2
