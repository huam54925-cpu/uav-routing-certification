import LeanCompletion.UAV.TreeBudgetNatRoutine
import LeanCompletion.UAV.TreeBudgetParentPrefixSpec

/-! The m,n headers followed by the existing root/count-list subprogram.
Every input, including a huge count with a short suffix, has a bit-length bound. -/
namespace UAVProof.TreeBudgetParentPrefixParse
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition

abbrev K := TreeBudgetEntryTM2.K ⊕ Fin 2
abbrev L := TreeBudgetEntryTM2.L ⊕ ((Fin 2 × Phase) ⊕ Bool)
abbrev Cfg := Configuration K L
def lab (i : Fin 2) (p : Phase) : L := .inr (.inl (i,p))
def bad : L := .inr (.inr false)
def ret : L := .inr (.inr true)
def next (i : Fin 2) : L := if i=0 then lab 1 .marker else .inl TreeBudgetEntryTM2.machine.main
def ports (i : Fin 2) : Ports K := ⟨.inl (.inl 0),.inl (.inl 1),.inr i,by decide,by simp,by simp⟩

def program : L → Statement K L
  | .inl l => compile Sum.inl ret (TreeBudgetEntryTM2.program l)
  | .inr (.inl (i,p)) => code (ports i) (lab i) (next i) bad true p
  | .inr (.inr b) => if b then .halt else .load (fun _ => (none,false)) .halt

def machine : FinTM2 where
  K := K
  k₀ := .inl (.inl 0)
  k₁ := .inl (.inl 2)
  Γ _ := Bool
  Λ := L
  main := lab 0 .marker
  σ := State
  initialState := (none,true)
  m := program

def store (s ctx : Bits) (saved : Fin 2 → Bits) : K → Bits :=
  banks (TreeBudgetEntryTM2.start s ctx).stk saved
def atLabel (l : L) (s ctx : Bits) (saved : Fin 2 → Bits) : Cfg := ⟨some l,(none,true),store s ctx saved⟩
def headers (m n : Bits) : Fin 2 → Bits := fun i => if i=0 then m else n
def start (s ctx : Bits) := atLabel (lab 0 .marker) s ctx (headers [] [])
def failed (s ctx : Bits) (saved : Fin 2 → Bits) : Cfg := ⟨none,(none,false),store s ctx saved⟩

theorem frame_layout (i : Fin 2) (l : L) (original s ctx : Bits) (saved : Fin 2 → Bits) (out : Bits) :
    cfg (ports i) (store original ctx saved) l none true s [] out =
      atLabel l s ctx (Function.update saved i out) := by
  unfold cfg atLabel
  congr 1
  funext k
  rcases k with (j | u) | v
  · fin_cases i <;> fin_cases j <;> rfl
  · cases u; fin_cases i <;> rfl
  · by_cases h : v=i <;> simp [tapes,ports,store,banks,h]

def headerEnd (i : Fin 2) (s ctx : Bits) (saved : Fin 2 → Bits) : Cfg := match parseNat s with
  | none => atLabel bad (TreeBudgetNatListLoop.suffix s) ctx saved
  | some (n,r) => atLabel (next i) r ctx (Function.update saved i (n.bits ++ saved i))

def header_run (i : Fin 2) (s ctx : Bits) (saved : Fin 2 → Bits) :
    EvalsToInTime machine.step (atLabel (lab i .marker) s ctx saved) (some (headerEnd i s ctx saved))
      (2*s.length+2) := by
  have h := TreeBudgetNatRoutine.run (ports i) (store s ctx saved) (lab i) (next i) bad
    program (fun _ => rfl) s (saved i)
  rw [frame_layout,Function.update_eq_self] at h
  unfold TreeBudgetNatRoutine.finish at h
  cases hp : parseNat s with
  | none =>
    simpa only [headerEnd,hp,frame_layout,Function.update_eq_self] using h
  | some pair =>
    obtain ⟨n,r⟩ := pair
    simpa only [headerEnd,hp,frame_layout] using h

def callee (saved : Fin 2 → Bits) (c : TreeBudgetEntryTM2.Cfg) : Cfg := embed Sum.inl ret saved c
def stopped (s ctx : Bits) : Cfg := match parseNat s with
  | none => failed (TreeBudgetNatListLoop.suffix s) ctx (headers [] [])
  | some (m,t) => match parseNat t with
    | none => failed (TreeBudgetNatListLoop.suffix t) ctx (headers m.bits [])
    | some (n,u) => {callee (headers m.bits n.bits) (TreeBudgetEntryTM2.stopped u ctx) with l:=none}

theorem entry_terminal (s ctx : Bits) : (TreeBudgetEntryTM2.stopped s ctx).l = none := by
  unfold TreeBudgetEntryTM2.stopped
  split <;> rfl

def parse_run (s ctx : Bits) : EvalsToInTime machine.step (start s ctx) (some (stopped s ctx))
    (32*(s.length+1)^2) := by
  have h₀ := header_run 0 s ctx (headers [] [])
  cases hm : parseNat s with
  | none =>
    simp only [headerEnd,hm] at h₀
    have hs : machine.step (atLabel bad (TreeBudgetNatListLoop.suffix s) ctx (headers [] [])) =
        some (stopped s ctx) := by rw [stopped,hm]; rfl
    exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ h₀ (once hs)) (by nlinarith)
  | some pair =>
    obtain ⟨m,t⟩ := pair
    have he : Function.update (headers [] []) 0 (m.bits ++ headers [] [] 0) = headers m.bits [] := by
      funext i; fin_cases i <;> simp [headers]
    simp only [headerEnd,hm,he] at h₀
    have h₁ := header_run 1 t ctx (headers m.bits [])
    have ht : t.length ≤ s.length := by
      have := congrArg List.length (parseNat_canonical s t m hm)
      simp only [List.length_append] at this
      omega
    cases hn : parseNat t with
    | none =>
      simp only [headerEnd,hn] at h₁
      have hs : machine.step (atLabel bad (TreeBudgetNatListLoop.suffix t) ctx (headers m.bits [])) =
          some (stopped s ctx) := by simp only [stopped,hm,hn]; rfl
      exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _
        (EvalsToInTime.trans machine.step _ _ _ _ _ h₀ h₁) (once hs)) (by nlinarith)
    | some pair =>
      obtain ⟨n,u⟩ := pair
      have he : Function.update (headers m.bits []) 1 (n.bits ++ headers m.bits [] 1) =
          headers m.bits n.bits := by funext i; fin_cases i <;> simp [headers]
      simp only [headerEnd,hn,he] at h₁
      have hc := call_run Sum.inl ret (headers m.bits n.bits) TreeBudgetEntryTM2.program program
        (fun _ => rfl) (TreeBudgetEntryTM2.entry_run u ctx)
      have hs : machine.step (callee (headers m.bits n.bits) (TreeBudgetEntryTM2.stopped u ctx)) =
          some (stopped s ctx) := by
        simp only [stopped,hm,hn]
        simp [machine,FinTM2.step,TM2.step,callee,embed,entry_terminal,program,ret,TM2.stepAux]
      have hu : u.length ≤ s.length := by
        have := congrArg List.length (parseNat_canonical t u n hn)
        simp only [List.length_append] at this
        omega
      have hb : (u.length+1)^2 ≤ (s.length+1)^2 := by gcongr
      exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _
        (EvalsToInTime.trans machine.step _ _ _ _ _
          (EvalsToInTime.trans machine.step _ _ _ _ _ h₀ h₁) hc) (once hs)) (by nlinarith)

theorem terminal (s ctx : Bits) : (stopped s ctx).l = none := by
  unfold stopped
  split
  · rfl
  · split <;> rfl

theorem context_preserved (s ctx : Bits) : (stopped s ctx).stk (.inl (.inl 5)) = ctx := by
  unfold stopped
  split
  · rfl
  · split
    · rfl
    · exact (TreeBudgetEntryTM2.refines _ ctx).2

theorem success_layout (a : TreeBudgetParentPrefix.Raw) (ctx : Bits) :
    stopped (TreeBudgetParentPrefix.encode a) ctx =
      ⟨none,(none,true),banks
        (TreeBudgetEntryTM2.callee a.root
          {TreeBudgetNatListLoop.conf 17 a.rest (TreeBudgetParentPrefix.body a) [] [] ctx with l:=none}).stk
        (headers a.routes.bits a.vertices.bits)⟩ := by
  simp only [stopped,TreeBudgetParentPrefix.encode,parseNat_append]
  simp only [TreeBudgetEntryTM2.stopped,parseNat_append,TreeBudgetParentWalkTM2.list_output]
  rfl

theorem failed_flag (s ctx : Bits) (h : TreeBudgetParentPrefix.parse s = none) :
    (stopped s ctx).var.2 = false := by
  cases hm : parseNat s with
  | none => simp [stopped,hm,failed]
  | some pair =>
    obtain ⟨m,t⟩ := pair
    cases hn : parseNat t with
    | none => simp [stopped,hm,hn,failed]
    | some pair =>
      obtain ⟨n,u⟩ := pair
      cases hr : parseNat u with
      | none => simp [stopped,hm,hn,callee,embed,TreeBudgetEntryTM2.stopped,hr]
      | some pair =>
        obtain ⟨r,v⟩ := pair
        have hp : parseNats v = none := by
          cases he : parseNats v with
          | none => rfl
          | some e => simp [TreeBudgetParentPrefix.parse,TreeBudgetSparseCodec.parseEntry,hm,hn,hr,he] at h
        have hl := TreeBudgetIndexedZeroTM2.layout v ctx
        simp only [hp] at hl
        simpa [stopped,hm,hn,callee,embed,TreeBudgetEntryTM2.stopped,hr,TreeBudgetEntryTM2.callee] using hl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by change Finite Bool; infer_instance

end UAVProof.TreeBudgetParentPrefixParse
