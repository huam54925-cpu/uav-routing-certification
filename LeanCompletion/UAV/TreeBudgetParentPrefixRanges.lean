import LeanCompletion.UAV.TreeBudgetParentPrefixRuns

namespace UAVProof.TreeBudgetParentPrefixTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open TreeBudgetParentPrefix (Raw)

def savedPrefix (a : Raw) (ctx : Bits) : Saved := banks
  (TreeBudgetEntryTM2.callee a.root
    {TreeBudgetNatListLoop.conf 17 a.rest (TreeBudgetParentPrefix.body a) [] [] ctx with l:=none}).stk
  (TreeBudgetParentPrefixParse.headers a.routes.bits a.vertices.bits)

@[simp] theorem saved_body (a : Raw) (ctx : Bits) :
    savedPrefix a ctx (.inl (.inl 2))=TreeBudgetParentPrefix.body a := rfl
@[simp] theorem saved_root (a : Raw) (ctx : Bits) : savedPrefix a ctx (.inl (.inr ()))=a.root.bits := rfl
@[simp] theorem saved_dimension (a : Raw) (ctx : Bits) : savedPrefix a ctx (.inr 1)=a.vertices.bits := rfl
def work (a : Raw) (i : ℕ) (xs : List ℕ) : Data :=
  {body:=TreeBudgetParentPrefix.body a,root:=encodeNat a.root,q:=xs.flatMap encodeNat,idx:=i.bits}

def rootEnd (a : Raw) (ctx : Bits) : Cfg := if a.root < a.vertices then
  cfg (.control .loop) (work a 0 a.parents) (savedPrefix a ctx)
  else stop (work a 0 []) (savedPrefix a ctx) false

def prepare_run (a : Raw) (ctx : Bits) :
    Run (cfg (entry .table) {} (savedPrefix a ctx)) (rootEnd a ctx)
      (16*((TreeBudgetParentPrefix.encode a).length+1)) := by
  let s := savedPrefix a ctx
  let d₁ : Data := {body:=TreeBudgetParentPrefix.body a}
  let d₂ : Data := {body:=TreeBudgetParentPrefix.body a,root:=encodeNat a.root}
  let d₃ : Data := {d₂ with r:=a.root.bits}
  let d₄ : Data := {d₃ with t:=a.vertices.bits}
  have h₀ : Run (cfg (entry .table) {} s) (cfg (entry .rootFrame) d₁ s)
      (2*(TreeBudgetParentPrefix.body a).length+2) := by simpa [copied,source,dest,setDest,framed] using copy_job .table {} s rfl
  have h₁ : Run (cfg (entry .rootFrame) d₁ s) (cfg (entry .rootDigit) d₂ s)
      (2*a.root.bits.length+2) := by simpa [copied,source,dest,setDest,framed,encodeNat,d₁,d₂,s] using copy_job .rootFrame d₁ s rfl
  have h₂ : Run (cfg (entry .rootDigit) d₂ s) (cfg (entry .rootBound) d₃ s)
      (2*a.root.bits.length+2) := by simpa [copied,source,dest,setDest,framed,d₂,d₃,s] using copy_job .rootDigit d₂ s rfl
  have h₃ : Run (cfg (entry .rootBound) d₃ s) (cfg (.beginCompare .root) d₄ s)
      (2*a.vertices.bits.length+2) := by simpa [copied,source,dest,setDest,framed,d₂,d₃,d₄,s] using copy_job .rootBound d₃ s rfl
  have hc := compare_job .root d₄ s
  have he : comparison .root d₄ = decide (a.root < a.vertices) := by
    rw [strict_comparison .root (by decide)]; simp [d₄,d₃,d₂]
  have pre := EvalsToInTime.trans machine.step _ _ _ _ _
    (EvalsToInTime.trans machine.step _ _ _ _ _
      (EvalsToInTime.trans machine.step _ _ _ _ _
        (EvalsToInTime.trans machine.step _ _ _ _ _ h₀ h₁) h₂) h₃) hc
  obtain ⟨hbr,hm,hn,hr,hp,ht⟩ := TreeBudgetParentPrefix.occupied a
  have hb : (TreeBudgetParentPrefix.body a).length ≤ (TreeBudgetParentPrefix.encode a).length := by omega
  by_cases h : a.root < a.vertices
  · have hbdy : Run (cfg (entry .body) d₂ s) (cfg (.control .loop) (work a 0 a.parents) s)
        (2*(TreeBudgetParentPrefix.body a).length+2) := by simpa [copied,source,dest,setDest,framed,d₂,work,s] using copy_job .body d₂ s rfl
    simp [compared,he,h,after] at pre
    apply weaken (show Run _ (rootEnd a ctx) _ from by
      simpa [rootEnd,h] using EvalsToInTime.trans machine.step _ _ _ _ _ pre hbdy)
    dsimp [d₄,d₃,d₂]; nlinarith
  · simp [compared,he,h,after] at pre
    apply weaken (show Run _ (rootEnd a ctx) _ from by simpa [rootEnd,h,work,d₄,d₃,d₂,s] using pre)
    dsimp [d₄,d₃,d₂]; nlinarith

def rangeEnd (a : Raw) (ctx : Bits) : ℕ → List ℕ → Cfg
  | i,[] => cfg (entry .counterDigit) (work a i []) (savedPrefix a ctx)
  | i,x::xs => if x<a.vertices then rangeEnd a ctx (i+1) xs
      else stop (work a i xs) (savedPrefix a ctx) false

def range_run (a : Raw) (ctx : Bits) (S i : ℕ) (xs : List ℕ)
    (hn : a.vertices.bits.length≤S) (hi : i+xs.length≤S)
    (hb : (xs.flatMap encodeNat).length≤S) :
    Run (cfg (.control .loop) (work a i xs) (savedPrefix a ctx)) (rangeEnd a ctx i xs)
      (16*(S+1)*(xs.length+1)) := by
  induction xs generalizing i with
  | nil =>
    apply weaken (once (loop_empty (work a i []) (savedPrefix a ctx) rfl))
    simp; omega
  | cons x xs ih =>
    let s := savedPrefix a ctx
    let d₀ := work a i (x::xs)
    let d₁ : Data := {work a i xs with r:=x.bits}
    let d₂ : Data := {d₁ with t:=a.vertices.bits}
    have hne : d₀.q≠[] := by
      dsimp [d₀,work]
      simp only [List.flatMap_cons,List.append_eq_nil_iff,not_and]
      intro h
      have hlen := encodeNat_nonempty x
      simp [h] at hlen
    have hf : Run (cfg (.frame .marker) d₀ s) (cfg (entry .parentBound) d₁ s)
        (2*d₀.q.length+2) := field_run d₀ s x (xs.flatMap encodeNat) rfl rfl rfl
    have hc : Run (cfg (entry .parentBound) d₁ s) (cfg (.beginCompare .parent) d₂ s)
        (2*a.vertices.bits.length+2) := by simpa [copied,source,dest,setDest,framed,d₁,d₂,work,s] using copy_job .parentBound d₁ s rfl
    have he : comparison .parent d₂ = decide (x<a.vertices) := by
      rw [strict_comparison .parent (by decide)]; simp [d₂,d₁,work]
    have hp := EvalsToInTime.trans machine.step _ _ _ _ _
      (EvalsToInTime.trans machine.step _ _ _ _ _ (prepend (loop_more d₀ s hne) hf) hc)
      (compare_job .parent d₂ s)
    have hib : i.bits.length≤S := by
      simp only [Nat.size_eq_bits_len]
      exact (TreeBudgetCostedCodec.nat_size_le i).trans (by omega)
    have hxb : x.bits.length≤S := by
      simp only [List.flatMap_cons,List.length_append,encodeNat_length,Nat.size_eq_bits_len] at hb ⊢
      omega
    have hb' : (xs.flatMap encodeNat).length≤S := by
      simp only [List.flatMap_cons,List.length_append] at hb
      omega
    have hstep : 2*d₀.q.length+2+1+(2*a.vertices.bits.length+2)+
        (d₂.r.length+d₂.t.length+3)+(2*i.bits.length+2) ≤ 16*(S+1) := by
      dsimp [d₀,d₂,d₁,work]
      nlinarith
    by_cases hx : x<a.vertices
    · have ht := ih (i+1) (by simp only [List.length_cons] at hi; omega) hb'
      have hin : Run (cfg (entry .increment) (work a i xs) s)
          (cfg (.control .loop) (work a (i+1) xs) s) (2*i.bits.length+2) := by
        simpa [work,TreeBudgetStackRoutine.increment_bits] using increment_job (work a i xs) s rfl
      simp [compared,he,hx,after] at hp
      have h := EvalsToInTime.trans machine.step _ _ _ _ _
        (EvalsToInTime.trans machine.step _ _ _ _ _ hp hin) ht
      apply weaken (show Run _ (rangeEnd a ctx i (x::xs)) _ from by simpa [rangeEnd,hx] using h)
      simp only [List.length_cons]
      nlinarith
    · simp [compared,he,hx,after] at hp
      apply weaken (show Run _ (rangeEnd a ctx i (x::xs)) _ from by
        simpa [rangeEnd,hx,d₂,d₁,work,s] using hp)
      simp only [List.length_cons]
      nlinarith

theorem range_contract (a : Raw) (ctx : Bits) (i : ℕ) (xs : List ℕ) :
    (if ∀ x∈xs,x<a.vertices then
      rangeEnd a ctx i xs = cfg (entry .counterDigit) (work a (i+xs.length) []) (savedPrefix a ctx)
    else (rangeEnd a ctx i xs).l=none ∧ (rangeEnd a ctx i xs).var.2=false) ∧
    kept (savedPrefix a ctx) (rangeEnd a ctx i xs) := by
  induction xs generalizing i with
  | nil => simp [rangeEnd,kept,cfg,store,banks]
  | cons x xs ih =>
    by_cases h : x<a.vertices
    · simpa [rangeEnd,h,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1)
    · simp [rangeEnd,h,stop,kept,store,banks]

def dimensionEnd (a : Raw) (ctx : Bits) : Cfg := if a.parents.length=a.vertices then
  cfg treeEntry (work a 0 []) (savedPrefix a ctx)
  else stop (work a a.parents.length []) (savedPrefix a ctx) false

def dimension_run (a : Raw) (ctx : Bits) :
    Run (cfg (entry .counterDigit) (work a a.parents.length []) (savedPrefix a ctx))
      (dimensionEnd a ctx) (10*((TreeBudgetParentPrefix.encode a).length+1)) := by
  let s := savedPrefix a ctx
  let d₀ := work a a.parents.length []
  let d₁ : Data := {d₀ with r:=a.parents.length.bits}
  let d₂ : Data := {d₁ with t:=a.vertices.bits}
  have h₀ : Run (cfg (entry .counterDigit) d₀ s) (cfg (entry .counterBound) d₁ s)
      (2*a.parents.length.bits.length+2) := by simpa [copied,source,dest,setDest,framed,d₀,d₁,work] using copy_job .counterDigit d₀ s rfl
  have h₁ : Run (cfg (entry .counterBound) d₁ s) (cfg (.beginCompare .dimension) d₂ s)
      (2*a.vertices.bits.length+2) := by simpa [copied,source,dest,setDest,framed,d₀,d₁,d₂,work,s] using copy_job .counterBound d₁ s rfl
  have he : comparison .dimension d₂ = decide (a.parents.length=a.vertices) := by
    rw [dimension_comparison]
    apply Bool.decide_congr
    constructor
    · intro h; simpa [d₂,d₁,d₀,work] using congrArg value h
    · intro h; simp [d₂,d₁,h]
  have h := EvalsToInTime.trans machine.step _ _ _ _ _
    (EvalsToInTime.trans machine.step _ _ _ _ _ h₀ h₁) (compare_job .dimension d₂ s)
  obtain ⟨hbr,hm,hn,hr,hp,ht⟩ := TreeBudgetParentPrefix.occupied a
  have hi : a.parents.length.bits.length≤(TreeBudgetParentPrefix.encode a).length := by
    simp only [Nat.size_eq_bits_len]
    exact (TreeBudgetCostedCodec.nat_size_le a.parents.length).trans hp
  by_cases hd : a.parents.length=a.vertices
  · simp [compared,he,hd,after] at h
    have tail := clear_job d₀ s
    apply weaken (show Run _ (dimensionEnd a ctx) _ from by
      simpa [dimensionEnd,hd,d₀,work,s] using EvalsToInTime.trans machine.step _ _ _ _ _ h tail)
    dsimp [d₂,d₁,d₀,work]; nlinarith
  · simp [compared,he,hd,after] at h
    apply weaken (show Run _ (dimensionEnd a ctx) _ from by simpa [dimensionEnd,hd,d₂,d₁,d₀,s] using h)
    dsimp [d₂,d₁,d₀,work]; nlinarith

end UAVProof.TreeBudgetParentPrefixTM2
