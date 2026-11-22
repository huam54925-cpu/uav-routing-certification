import LeanCompletion.UAV.TreeBudgetRowCheckBlocks
import LeanCompletion.UAV.TreeBudgetRowCheckSpec
import LeanCompletion.UAV.TreeBudgetNaturalLookupIndex
import LeanCompletion.UAV.TreeBudgetIntTM2

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/- The persistent bank is arbitrary. The loop owns exactly registers 10..34. -/
def state (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) : K → Bits
  | .inl _ => []
  | .inr k => match k.val with
      | 10 => P | 11 => H | 12 => u | 13 => ap | 14 => an
      | 15 => par | 16 => cap | 17 => coord | 18 => plus | 19 => minus
      | 20 => positive | 21 => negative | 22 => mass
      | 23 => [] | 24 => [] | 25 => [] | 26 => [] | 27 => []
      | 28 => [] | 29 => [] | 30 => [] | 31 => [] | 32 => [] | 33 => [] | 34 => []
      | _ => base (.inr k)

def ready (base : K → Bits) (P H u ap an positive negative mass : Bits) : K → Bits :=
  state base P H u ap an [] [] [] [] [] positive negative mass

structure Execution (a b : Configuration K (Label PC)) where
  val : ℕ
  property : Run instructions a b val

def source (i : Fin 24) : K := reg ⟨i.val,by omega⟩
def operandPort (i : Fin 24) (dst : Fin 35) (hd : 24<dst.val) : Ports K :=
  ⟨source i,reg 24,reg dst,
    by simp only [source,reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega,
    by simp only [source,reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega,
    by simp only [source,reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]; omega⟩

@[simp] theorem set_source (s : K → Bits) (i : Fin 24) (j : Fin 35)
    (hj : 24≤j.val) (v : Bits) : set s j v (source i)=s (source i) := by
  apply Function.update_of_ne
  simp only [source,reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]
  omega

theorem clear_pair (s : K → Bits) (u v : Bits)
    (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[]) :
    set (set (set (set s 31 u) 32 v) 31 []) 32 []=s := by
  funext k
  by_cases h31 : k=reg 31
  · subst k; simp [set,reg,h₁]
  · by_cases h32 : k=reg 32
    · subst k; simp [set,reg,h₂]
    · simp [set,h31,h32]

/-- Copying comparison operands preserves their sources. The destructive
comparison leaves its complete temporary bank empty on either branch. -/
def compare_saved (l₁ l₂ l₃ yes no : PC) (i j : Fin 24)
    (c₁ : instructions l₁=.copy (operandPort i 31 (by decide)) false l₂)
    (c₂ : instructions l₂=.copy (operandPort j 32 (by decide)) false l₃)
    (c₃ : instructions l₃=.le cw yes no)
    (s : K → Bits) (hs : s (reg 24)=[])
    (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    Execution (cfg l₁ s)
      (cfg (if value (s (source i))≤value (s (source j)) then yes else no) s) := by
  let u := s (source i)
  let v := s (source j)
  have a := copy_run instructions l₁ l₂ (operandPort i 31 (by decide)) false c₁ s hs
  have b := copy_run instructions l₂ l₃ (operandPort j 32 (by decide)) false c₂ (set s 31 u)
    (by simp [operandPort,set,reg,hs])
  have c := compare_block l₃ yes no c₃ (set (set s 31 u) 32 v)
    (by simp [set,reg,h₃]) (by simp [set,reg,h₄])
  simp only [Bool.false_eq_true,ite_false,operandPort,h₁,List.append_nil] at a
  change Run instructions (cfg l₁ s) (cfg l₂ (set s 31 u)) (2*u.length+3) at a
  simp only [Bool.false_eq_true,ite_false,operandPort] at b
  rw [set_source _ _ _ (by decide)] at b
  simp only [set,Function.update_of_ne (show reg 32≠reg 31 by decide),h₂,List.append_nil] at b
  change Run instructions (cfg l₂ (set s 31 u)) (cfg l₃ (set (set s 31 u) 32 v)) (2*v.length+3) at b
  have hout := clear_pair s u v h₁ h₂
  rw [hout] at c
  simp only [set,Function.update_self,Function.update_of_ne (show reg 31≠reg 32 by decide)] at c
  exact ⟨_,seq instructions (seq instructions a b) c⟩

theorem clear_operands (s : K → Bits) (u v : Bits)
    (h₁ : s (reg 26)=[]) (h₂ : s (reg 27)=[]) :
    set (set (set (set s 26 u) 27 v) 26 []) 27 []=s := by
  funext k
  by_cases h26 : k=reg 26
  · subst k; simp [set,reg,h₁]
  · by_cases h27 : k=reg 27
    · subst k; simp [set,reg,h₂]
    · simp [set,h26,h27]

@[simp] theorem set_acc (s : K → Bits) (i : Fin 3) (j : Fin 35)
    (hj : 23≤j.val) (v : Bits) : set s j v (acc i)=s (acc i) := by
  apply Function.update_of_ne
  simp only [acc,reg,ne_eq,Sum.inr.injEq,Fin.ext_iff]
  omega

def weighted_saved (l₁ l₂ l₃ next : PC) (i j : Fin 24) (a : Fin 3)
    (c₁ : instructions l₁=.copy (operandPort i 26 (by decide)) false l₂)
    (c₂ : instructions l₂=.copy (operandPort j 27 (by decide)) false l₃)
    (c₃ : instructions l₃=.weighted (mw a) next)
    (s : K → Bits) (hs : s (reg 24)=[])
    (h₁ : s (reg 26)=[]) (h₂ : s (reg 27)=[])
    (h₃ : s (reg 28)=[]) (h₄ : s (reg 29)=[]) :
    Execution (cfg l₁ s)
      (cfg next (Function.update s (acc a)
        (TreeBudgetWeightedTM2.weighted (s (source i)) (s (source j)) (s (acc a))))) := by
  let u := s (source i)
  let v := s (source j)
  have first := copy_run instructions l₁ l₂ (operandPort i 26 (by decide)) false c₁ s hs
  have second := copy_run instructions l₂ l₃ (operandPort j 27 (by decide)) false c₂ (set s 26 u)
    (by simp [operandPort,set,reg,hs])
  have third := weighted_block l₃ next a c₃ (set (set s 26 u) 27 v)
    (by simp [set,reg,h₃]) (by simp [set,reg,h₄])
  simp only [Bool.false_eq_true,ite_false,operandPort,h₁,List.append_nil] at first
  change Run instructions (cfg l₁ s) (cfg l₂ (set s 26 u)) (2*u.length+3) at first
  simp only [Bool.false_eq_true,ite_false,operandPort] at second
  rw [set_source _ _ _ (by decide)] at second
  simp only [set,Function.update_of_ne (show reg 27≠reg 26 by decide),h₂,List.append_nil] at second
  change Run instructions (cfg l₂ (set s 26 u)) (cfg l₃ (set (set s 26 u) 27 v)) (2*v.length+3) at second
  have hout := clear_operands s u v h₁ h₂
  rw [set_acc _ _ _ (by decide),set_acc _ _ _ (by decide)] at third
  rw [hout] at third
  simp only [set,Function.update_self,Function.update_of_ne (show reg 26≠reg 27 by decide)] at third
  exact ⟨_,seq instructions (seq instructions first second) third⟩

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨reg $s,reg 24,reg $d,by decide,by decide,by decide⟩ : Ports K))

def copy_empty (l next : PC) (p : Ports K) (h : instructions l=.copy p false next)
    (s : K → Bits) (u : Bits) (hs : s p.src=u) (ht : s p.scratch=[]) (hd : s p.dst=[]) :
    Run instructions (cfg l s) (cfg next (Function.update s p.dst u)) (2*u.length+3) := by
  simpa only [hs,hd,Bool.false_eq_true,ite_false,List.append_nil] using
    copy_run instructions l next p false h s ht

theorem state_base (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits)
    (j : Fin 35) (hj : j.val<10) :
    state base P H u ap an par cap coord plus minus positive negative mass (reg j)=base (reg j) := by
  fin_cases j <;> simp_all [state,reg]

def prepare_run (P H u ap an root tp tn ctx suffix : Bits) :
    Execution (cfg .prepP (store P H u ap an root tp tn ctx suffix))
      (cfg .loop (ready (store P H u ap an root tp tn ctx suffix) P H u ap an tn tp [])) := by
  let s := store P H u ap an root tp tn ctx suffix
  let s1 := set s 10 P
  let s2 := set s1 11 H
  let s3 := set s2 12 u
  let s4 := set s3 13 ap
  let s5 := set s4 14 an
  let s6 := set s5 20 tn
  let s7 := set s6 21 tp
  have a := copy_empty .prepP .prepH port(0,10) rfl s P rfl rfl rfl
  have b := copy_empty .prepH .prepRow port(1,11) rfl s1 H rfl rfl rfl
  have c := copy_empty .prepRow .prepPos port(2,12) rfl s2 u rfl rfl rfl
  have d := copy_empty .prepPos .prepNeg port(3,13) rfl s3 ap rfl rfl rfl
  have e := copy_empty .prepNeg .prepBudgetPos port(4,14) rfl s4 an rfl rfl rfl
  have f := copy_empty .prepBudgetPos .prepBudgetNeg port(7,20) rfl s5 tn rfl rfl rfl
  have g := copy_empty .prepBudgetNeg .loop port(6,21) rfl s6 tp rfl rfl rfl
  have he : s7=ready s P H u ap an tn tp [] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [s7,s6,s5,s4,s3,s2,s1,s,set,state,ready,store,reg]
  have run := seq instructions (seq instructions (seq instructions (seq instructions
    (seq instructions (seq instructions a b) c) d) e) f) g
  change Run instructions (cfg .prepP s) (cfg .loop s7) _ at run
  rw [he] at run
  exact ⟨_,run⟩

def read_fields (base : K → Bits) (ps hs us aps ans positive negative mass : Bits)
    (parent H u ap an : ℕ) :
    Execution (cfg .loop (ready base (encodeNat parent++ps) (encodeNat H++hs)
      (encodeNat u++us) (encodeNat ap++aps) (encodeNat an++ans) positive negative mass))
      (cfg .capU (state base ps hs us aps ans parent.bits H.bits u.bits ap.bits an.bits
        positive negative mass)) := by
  let s := ready base (encodeNat parent++ps) (encodeNat H++hs)
    (encodeNat u++us) (encodeNat ap++aps) (encodeNat an++ans) positive negative mass
  let s1 := set (set s 10 ps) 15 parent.bits
  let s2 := set (set s1 11 hs) 16 H.bits
  let s3 := set (set s2 12 us) 17 u.bits
  let s4 := set (set s3 13 aps) 18 ap.bits
  let s5 := set (set s4 14 ans) 19 an.bits
  have test := test_run instructions .loop .massLeft .readP (reg 10) rfl
    (ready base (encodeNat parent++ps) (encodeNat H++hs)
      (encodeNat u++us) (encodeNat ap++aps) (encodeNat an++ans) positive negative mass)
  have he : ((encodeNat parent++ps).isEmpty)=false := by
    simp [encodeNat,word]
  simp only [ready,state,reg,he,Bool.false_eq_true,ite_false] at test
  have a := read_run instructions .readP .readH port(10,15) rfl s parent.bits ps rfl rfl rfl
  have b := read_run instructions .readH .readRow port(11,16) rfl s1 H.bits hs rfl rfl rfl
  have c := read_run instructions .readRow .readPos port(12,17) rfl s2 u.bits us rfl rfl rfl
  have d := read_run instructions .readPos .readNeg port(13,18) rfl s3 ap.bits aps rfl rfl rfl
  have e := read_run instructions .readNeg .capU port(14,19) rfl s4 an.bits ans rfl rfl rfl
  have he : s5=state base ps hs us aps ans parent.bits H.bits u.bits ap.bits an.bits positive negative mass := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [s5,s4,s3,s2,s1,s,set,state,ready,reg]
  have run := seq instructions (seq instructions (seq instructions (seq instructions
    (seq instructions test a) b) c) d) e
  change Run instructions (cfg .loop s) (cfg .capU s5) _ at run
  rw [he] at run
  exact ⟨_,run⟩

theorem state_positive (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass out : Bits) :
    Function.update (state base P H u ap an par cap coord plus minus positive negative mass) (acc 0) out=
      state base P H u ap an par cap coord plus minus out negative mass := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> simp [state,acc,reg]

theorem state_negative (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass out : Bits) :
    Function.update (state base P H u ap an par cap coord plus minus positive negative mass) (acc 1) out=
      state base P H u ap an par cap coord plus minus positive out mass := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> simp [state,acc,reg]

theorem state_mass (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass out : Bits) :
    Function.update (state base P H u ap an par cap coord plus minus positive negative mass) (acc 2) out=
      state base P H u ap an par cap coord plus minus positive negative out := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> simp [state,acc,reg]

def cap_run (base : K → Bits) (P H u ap an par plus minus positive negative mass : Bits) (cap coord : ℕ) :
    Execution (cfg .capU (state base P H u ap an par cap.bits coord.bits plus minus positive negative mass))
      (cfg (if coord≤cap then .selfPosU else bad)
        (state base P H u ap an par cap.bits coord.bits plus minus positive negative mass)) := by
  have e := compare_saved .capU .capH .capCompare .selfPosU bad 17 16 rfl rfl rfl
    (state base P H u ap an par cap.bits coord.bits plus minus positive negative mass) rfl rfl rfl rfl rfl
  exact ⟨e.val, by simpa only [source,state,reg,value_bits] using e.property⟩

def self_run (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    Execution (cfg .selfPosU (state base P H u ap an par cap coord plus minus positive negative mass))
      (cfg .parentLeft (state base P H u ap an par cap coord plus minus
        (TreeBudgetWeightedTM2.weighted coord plus positive)
        (TreeBudgetWeightedTM2.weighted coord minus negative) mass)) := by
  have first := weighted_saved .selfPosU .selfPosH .selfPosRun .selfNegU 17 18 0 rfl rfl rfl
    (state base P H u ap an par cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl
  have firstProp := first.property
  change Run instructions _ (cfg .selfNegU (Function.update
    (state base P H u ap an par cap coord plus minus positive negative mass) (acc 0)
      (TreeBudgetWeightedTM2.weighted coord plus positive))) first.val at firstProp
  rw [state_positive] at firstProp
  have second := weighted_saved .selfNegU .selfNegH .selfNegRun .parentLeft 17 19 1 rfl rfl rfl
    (state base P H u ap an par cap coord plus minus
      (TreeBudgetWeightedTM2.weighted coord plus positive) negative mass) rfl rfl rfl rfl rfl
  have secondProp := second.property
  change Run instructions _ (cfg .parentLeft (Function.update
    (state base P H u ap an par cap coord plus minus
      (TreeBudgetWeightedTM2.weighted coord plus positive) negative mass) (acc 1)
      (TreeBudgetWeightedTM2.weighted coord minus negative))) second.val at secondProp
  rw [state_negative] at secondProp
  exact ⟨_, seq instructions firstProp secondProp⟩

def parent_choice (base : K → Bits) (P H u ap an cap coord plus minus positive negative mass : Bits)
    (parent root : ℕ) (hr : base (reg 5)=root.bits) :
    Execution (cfg .parentLeft
      (state base P H u ap an parent.bits cap coord plus minus positive negative mass))
      (cfg (if parent=root then .rootAddU else .parentNonzero)
        (state base P H u ap an parent.bits cap coord plus minus positive negative mass)) := by
  let s := state base P H u ap an parent.bits cap coord plus minus positive negative mass
  have first := compare_saved .parentLeft .rootRight .parentLEroot .rootLeft .parentNonzero
    15 5 rfl rfl rfl s rfl rfl rfl rfl rfl
  have second := compare_saved .rootLeft .parentRight .rootLEparent .rootAddU .parentNonzero
    5 15 rfl rfl rfl s rfl rfl rfl rfl rfl
  have firstProp := first.property
  have secondProp := second.property
  change Run instructions (cfg .parentLeft s)
    (cfg (if value parent.bits≤value (base (reg 5)) then .rootLeft else .parentNonzero) s) first.val at firstProp
  change Run instructions (cfg .rootLeft s)
    (cfg (if value (base (reg 5))≤value parent.bits then .rootAddU else .parentNonzero) s) second.val at secondProp
  rw [hr,value_bits,value_bits] at firstProp secondProp
  by_cases hpr : parent≤root
  · simp only [if_pos hpr] at firstProp
    have run := seq instructions firstProp secondProp
    have he : (root≤parent) ↔ parent=root := by omega
    exact ⟨_, by simpa only [he] using run⟩
  · have he : parent≠root := by omega
    exact ⟨first.val, by simpa only [if_neg hpr,if_neg he] using firstProp⟩

def root_mass_run (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    Execution (cfg .rootAddU (state base P H u ap an par cap coord plus minus positive negative mass))
      (cfg (.roundClear 0) (state base P H u ap an par cap coord plus minus positive negative
        (TreeBudgetWeightedTM2.weighted coord [true] mass))) := by
  let s := state base P H u ap an par cap coord plus minus positive negative mass
  have first := copy_run instructions .rootAddU .rootAddOne (operandPort 17 26 (by decide)) false rfl s rfl
  simp only [operandPort,source,reg,s,state,Bool.false_eq_true,ite_false,List.append_nil] at first
  change Run instructions (cfg .rootAddU s) (cfg .rootAddOne (set s 26 coord)) (2*coord.length+3) at first
  have second := push_run instructions .rootAddOne .rootAddRun (reg 27) true rfl (set s 26 coord)
  change Run instructions (cfg .rootAddOne (set s 26 coord))
    (cfg .rootAddRun (set (set s 26 coord) 27 [true])) 1 at second
  have third := weighted_block .rootAddRun (.roundClear 0) 2 rfl (set (set s 26 coord) 27 [true])
    (by simp [set,reg,s,state]) (by simp [set,reg,s,state])
  rw [set_acc _ _ _ (by decide),set_acc _ _ _ (by decide)] at third
  have hout := clear_operands s coord [true] rfl rfl
  rw [hout] at third
  simp only [set,Function.update_self,Function.update_of_ne (show reg 26≠reg 27 by decide)] at third
  change Run instructions _ (cfg (.roundClear 0)
    (Function.update s (acc 2) (TreeBudgetWeightedTM2.weighted coord [true] mass))) _ at third
  rw [show s=state base P H u ap an par cap coord plus minus positive negative mass from rfl,
    state_mass] at third
  exact ⟨_,seq instructions (seq instructions first second) third⟩

def round_clear_run (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    Execution (cfg (.roundClear 0) (state base P H u ap an par cap coord plus minus positive negative mass))
      (cfg .loop (ready base P H u ap an positive negative mass)) := by
  let s := state base P H u ap an par cap coord plus minus positive negative mass
  let s1 := set s 15 []
  let s2 := set s1 16 []
  let s3 := set s2 17 []
  let s4 := set s3 18 []
  let s5 := set s4 19 []
  have a := clear_run instructions (.roundClear 0) (.roundClear 1) port(15,26) rfl s rfl
  have b := clear_run instructions (.roundClear 1) (.roundClear 2) port(16,26) rfl s1 rfl
  have c := clear_run instructions (.roundClear 2) (.roundClear 3) port(17,26) rfl s2 rfl
  have d := clear_run instructions (.roundClear 3) (.roundClear 4) port(18,26) rfl s3 rfl
  have e := clear_run instructions (.roundClear 4) .loop port(19,26) rfl s4 rfl
  have he : s5=ready base P H u ap an positive negative mass := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [s5,s4,s3,s2,s1,s,set,state,ready,reg]
  have run := seq instructions (seq instructions (seq instructions (seq instructions a b) c) d) e
  change Run instructions (cfg (.roundClear 0) s) (cfg .loop s5) _ at run
  rw [he] at run
  exact ⟨_,run⟩

def lookup_index_block (l next : PC) (i : Fin 3) (atRoot : Bool)
    (hi : instructions l=.lookup (lw i atRoot) next)
    (s : K → Bits) (xs : List ℕ) (j : ℕ) (hj : j<xs.length)
    (ht : s (tableReg i)=xs.flatMap encodeNat) (hn : s (indexReg atRoot)=j.bits)
    (hc : ∀ k, s (.inl k)=[]) (h₁ : s (reg 25)=[]) (h₂ : s (reg 23)=[]) :
    Execution (cfg l s) (cfg next (set s 23 xs[j].bits)) := by
  have run := TreeBudgetSemanticRegisterTM2.lookup_run instructions l next (lw i atRoot) hi s
    (xs.flatMap encodeNat) j.bits xs[j].bits _ (A4NaturalLookup.lookup_index xs j hj)
  rw [← ht,← hn,lookup_input s i atRoot hc h₁ h₂,
    lookup_output s i atRoot xs[j].bits hc h₁] at run
  exact ⟨_,run⟩

theorem clear_lookup_operands (s : K → Bits) (u v : Bits)
    (h₀ : s (reg 23)=[]) (h₁ : s (reg 26)=[]) (h₂ : s (reg 27)=[]) :
    set (set (set (set (set (set s 23 v) 26 u) 27 v) 23 []) 26 []) 27 []=s := by
  funext k
  by_cases h23 : k=reg 23
  · subst k; simp [set,reg,h₀]
  · by_cases h26 : k=reg 26
    · subst k; simp [set,reg,h₁]
    · by_cases h27 : k=reg 27
      · subst k; simp [set,reg,h₂]
      · simp [set,h23,h26,h27]

def lookup_fee_run (lookupPc copyU copyH clearPc weightedPc next : PC) (table which : Fin 3)
    (hlookup : instructions lookupPc=.lookup (lw table false) copyU)
    (hu : instructions copyU=.copy (operandPort 17 26 (by decide)) false copyH)
    (hh : instructions copyH=.copy (operandPort 23 27 (by decide)) false clearPc)
    (hclear : instructions clearPc=.clear ⟨reg 23,reg 24,reg 31,by decide,by decide,by decide⟩ weightedPc)
    (hweighted : instructions weightedPc=.weighted (mw which) next)
    (s : K → Bits) (xs : List ℕ) (j : ℕ) (hj : j<xs.length)
    (ht : s (tableReg table)=xs.flatMap encodeNat) (hn : s (indexReg false)=j.bits)
    (hc : ∀ k, s (.inl k)=[]) (h₀ : s (reg 23)=[]) (hs : s (reg 24)=[])
    (hl : s (reg 25)=[]) (h₁ : s (reg 26)=[]) (h₂ : s (reg 27)=[])
    (h₃ : s (reg 28)=[]) (h₄ : s (reg 29)=[]) :
    Execution (cfg lookupPc s)
      (cfg next (Function.update s (acc which)
        (TreeBudgetWeightedTM2.weighted (s (reg 17)) xs[j].bits (s (acc which))))) := by
  let u := s (reg 17)
  let v := xs[j].bits
  have look := lookup_index_block lookupPc copyU table false hlookup s xs j hj ht hn hc hl h₀
  have first := copy_run instructions copyU copyH (operandPort 17 26 (by decide)) false hu
    (set s 23 v) (by simp [operandPort,set,reg,hs])
  have second := copy_run instructions copyH clearPc (operandPort 23 27 (by decide)) false hh
    (set (set s 23 v) 26 u) (by simp [operandPort,set,reg,hs])
  have clear := clear_run instructions clearPc weightedPc
    ⟨reg 23,reg 24,reg 31,by decide,by decide,by decide⟩ hclear
    (set (set (set s 23 v) 26 u) 27 v) (by simp [set,reg,hs])
  have last := weighted_block weightedPc next which hweighted
    (set (set (set (set s 23 v) 26 u) 27 v) 23 [])
    (by simp [set,reg,h₃]) (by simp [set,reg,h₄])
  simp [operandPort,source,reg,set,h₁,h₂] at first second clear
  change Run instructions (cfg copyU (set s 23 v))
    (cfg copyH (set (set s 23 v) 26 u)) (2*u.length+3) at first
  change Run instructions (cfg copyH (set (set s 23 v) 26 u))
    (cfg clearPc (set (set (set s 23 v) 26 u) 27 v)) (2*v.length+3) at second
  change Run instructions (cfg clearPc (set (set (set s 23 v) 26 u) 27 v))
    (cfg weightedPc (set (set (set (set s 23 v) 26 u) 27 v) 23 [])) (v.length+2) at clear
  rw [set_acc _ _ _ (by decide),set_acc _ _ _ (by decide),
    set_acc _ _ _ (by decide),set_acc _ _ _ (by decide)] at last
  rw [clear_lookup_operands s u v h₀ h₁ h₂] at last
  simp only [set,Function.update_self,Function.update_of_ne (show reg 26≠reg 23 by decide),
    Function.update_of_ne (show reg 26≠reg 27 by decide),
    Function.update_of_ne (show reg 27≠reg 23 by decide)] at last
  exact ⟨_,seq instructions (seq instructions (seq instructions (seq instructions look.property first) second) clear) last⟩

def parent_test_run (base : K → Bits) (P H u ap an cap plus minus positive negative mass : Bits)
    (rows : List ℕ) (parent coord : ℕ) (hp : parent<rows.length)
    (hr : base (reg 2)=rows.flatMap encodeNat) :
    Execution (cfg .parentNonzero
      (state base P H u ap an parent.bits cap coord.bits plus minus positive negative mass))
      (cfg (if coord=0 then .roundClear 0 else if rows[parent]=0 then bad else .parentPosLookup)
        (state base P H u ap an parent.bits cap coord.bits plus minus positive negative mass)) := by
  let s := state base P H u ap an parent.bits cap coord.bits plus minus positive negative mass
  have first := test_run instructions .parentNonzero (.roundClear 0) .parentLookup (reg 17) rfl s
  change Run instructions (cfg .parentNonzero s)
    (cfg (if coord.bits.isEmpty then .roundClear 0 else .parentLookup) s) 1 at first
  simp only [TreeBudgetIntTM2.bits_empty_iff] at first
  by_cases hz : coord=0
  · exact ⟨_, by simpa only [if_pos hz] using first⟩
  · simp only [if_neg hz] at first
    have lookup := lookup_index_block .parentLookup .parentTest 0 false rfl s rows parent hp hr rfl
      (by intro k; rfl) rfl rfl
    have test := test_run instructions .parentTest bad .parentClear (reg 23) rfl (set s 23 rows[parent].bits)
    change Run instructions (cfg .parentTest (set s 23 rows[parent].bits))
      (cfg (if rows[parent].bits.isEmpty then bad else .parentClear) (set s 23 rows[parent].bits)) 1 at test
    simp only [TreeBudgetIntTM2.bits_empty_iff] at test
    by_cases hparent : rows[parent]=0
    · simp only [if_pos hparent] at test
      have hs : set s 23 rows[parent].bits=s := by
        rw [hparent]
        change Function.update s (reg 23) (s (reg 23))=s
        simp
      have run := seq instructions (seq instructions first lookup.property) test
      exact ⟨_, by simpa only [if_neg hz,if_pos hparent,hs] using run⟩
    · simp only [if_neg hparent] at test
      have clear := clear_run instructions .parentClear .parentPosLookup
        ⟨reg 23,reg 24,reg 26,by decide,by decide,by decide⟩ rfl
        (set s 23 rows[parent].bits) (by simp [set,reg,s,state])
      have hs : Function.update (set s 23 rows[parent].bits) (reg 23) []=s := by
        simp only [set,Function.update_idem]
        change Function.update s (reg 23) (s (reg 23))=s
        simp
      rw [hs] at clear
      have run := seq instructions (seq instructions (seq instructions first lookup.property) test) clear
      exact ⟨_, by simpa only [if_neg hz,if_neg hparent] using run⟩

def parent_fees_run (base : K → Bits) (P H u ap an cap coord plus minus positive negative mass : Bits)
    (Ap An : List ℕ) (parent : ℕ) (hp : parent<Ap.length) (hn : parent<An.length)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat) :
    Execution (cfg .parentPosLookup
      (state base P H u ap an parent.bits cap coord plus minus positive negative mass))
      (cfg (.roundClear 0) (state base P H u ap an parent.bits cap coord plus minus
        (TreeBudgetWeightedTM2.weighted coord Ap[parent].bits positive)
        (TreeBudgetWeightedTM2.weighted coord An[parent].bits negative) mass)) := by
  let s := state base P H u ap an parent.bits cap coord plus minus positive negative mass
  have first := lookup_fee_run .parentPosLookup .parentPosU .parentPosH .parentPosClear .parentPosRun
    .parentNegLookup 1 0 rfl rfl rfl rfl rfl s Ap parent hp hap rfl
    (by intro k; rfl) rfl rfl rfl rfl rfl rfl rfl
  have firstProp := first.property
  change Run instructions _ (cfg .parentNegLookup (Function.update s (acc 0)
    (TreeBudgetWeightedTM2.weighted coord Ap[parent].bits positive))) first.val at firstProp
  dsimp only [s] at firstProp
  rw [state_positive] at firstProp
  let s' := state base P H u ap an parent.bits cap coord plus minus
    (TreeBudgetWeightedTM2.weighted coord Ap[parent].bits positive) negative mass
  have second := lookup_fee_run .parentNegLookup .parentNegU .parentNegH .parentNegClear .parentNegRun
    (.roundClear 0) 2 1 rfl rfl rfl rfl rfl s' An parent hn han rfl
    (by intro k; rfl) rfl rfl rfl rfl rfl rfl rfl
  have secondProp := second.property
  change Run instructions _ (cfg (.roundClear 0) (Function.update s' (acc 1)
    (TreeBudgetWeightedTM2.weighted coord An[parent].bits negative))) second.val at secondProp
  dsimp only [s'] at secondProp
  rw [state_negative] at secondProp
  exact ⟨_, seq instructions firstProp secondProp⟩

end UAVProof.A4RowCheck
