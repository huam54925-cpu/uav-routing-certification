import LeanCompletion.UAV.TreeBudgetColumnCheckLoop
import LeanCompletion.UAV.TreeBudgetColumnCheckComparisons

namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open A4ColumnAccumulator Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def root_branch (s : Input) (r v : ℕ) (h t : Bits) (hr : s.root=r.bits) :
    Run (cfg .rootA (state s v.bits h t [] []))
      (cfg (if v=r then .clearTarget else .records) (state s v.bits h t [] []))
      (6*(v.bits.length+r.bits.length)+18) := by
  let d := state s v.bits h t [] []
  have a := root_le d rfl rfl rfl rfl rfl
  have b := root_ge d rfl rfl rfl rfl rfl
  change Run (cfg .rootA d) (cfg (if value v.bits≤value s.root then .rootBackA else .records) d)
    (3*(v.bits.length+s.root.length)+9) at a
  change Run (cfg .rootBackA d) (cfg (if value s.root≤value v.bits then .clearTarget else .records) d)
    (3*(s.root.length+v.bits.length)+9) at b
  rw [hr,value_bits,value_bits] at a b
  by_cases hvr : v≤r
  · rw [if_pos hvr] at a
    have he : (r≤v)↔v=r := by omega
    simp only [he] at b
    convert seq a b using 1 <;> omega
  · rw [if_neg hvr] at a
    have hne : v≠r := by omega
    rw [if_neg hne]
    exact weaken a (by omega)

def sum_branch (s : Input) (v : ℕ) (h t a : Bits) :
    Run (cfg .sumA (state s v.bits h t [] a))
      (cfg (if value a=value t then .clearTarget else .bad) (state s v.bits h t [] a))
      (6*(a.length+t.length)+18) := by
  let d := state s v.bits h t [] a
  have x := sum_le d rfl rfl rfl rfl rfl
  have y := sum_ge d rfl rfl rfl rfl rfl
  simp only [d,state] at x y
  by_cases hle : value a≤value t
  · rw [if_pos hle] at x
    have he : (value t≤value a)↔value a=value t := by omega
    simp only [he] at y
    convert seq x y using 1 <;> omega
  · rw [if_neg hle] at x
    have hne : value a≠value t := by omega
    rw [if_neg hne]
    exact weaken x (by omega)

def cleanup_round (s : Input) (v : ℕ) (h t a : Bits) :
    Run (cfg .clearTarget (state s v.bits h t [] a))
      (cfg .column (state s (v+1).bits h [] [] []))
      (t.length+a.length+2*v.bits.length+7) := by
  let d0 := state s v.bits h t [] a
  let d1 := put d0 (wr .target) []
  let d2 := put d1 (wr .acc) []
  let d3 := put d2 (wr .index) (v+1).bits
  have x : Run (cfg .clearTarget d0) (cfg .increment d1) (t.length+2) :=
    clearData .clearTarget .increment _ rfl d0 rfl
  have y : Run (cfg .increment d1) (cfg .finish d2) (a.length+2) :=
    clearData .increment .finish _ rfl d1 rfl
  have z : Run (cfg .finish d2) (cfg .column d3) (2*v.bits.length+3) := by
    simpa [d0,d1,d2,d3,state,store,put,Function.update_apply,TreeBudgetStackRoutine.increment_bits]
      using incData .finish .column _ rfl d2 rfl
  have he : d3=state s (v+1).bits h [] [] [] := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d0,d1,d2,d3,state,put,Function.update_apply]
  rw [he] at z
  convert seq (seq x y) z using 1 <;> omega

def columns (r v : ℕ) (xs : RawCertificate) : List ℕ → Bool
  | [] => true
  | h::hs => (decide (v=r) || decide (columnSum v xs=h)) && columns r (v+1) xs hs

def output (s : Input) (r v : ℕ) (xs : RawCertificate) : List ℕ → Cfg
  | [] => TreeBudgetSemanticRegisterTM2.stopped (store (state s v.bits [] [] [] []))
  | h::hs =>
    if v=r ∨ columnSum v xs=h then output s r (v+1) xs hs
    else ⟨none,(none,false),store (state s v.bits (hs.flatMap encodeNat) h.bits [] (columnWord v xs []))⟩

theorem columns_true_iff (r v : ℕ) (xs : RawCertificate) (hs : List ℕ) :
    columns r v xs hs=true ↔
      ∀ i, i<hs.length → v+i≠r → columnSum (v+i) xs=hs[i]?.getD 0 := by
  induction hs generalizing v with
  | nil => simp [columns]
  | cons h hs ih =>
    simp only [columns,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨head,tail⟩ i hi hne
      cases i with
      | zero =>
        have hv : v≠r := by simpa using hne
        simpa using head.resolve_left hv
      | succ i =>
        have hv : v+1+i≠r := by omega
        simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using tail i (by simpa using hi) hv
    · intro all
      constructor
      · by_cases hv : v=r
        · exact Or.inl hv
        · exact Or.inr (by simpa using all 0 (by simp) (by simpa using hv))
      · intro i hi hne
        have hv : v+(i+1)≠r := by omega
        simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using all (i+1) (by simpa using hi) hv

theorem output_layout (s : Input) (r v : ℕ) (xs : RawCertificate) (hs : List ℕ) :
    (output s r v xs hs).l=none ∧ (output s r v xs hs).var.2=columns r v xs hs ∧
    (output s r v xs hs).stk (wr .body)=s.body ∧
    (output s r v xs hs).stk (wr .tokens)=s.tokens ∧
    (output s r v xs hs).stk (wr .root)=s.root ∧
    (output s r v xs hs).stk (wr .targets)=s.targets ∧
    (output s r v xs hs).stk (wr .ctx)=s.ctx := by
  induction hs generalizing v with
  | nil => simp [output,columns,TreeBudgetSemanticRegisterTM2.stopped,store,state]
  | cons h hs ih =>
    by_cases hr : v=r
    · simpa [output,columns,hr] using ih (v+1)
    · by_cases hc : columnSum v xs=h
      · simpa [output,columns,hc] using ih (v+1)
      · simp [output,columns,hr,hc,store,state]

def columns_run (s : Input) (r v : ℕ) (xs : RawCertificate) (hs : List ℕ) (B : ℕ)
    (hbody : s.body=xs.flatMap encodeEntry) (hroot : s.root=r.bits)
    (hrows : ∀ e∈xs, v+hs.length≤e.2.length)
    (hb : (xs.flatMap encodeEntry).length≤B) (hh : (hs.flatMap encodeNat).length≤B)
    (hn : v+hs.length≤B) (hr : r.bits.length≤B) :
    Run (cfg .column (state s v.bits (hs.flatMap encodeNat) [] [] []))
      (output s r v xs hs) (8192*hs.length*(B+1)^3+2) := by
  induction hs generalizing v with
  | nil =>
    have a := testData .column .done .readTarget (wr .htail) rfl (state s v.bits [] [] [] [])
    have b := TreeBudgetSemanticRegisterTM2.halt_run code .done rfl (store (state s v.bits [] [] [] []))
    simpa [state,store,output,cfg] using seq a b
  | cons h hs ih =>
    have hv : v.bits.length≤B := by
      have hv' : v.bits.length≤v := by
        simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr v.lt_two_pow_self : v.size≤v)
      simp only [List.length_cons] at hn
      omega
    have hhead : h.bits.length≤B := by
      have hh' := hh
      simp only [List.flatMap_cons,List.length_append,encodeNat,word_length] at hh'
      omega
    have htail : (hs.flatMap encodeNat).length≤B := by
      simp only [List.flatMap_cons,List.length_append] at hh
      omega
    have hnext : v+1+hs.length≤B := by simp only [List.length_cons] at hn; omega
    have next := ih (v+1) (by
      intro e he
      have hh := hrows e he
      simp only [List.length_cons] at hh
      omega) htail hnext
    let d0 := state s v.bits ((h::hs).flatMap encodeNat) [] [] []
    let d1 := state s v.bits (hs.flatMap encodeNat) h.bits [] []
    have test := testData .column .done .readTarget (wr .htail) rfl d0
    have ht : (store d0 (wr .htail)).isEmpty=false := by
      change (word h.bits++hs.flatMap encodeNat).isEmpty=false
      cases h.bits <;> rfl
    simp only [ht,Bool.false_eq_true,ite_false] at test
    have read : Run (cfg .readTarget d0) (cfg .rootA d1) (3*h.bits.length+3) := by
      have read := readData .readTarget .rootA _ rfl d0 h.bits (hs.flatMap encodeNat) rfl rfl rfl
      convert read using 1
      congr 1
      apply data_ext
      · rfl
      · funext k; cases k <;> simp [d0,d1,state,put,Function.update_apply]
    have branch := root_branch s r v (hs.flatMap encodeNat) h.bits hroot
    have head := seq (seq test read) branch
    by_cases heq : v=r
    · rw [if_pos heq] at head
      have cleanup := cleanup_round s v (hs.flatMap encodeNat) h.bits []
      have allRun := seq (seq head cleanup) next
      have hout : output s r v xs (h::hs)=output s r (v+1) xs hs := by simp [output,heq]
      rw [hout]
      apply weaken allRun
      simp only [List.length_cons,List.length_nil]
      nlinarith [Nat.zero_le (B^3),Nat.zero_le (B^2)]
    · rw [if_neg heq] at head
      let d2 := state s v.bits (hs.flatMap encodeNat) h.bits (xs.flatMap encodeEntry) []
      have copy : Run (cfg .records d1) (cfg .entry d2) (2*(xs.flatMap encodeEntry).length+3) := by
        have copy := copyData .records .entry _ rfl d1 rfl
        convert copy using 1
        · congr 1
          apply data_ext
          · rfl
          · funext k; cases k <;> simp [d1,d2,state,put,store,Function.update_apply,hbody]
        · simp [d1,store,state,hbody]
      have hacc : countWidth xs+max ([] : Bits).length (coordMax v xs)≤B := by
        have h := occupied_width v xs
        simp only [List.length_nil,Nat.zero_max]
        omega
      have scan := records_loop s v (hs.flatMap encodeNat) h.bits xs [] B
        (by intro e he; have hh := hrows e he; simp only [List.length_cons] at hh; omega)
        hb hv hacc
      let a := columnWord v xs []
      have ha : a.length≤B := (columnWord_body_bound v xs).trans hb
      have hvalue : value a=columnSum v xs := by simp [a,columnWord_value,value]
      have compare := sum_branch s v (hs.flatMap encodeNat) h.bits a
      simp only [value_bits,hvalue] at compare
      have middle := seq (seq (seq head copy) scan) compare
      have hk : xs.length≤B := (length_le_flatMap encodeEntry encodeEntry_nonempty xs).trans hb
      have htime :
          1+(3*h.bits.length+3)+(6*(v.bits.length+r.bits.length)+18)+
            (2*(xs.flatMap encodeEntry).length+3)+(4096*xs.length*(B+1)^2+1)+
            (6*(a.length+h.bits.length)+18)+(h.bits.length+a.length+2*v.bits.length+7)
            ≤8192*(B+1)^3 := by
        have hk' := Nat.mul_le_mul_right ((B+1)^2) (Nat.mul_le_mul_left 4096 hk)
        have hp := Nat.pow_le_pow_left (show 1≤B+1 by omega) 2
        nlinarith
      by_cases hsum : columnSum v xs=h
      · rw [if_pos hsum] at middle
        have cleanup := cleanup_round s v (hs.flatMap encodeNat) h.bits a
        have allRun := seq (seq middle cleanup) next
        have hout : output s r v xs (h::hs)=output s r (v+1) xs hs := by simp [output,hsum]
        rw [hout]
        apply weaken allRun
        simp only [List.length_cons]
        nlinarith
      · rw [if_neg hsum] at middle
        have last := TreeBudgetSemanticRegisterTM2.fail_run code .bad rfl
          (store (state s v.bits (hs.flatMap encodeNat) h.bits [] a))
        have allRun := seq middle last
        have hout : output s r v xs (h::hs)=
            ⟨none,(none,false),store (state s v.bits (hs.flatMap encodeNat) h.bits [] a)⟩ := by
          simp [output,heq,hsum,a]
        rw [hout]
        apply weaken allRun
        simp only [List.length_cons]
        nlinarith [Nat.pow_le_pow_left (show 1≤B+1 by omega) 3]

def check_run (s : Input) (r : ℕ) (xs : RawCertificate) (H : List ℕ)
    (hbody : s.body=xs.flatMap encodeEntry) (hroot : s.root=r.bits)
    (htargets : s.targets=H.flatMap encodeNat)
    (hrows : ∀ e∈xs, e.2.length=H.length) :
    Run (start s) (output s r 0 xs H)
      (16384*(s.body.length+s.targets.length+s.root.length+1)^4) := by
  let B := s.body.length+s.targets.length+s.root.length
  have hb : (xs.flatMap encodeEntry).length≤B := by dsimp [B]; rw [← hbody]; omega
  have hh : (H.flatMap encodeNat).length≤B := by dsimp [B]; rw [← htargets]; omega
  have hn : H.length≤B := (length_le_flatMap encodeNat encodeNat_nonempty H).trans hh
  have hr : r.bits.length≤B := by dsimp [B]; rw [← hroot]; omega
  have first := copyData .prepare .column _ rfl (state s [] [] [] [] []) rfl
  have he : put (state s [] [] [] [] []) (wr .htail) (s.targets++[])=
      state s [] (H.flatMap encodeNat) [] [] [] := by
    apply data_ext
    · rfl
    · funext k; cases k <;> simp [state,put,Function.update_apply,htargets]
  change Run (start s)
    (cfg .column (put (state s [] [] [] [] []) (wr .htail) (s.targets++[])))
    (2*s.targets.length+3) at first
  rw [he] at first
  have rest := columns_run s r 0 xs H B hbody hroot
    (by intro e he; simp [hrows e he]) hb hh (by simpa using hn) hr
  have allRun := seq first rest
  apply weaken allRun
  have hn' := Nat.mul_le_mul_right ((B+1)^3) (Nat.mul_le_mul_left 8192 hn)
  have htargets' : s.targets.length≤B := by dsimp [B]; omega
  change 2*s.targets.length+3+(8192*H.length*(B+1)^3+2)≤16384*(B+1)^4
  nlinarith [Nat.pow_le_pow_left (show 1≤B+1 by omega) 3]

end UAVProof.A4ColumnCheck
