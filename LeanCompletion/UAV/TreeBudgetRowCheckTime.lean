import LeanCompletion.UAV.TreeBudgetRowCheckTotal
import LeanCompletion.UAV.TreeBudgetRowCheckCosts

/-! Explicit uniform polynomial transition bound for `A4RowCheck.row_run`. -/
namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2 TreeBudgetWeightedTM2 A4RowCheckModel TreeBudgetParentArray
open TreeBudgetVectorChecker TreeBudgetCostedCandidates

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem bits_len_le_flatMap (xs : List ℕ) (i : ℕ) (hi : i<xs.length) :
    xs[i].bits.length≤(xs.flatMap encodeNat).length := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero,List.flatMap_cons,List.length_append,
        encodeNat_length,Nat.size_eq_bits_len]
      omega
    | succ i =>
      simp only [List.length_cons] at hi
      have h := ih i (by omega)
      simp only [List.getElem_cons_succ,List.flatMap_cons,List.length_append]
      omega

theorem length_le_flatMap_nat (xs : List ℕ) : xs.length≤(xs.flatMap encodeNat).length :=
  length_le_flatMap encodeNat encodeNat_nonempty xs

theorem coordSum_le_body (vs : List Node) :
    2*(vs.map fun v => v.coord.bits.length).sum≤(body vs Node.coord).length := by
  induction vs with
  | nil => simp [body]
  | cons v vs ih =>
    simp only [body,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,
      encodeNat_length,Nat.size_eq_bits_len] at ih ⊢
    omega

theorem workSize_le (s : K → Bits) (M : ℕ)
    (h : ∀ k : Fin 35, 10≤k.val → (s (reg k)).length≤M) : workSize s≤35*M := by
  unfold workSize
  calc
    ∑ k : Fin 35, (if 10≤k.val then (s (reg k)).length else 0)
      ≤ ∑ _k : Fin 35, M := Finset.sum_le_sum fun k _ => by
        split_ifs with hk
        · exact h k hk
        · exact Nat.zero_le M
    _ = 35*M := by simp

theorem workSize_state_le (base : K → Bits) (P H u ap an par cap coord plus minus pos neg mass : Bits)
    (M : ℕ) (hP : P.length≤M) (hH : H.length≤M) (hu : u.length≤M) (hap : ap.length≤M)
    (han : an.length≤M) (hpar : par.length≤M) (hcap : cap.length≤M) (hcoord : coord.length≤M)
    (hplus : plus.length≤M) (hminus : minus.length≤M) (hpos : pos.length≤M)
    (hneg : neg.length≤M) (hmass : mass.length≤M) :
    workSize (state base P H u ap an par cap coord plus minus pos neg mass)≤35*M := by
  apply workSize_le
  intro k hk
  fin_cases k <;> simp_all [state,reg]

theorem cleanup_state_val (base : K → Bits) (P H u ap an par cap coord plus minus pos neg mass : Bits)
    (b : Bool) (M : ℕ) (hP : P.length≤M) (hH : H.length≤M) (hu : u.length≤M) (hap : ap.length≤M)
    (han : an.length≤M) (hpar : par.length≤M) (hcap : cap.length≤M) (hcoord : coord.length≤M)
    (hplus : plus.length≤M) (hminus : minus.length≤M) (hpos : pos.length≤M)
    (hneg : neg.length≤M) (hmass : mass.length≤M) :
    (cleanup_state_run base P H u ap an par cap coord plus minus pos neg mass b).val≤875*M+51 := by
  dsimp [cleanup_state_run]
  have hw := workSize_state_le base P H u ap an par cap coord plus minus pos neg mass M
    hP hH hu hap han hpar hcap hcoord hplus hminus hpos hneg hmass
  omega

theorem read_fields_val (base : K → Bits) (ps hs us aps ans positive negative mass : Bits)
    (parent H u ap an : ℕ) :
    (read_fields base ps hs us aps ans positive negative mass parent H u ap an).val=
      3*(parent.bits.length+H.bits.length+u.bits.length+ap.bits.length+an.bits.length)+16 := by
  dsimp [read_fields]
  omega

theorem cap_run_val (base : K → Bits) (P H u ap an par plus minus positive negative mass : Bits)
    (cap coord : ℕ) :
    (cap_run base P H u ap an par plus minus positive negative mass cap coord).val=
      3*(coord.bits.length+cap.bits.length)+9 := by
  simpa [cap_run] using compare_saved_val .capU .capH .capCompare .selfPosU bad 17 16 rfl rfl rfl
    (state base P H u ap an par cap.bits coord.bits plus minus positive negative mass) rfl rfl rfl rfl rfl

theorem self_run_val (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    (self_run base P H u ap an par cap coord plus minus positive negative mass).val=
      4*coord.length+2*(plus.length+minus.length)+
        16*(coord.length+plus.length+positive.length+1)^2+
        16*(coord.length+minus.length+negative.length+1)^2+18 := by
  dsimp [self_run]
  have h₁ := weighted_saved_val .selfPosU .selfPosH .selfPosRun .selfNegU 17 18 0 rfl rfl rfl
    (state base P H u ap an par cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl
  have h₂ := weighted_saved_val .selfNegU .selfNegH .selfNegRun .parentLeft 17 19 1 rfl rfl rfl
    (state base P H u ap an par cap coord plus minus
      (weighted coord plus positive) negative mass) rfl rfl rfl rfl rfl
  simp only [source,acc,state,reg] at h₁ h₂
  omega

theorem parent_choice_val (base : K → Bits) (P H u ap an cap coord plus minus positive negative mass : Bits)
    (parent root : ℕ) (hr : base (reg 5)=root.bits) :
    (parent_choice base P H u ap an cap coord plus minus positive negative mass parent root hr).val≤
      6*(parent.bits.length+root.bits.length)+18 := by
  dsimp only [parent_choice,id]
  have h₁ := compare_saved_val .parentLeft .rootRight .parentLEroot .rootLeft .parentNonzero 15 5 rfl rfl rfl
    (state base P H u ap an parent.bits cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl
  have h₂ := compare_saved_val .rootLeft .parentRight .rootLEparent .rootAddU .parentNonzero 5 15 rfl rfl rfl
    (state base P H u ap an parent.bits cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl
  simp [source,state,reg,hr] at h₁ h₂
  by_cases hpr : parent≤root
  · simp only [hpr,↓reduceDIte]
    change (compare_saved .parentLeft .rootRight .parentLEroot .rootLeft .parentNonzero 15 5 rfl rfl rfl
      (state base P H u ap an parent.bits cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl).val+
      (compare_saved .rootLeft .parentRight .rootLEparent .rootAddU .parentNonzero 5 15 rfl rfl rfl
      (state base P H u ap an parent.bits cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl).val≤_
    rw [h₁,h₂]
    omega
  · simp only [hpr,↓reduceDIte]
    change (compare_saved .parentLeft .rootRight .parentLEroot .rootLeft .parentNonzero 15 5 rfl rfl rfl
      (state base P H u ap an parent.bits cap coord plus minus positive negative mass) rfl rfl rfl rfl rfl).val≤_
    rw [h₁]
    omega

theorem root_mass_val (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    (root_mass_run base P H u ap an par cap coord plus minus positive negative mass).val=
      2*coord.length+16*(coord.length+[true].length+mass.length+1)^2+7 := by
  change ((2*coord.length+3)+1)+(16*(coord.length+[true].length+mass.length+1)^2+3)=_
  omega

theorem round_clear_val (base : K → Bits) (P H u ap an par cap coord plus minus positive negative mass : Bits) :
    (round_clear_run base P H u ap an par cap coord plus minus positive negative mass).val=
      par.length+cap.length+coord.length+plus.length+minus.length+10 := by
  change ((((par.length+2)+(cap.length+2))+(coord.length+2))+(plus.length+2))+(minus.length+2)=_
  omega

theorem lookup_index_block_val (l next : PC) (i : Fin 3) (atRoot : Bool)
    (hi : instructions l=.lookup (lw i atRoot) next)
    (s : K → Bits) (xs : List ℕ) (j : ℕ) (hj : j<xs.length)
    (ht : s (tableReg i)=xs.flatMap encodeNat) (hn : s (indexReg atRoot)=j.bits)
    (hc : ∀ k, s (.inl k)=[]) (h₁ : s (reg 25)=[]) (h₂ : s (reg 23)=[]) :
    (lookup_index_block l next i atRoot hi s xs j hj ht hn hc h₁ h₂).val=
      256*((s (tableReg i)).length+(s (indexReg atRoot)).length+1)^2+2 := rfl

theorem lookup_fee_val (lookupPc copyU copyH clearPc weightedPc next : PC) (table which : Fin 3)
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
    (lookup_fee_run lookupPc copyU copyH clearPc weightedPc next table which
      hlookup hu hh hclear hweighted s xs j hj ht hn hc h₀ hs hl h₁ h₂ h₃ h₄).val=
      256*((xs.flatMap encodeNat).length+j.bits.length+1)^2+
        2*(s (reg 17)).length+3*xs[j].bits.length+
        16*((s (reg 17)).length+xs[j].bits.length+(s (acc which)).length+1)^2+13 := by
  change ((((lookup_index_block lookupPc copyU table false hlookup s xs j hj ht hn hc hl h₀).val+
    (2*(s (reg 17)).length+3))+(2*xs[j].bits.length+3))+(xs[j].bits.length+2))+
    (16*((s (reg 17)).length+xs[j].bits.length+(s (acc which)).length+1)^2+3)=_
  rw [lookup_index_block_val,ht,hn]
  omega

theorem parent_test_val (base : K → Bits) (P H u ap an cap plus minus positive negative mass : Bits)
    (rows : List ℕ) (parent coord : ℕ) (hp : parent<rows.length)
    (hr : base (reg 2)=rows.flatMap encodeNat) :
    (parent_test_run base P H u ap an cap plus minus positive negative mass rows parent coord hp hr).val≤
      256*((rows.flatMap encodeNat).length+parent.bits.length+1)^2+rows[parent].bits.length+6 := by
  dsimp only [parent_test_run,id]
  by_cases hz : coord=0
  · simp only [hz,↓reduceDIte]
    change 1≤_
    omega
  · simp only [hz,↓reduceDIte]
    by_cases hparent : rows[parent]=0
    · simp only [hparent,↓reduceDIte]
      change (1+(256*((base (reg 2)).length+parent.bits.length+1)^2+2))+1≤_
      rw [hr]
      omega
    · simp only [hparent,↓reduceDIte]
      change ((1+(256*((base (reg 2)).length+parent.bits.length+1)^2+2))+1)+(rows[parent].bits.length+2)≤_
      rw [hr]
      omega

theorem parent_fees_val (base : K → Bits) (P H u ap an cap coord plus minus positive negative mass : Bits)
    (Ap An : List ℕ) (parent : ℕ) (hp : parent<Ap.length) (hn : parent<An.length)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat) :
    (parent_fees_run base P H u ap an cap coord plus minus positive negative mass Ap An parent hp hn hap han).val=
      (256*((Ap.flatMap encodeNat).length+parent.bits.length+1)^2+
        2*coord.length+3*Ap[parent].bits.length+
        16*(coord.length+Ap[parent].bits.length+positive.length+1)^2+13)+
      (256*((An.flatMap encodeNat).length+parent.bits.length+1)^2+
        2*coord.length+3*An[parent].bits.length+
        16*(coord.length+An[parent].bits.length+negative.length+1)^2+13) := by
  dsimp [parent_fees_run]
  rw [lookup_fee_val,lookup_fee_val]
  simp [state,reg,acc]

theorem mass_left_val (s : K → Bits) (hs : s (reg 24)=[]) (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    (mass_left_run s hs h₁ h₂ h₃ h₄).val=3*(s (reg 22)).length+8 := by
  dsimp [mass_left_run]
  omega

theorem mass_right_val (s : K → Bits) (hs : s (reg 24)=[]) (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    (mass_right_run s hs h₁ h₂ h₃ h₄).val=3*(s (reg 22)).length+8 := by
  dsimp [mass_right_run]
  omega

theorem final_test_val (base : K → Bits) (positive negative mass : Bits) :
    (final_test_run base positive negative mass).val≤
      6*mass.length+3*(positive.length+negative.length)+25 := by
  let s := ready base [] [] [] [] [] positive negative mass
  have hml := mass_left_val s rfl rfl rfl rfl rfl
  have hmr := mass_right_val s rfl rfl rfl rfl rfl
  have hb := compare_saved_val .budgetLeft .budgetRight .budgetCompare good bad
    20 21 rfl rfl rfl s rfl rfl rfl rfl rfl
  dsimp only [final_test_run,id]
  by_cases hlo : value mass≤1
  · simp only [hlo,↓reduceDIte]
    by_cases hhi : 1≤value mass
    · simp only [hhi,↓reduceDIte]
      by_cases hbd : value positive≤value negative
      · simp only [hbd,↓reduceDIte]
        change ((mass_left_run s rfl rfl rfl rfl rfl).val+
          (mass_right_run s rfl rfl rfl rfl rfl).val)+
          (compare_saved .budgetLeft .budgetRight .budgetCompare good bad 20 21 rfl rfl rfl s rfl rfl rfl rfl rfl).val≤_
        rw [hml,hmr,hb]; simp [s,source,ready,state,reg]; omega
      · simp only [hbd,↓reduceDIte]
        change ((mass_left_run s rfl rfl rfl rfl rfl).val+
          (mass_right_run s rfl rfl rfl rfl rfl).val)+
          (compare_saved .budgetLeft .budgetRight .budgetCompare good bad 20 21 rfl rfl rfl s rfl rfl rfl rfl rfl).val≤_
        rw [hml,hmr,hb]; simp [s,source,ready,state,reg]; omega
    · simp only [hhi,↓reduceDIte]
      change (mass_left_run s rfl rfl rfl rfl rfl).val+
        (mass_right_run s rfl rfl rfl rfl rfl).val≤_
      rw [hml,hmr]; simp [s,ready,state,reg]; omega
  · simp only [hlo,↓reduceDIte]
    change (mass_left_run s rfl rfl rfl rfl rfl).val≤_
    rw [hml]; simp [s,ready,state,reg]; omega

theorem final_run_val (base : K → Bits) (positive negative mass : Bits) (M : ℕ)
    (hpos : positive.length≤M) (hneg : negative.length≤M) (hmass : mass.length≤M) :
    (final_run base positive negative mass).val≤1024*(M+1) := by
  dsimp only [final_run,id]
  have ht := final_test_val base positive negative mass
  have hc := cleanup_state_val base [] [] [] [] [] [] [] [] [] [] positive negative mass
    (decide (value mass=1 ∧ value positive≤value negative)) M
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    hpos hneg hmass
  change (1+(final_test_run base positive negative mass).val)+
    (cleanup_state_run base [] [] [] [] [] [] [] [] [] [] positive negative mass _).val≤_
  omega

theorem vertex_run_val (base : K → Bits) (rows Ap An : List ℕ) (root : ℕ)
    (hr : base (reg 5)=root.bits) (hrow : base (reg 2)=rows.flatMap encodeNat)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat)
    (v : Node) (vs : List Node) (q : WordState)
    (hp : v.parent<rows.length) (hpA : v.parent<Ap.length) (hpN : v.parent<An.length)
    (B W : ℕ)
    (hBrows : (rows.flatMap encodeNat).length≤W)
    (hBAp : (Ap.flatMap encodeNat).length≤B)
    (hBAn : (An.flatMap encodeNat).length≤B)
    (hBroot : root.bits.length≤B)
    (hbP : (body vs Node.parent).length≤B) (hbH : (body vs Node.cap).length≤B)
    (hbU : (body vs Node.coord).length≤W) (hbAp : (body vs Node.plus).length≤B)
    (hbAn : (body vs Node.minus).length≤B)
    (hvPar : v.parent.bits.length≤B) (hvCap : v.cap.bits.length≤B)
    (hvCoord : 2*v.coord.bits.length≤W) (hvPlus : v.plus.bits.length≤B)
    (hvMinus : v.minus.bits.length≤B)
    (hq1 : q.1.length+2*v.coord.bits.length≤ max B 1+W)
    (hq2 : q.2.1.length+2*v.coord.bits.length≤ max B 1+W)
    (hq3 : q.2.2.length+2*v.coord.bits.length≤ max B 1+W) :
    (vertex_run base rows Ap An root hr hrow hap han v vs q hp hpA hpN).val≤
      4096*(B+W+1)^2 := by
  let M := B+W+1
  have hq1_le : q.1.length≤M := by omega
  have hq2_le : q.2.1.length≤M := by omega
  have hq3_le : q.2.2.length≤M := by omega
  have hcoord_le : v.coord.bits.length≤W := by omega
  have hqself1 : (weighted v.coord.bits v.plus.bits q.1).length≤M := by
    have hw := weighted_length v.coord.bits v.plus.bits q.1
    omega
  have hqself2 : (weighted v.coord.bits v.minus.bits q.2.1).length≤M := by
    have hw := weighted_length v.coord.bits v.minus.bits q.2.1
    omega
  have hmass_next : (weighted v.coord.bits [true] q.2.2).length≤M := by
    have hw := weighted_length v.coord.bits [true] q.2.2
    simp only [List.length_cons,List.length_nil] at hw
    omega
  have hAp_par : Ap[v.parent].bits.length≤B := (bits_len_le_flatMap Ap v.parent hpA).trans hBAp
  have hAn_par : An[v.parent].bits.length≤B := (bits_len_le_flatMap An v.parent hpN).trans hBAn
  have hrow_par : rows[v.parent].bits.length≤W := (bits_len_le_flatMap rows v.parent hp).trans hBrows
  have hread := read_fields_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) q.1 q.2.1 q.2.2 v.parent v.cap v.coord v.plus v.minus
  have hcap_v := cap_run_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.plus.bits v.minus.bits q.1 q.2.1 q.2.2 v.cap v.coord
  have hself := self_run_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
    q.1 q.2.1 q.2.2
  have hchoice := parent_choice_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits
    (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2 v.parent root hr
  let eRead := read_fields base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) q.1 q.2.1 q.2.2 v.parent v.cap v.coord v.plus v.minus
  let eCap := cap_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.plus.bits v.minus.bits q.1 q.2.1 q.2.2 v.cap v.coord
  let eSelf := self_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
    q.1 q.2.1 q.2.2
  let eChoice := parent_choice base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits
    (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2 v.parent root hr
  dsimp only [vertex_run,id]
  have hBM : B≤M := by omega
  have hWM : W≤M := by omega
  have h2M : (2*M)^2=4*M^2 := by ring
  have h3M : (3*M)^2=9*M^2 := by ring
  have hM : M≤M^2 := Nat.le_self_pow (by decide) M
  by_cases hcap : v.coord≤v.cap
  · simp only [hcap,↓reduceDIte]
    have hsq1 : (v.coord.bits.length+v.plus.bits.length+q.1.length+1)^2≤4*M^2 := by
      rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
    have hsq2 : (v.coord.bits.length+v.minus.bits.length+q.2.1.length+1)^2≤4*M^2 := by
      rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
    by_cases hroot : v.parent=root
    · simp only [hroot,↓reduceDIte]
      let eMass := root_mass_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
      let eClean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1)
        (weighted v.coord.bits [true] q.2.2)
      have hmass := root_mass_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
      have hclean := round_clear_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1)
        (weighted v.coord.bits [true] q.2.2)
      have hsq3 : (v.coord.bits.length+[true].length+q.2.2.length+1)^2≤9*M^2 := by
        rw [← h3M]; simp only [List.length_cons,List.length_nil]; exact Nat.pow_le_pow_left (by omega) 2
      change (((((eRead.val+eCap.val)+eSelf.val)+eChoice.val)+eMass.val)+eClean.val)≤4096*M^2
      dsimp only [eRead,eCap,eSelf,eChoice,eMass,eClean]
      rw [hread,hcap_v,hself,hmass,hclean]
      omega
    · simp only [hroot,↓reduceDIte]
      let ePar := parent_test_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.cap.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
        rows v.parent v.coord hp hrow
      have hpar := parent_test_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.cap.bits v.plus.bits v.minus.bits
        (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
        rows v.parent v.coord hp hrow
      have hsqR : ((rows.flatMap encodeNat).length+v.parent.bits.length+1)^2≤M^2 :=
        Nat.pow_le_pow_left (by omega) 2
      by_cases hzero : v.coord=0
      · simp only [hzero,↓reduceDIte]
        let eClean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
          (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
          (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
        have hclean := round_clear_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
          (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
          (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
        change (((((eRead.val+eCap.val)+eSelf.val)+eChoice.val)+ePar.val)+eClean.val)≤4096*M^2
        dsimp only [eRead,eCap,eSelf,eChoice,ePar,eClean]
        rw [hread,hcap_v,hself,hclean]
        omega
      · simp only [hzero,↓reduceDIte]
        by_cases hparent : rows[v.parent]=0
        · simp only [hparent,↓reduceDIte]
          let eCs := cleanup_state_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2 false
          have hcs := cleanup_state_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2 false M
            (hbP.trans hBM) (hbH.trans hBM) (hbU.trans hWM) (hbAp.trans hBM) (hbAn.trans hBM)
            (hvPar.trans hBM) (hvCap.trans hBM) (hcoord_le.trans hWM) (hvPlus.trans hBM) (hvMinus.trans hBM)
            hqself1 hqself2 hq3_le
          change (((((eRead.val+eCap.val)+eSelf.val)+eChoice.val)+ePar.val)+eCs.val)≤4096*M^2
          dsimp only [eRead,eCap,eSelf,eChoice,ePar,eCs]
          rw [hread,hcap_v,hself]
          omega
        · simp only [hparent,↓reduceDIte]
          let eFees := parent_fees_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
            Ap An v.parent hpA hpN hap han
          let eClean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits Ap[v.parent].bits (weighted v.coord.bits v.plus.bits q.1))
            (weighted v.coord.bits An[v.parent].bits (weighted v.coord.bits v.minus.bits q.2.1)) q.2.2
          have hfees := parent_fees_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits v.plus.bits q.1) (weighted v.coord.bits v.minus.bits q.2.1) q.2.2
            Ap An v.parent hpA hpN hap han
          have hclean := round_clear_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (weighted v.coord.bits Ap[v.parent].bits (weighted v.coord.bits v.plus.bits q.1))
            (weighted v.coord.bits An[v.parent].bits (weighted v.coord.bits v.minus.bits q.2.1)) q.2.2
          have hsqA : ((Ap.flatMap encodeNat).length+v.parent.bits.length+1)^2≤4*M^2 := by
            rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
          have hsqN : ((An.flatMap encodeNat).length+v.parent.bits.length+1)^2≤4*M^2 := by
            rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
          have hsqF1 : (v.coord.bits.length+Ap[v.parent].bits.length+
              (weighted v.coord.bits v.plus.bits q.1).length+1)^2≤4*M^2 := by
            rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
          have hsqF2 : (v.coord.bits.length+An[v.parent].bits.length+
              (weighted v.coord.bits v.minus.bits q.2.1).length+1)^2≤4*M^2 := by
            rw [← h2M]; exact Nat.pow_le_pow_left (by omega) 2
          change ((((((eRead.val+eCap.val)+eSelf.val)+eChoice.val)+ePar.val)+eFees.val)+eClean.val)≤4096*M^2
          dsimp only [eRead,eCap,eSelf,eChoice,ePar,eFees,eClean]
          rw [hread,hcap_v,hself,hfees,hclean]
          omega
  · simp only [hcap,↓reduceDIte]
    let eCs := cleanup_state_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
      (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
      q.1 q.2.1 q.2.2 false
    have hcs := cleanup_state_val base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
      (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
      q.1 q.2.1 q.2.2 false M
      (hbP.trans hBM) (hbH.trans hBM) (hbU.trans hWM) (hbAp.trans hBM) (hbAn.trans hBM)
      (hvPar.trans hBM) (hvCap.trans hBM) (hcoord_le.trans hWM) (hvPlus.trans hBM) (hvMinus.trans hBM)
      hq1_le hq2_le hq3_le
    change ((eRead.val+eCap.val)+eCs.val)≤4096*M^2
    dsimp only [eRead,eCap,eCs]
    rw [hread,hcap_v]
    omega

theorem loop_run_val (base : K → Bits) (rows Ap An : List ℕ) (root : ℕ)
    (hr : base (reg 5)=root.bits) (hrow : base (reg 2)=rows.flatMap encodeNat)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat)
    (vs : List Node) (q : WordState)
    (hp : ∀ v∈vs, v.parent<rows.length ∧ v.parent<Ap.length ∧ v.parent<An.length)
    (B W : ℕ)
    (hBrows : (rows.flatMap encodeNat).length≤W)
    (hBAp : (Ap.flatMap encodeNat).length≤B)
    (hBAn : (An.flatMap encodeNat).length≤B)
    (hBroot : root.bits.length≤B)
    (hbP : (body vs Node.parent).length≤B) (hbH : (body vs Node.cap).length≤B)
    (hbU : (body vs Node.coord).length≤W) (hbAp : (body vs Node.plus).length≤B)
    (hbAn : (body vs Node.minus).length≤B)
    (hvB : ∀ v∈vs, v.parent.bits.length≤B ∧ v.cap.bits.length≤B ∧ v.plus.bits.length≤B ∧ v.minus.bits.length≤B)
    (hq1 : q.1.length+2*(vs.map fun v => v.coord.bits.length).sum≤ max B 1+W)
    (hq2 : q.2.1.length+2*(vs.map fun v => v.coord.bits.length).sum≤ max B 1+W)
    (hq3 : q.2.2.length+2*(vs.map fun v => v.coord.bits.length).sum≤ max B 1+W) :
    (loop_run base rows Ap An root hr hrow hap han vs q hp).val≤
      (vs.length+1)*4096*(B+W+1)^2 := by
  induction vs generalizing q with
  | nil =>
    simp only [loop_run,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero,List.length_nil,
      Nat.zero_add,Nat.one_mul] at hq1 hq2 hq3 ⊢
    have hf := final_run_val base q.1 q.2.1 q.2.2 (B+W+1) (by omega) (by omega) (by omega)
    have hM : B+W+1≤(B+W+1)^2 := Nat.le_self_pow (by decide) (B+W+1)
    linarith
  | cons v vs ih =>
    have hv := hp v (by simp)
    have hvb := hvB v (by simp)
    have hcs_tail := coordSum_le_body vs
    have hbP' : (body vs Node.parent).length≤B := by
      unfold body at hbP ⊢; simp only [List.map_cons,List.flatMap_cons,List.length_append] at hbP; omega
    have hbH' : (body vs Node.cap).length≤B := by
      unfold body at hbH ⊢; simp only [List.map_cons,List.flatMap_cons,List.length_append] at hbH; omega
    have hbU' : (body vs Node.coord).length≤W := by
      unfold body at hbU ⊢; simp only [List.map_cons,List.flatMap_cons,List.length_append] at hbU; omega
    have hbAp' : (body vs Node.plus).length≤B := by
      unfold body at hbAp ⊢; simp only [List.map_cons,List.flatMap_cons,List.length_append] at hbAp; omega
    have hbAn' : (body vs Node.minus).length≤B := by
      unfold body at hbAn ⊢; simp only [List.map_cons,List.flatMap_cons,List.length_append] at hbAn; omega
    have hvCoord : 2*v.coord.bits.length≤W := by
      have h := coordSum_le_body (v::vs)
      simp only [List.map_cons,List.sum_cons] at h
      omega
    have hq1_v : q.1.length+2*v.coord.bits.length≤ max B 1+W := by
      simp only [List.map_cons,List.sum_cons] at hq1; omega
    have hq2_v : q.2.1.length+2*v.coord.bits.length≤ max B 1+W := by
      simp only [List.map_cons,List.sum_cons] at hq2; omega
    have hq3_v : q.2.2.length+2*v.coord.bits.length≤ max B 1+W := by
      simp only [List.map_cons,List.sum_cons] at hq3; omega
    have hone := vertex_run_val base rows Ap An root hr hrow hap han v vs q hv.1 hv.2.1 hv.2.2 B W
      hBrows hBAp hBAn hBroot hbP' hbH' hbU' hbAp' hbAn' hvb.1 hvb.2.1 hvCoord hvb.2.2.1 hvb.2.2.2
      hq1_v hq2_v hq3_v
    have hAp_par : Ap[v.parent]?.getD 0=Ap[v.parent] := by simp [List.getElem?_eq_getElem,hv.2.1]
    have hAn_par : An[v.parent]?.getD 0=An[v.parent] := by simp [List.getElem?_eq_getElem,hv.2.2]
    have hAp_len : (Ap[v.parent]?.getD 0).bits.length≤B := by
      rw [hAp_par]; exact (bits_len_le_flatMap Ap v.parent hv.2.1).trans hBAp
    have hAn_len : (An[v.parent]?.getD 0).bits.length≤B := by
      rw [hAn_par]; exact (bits_len_le_flatMap An v.parent hv.2.2).trans hBAn
    have hv_plus : v.plus.bits.length≤B := hvb.2.2.1
    have hv_minus : v.minus.bits.length≤B := hvb.2.2.2
    have hsum_all : 2*v.coord.bits.length+2*(vs.map fun u => u.coord.bits.length).sum≤W := by
      have h := coordSum_le_body (v::vs)
      simp only [List.map_cons,List.sum_cons] at h
      omega
    have hnext1 : (nodeStep Ap An root v q).1.length+2*(vs.map fun u => u.coord.bits.length).sum≤ max B 1+W := by
      have hw1 := weighted_length v.coord.bits v.plus.bits q.1
      have hw2 := weighted_length v.coord.bits (Ap[v.parent]?.getD 0).bits (weighted v.coord.bits v.plus.bits q.1)
      simp only [List.map_cons,List.sum_cons] at hq1
      unfold nodeStep
      split_ifs <;> simp only [Nat.max_def] at hw1 hw2 hq1 ⊢ <;> split_ifs at hw1 hw2 hq1 ⊢ <;> omega
    have hnext2 : (nodeStep Ap An root v q).2.1.length+2*(vs.map fun u => u.coord.bits.length).sum≤ max B 1+W := by
      have hw1 := weighted_length v.coord.bits v.minus.bits q.2.1
      have hw2 := weighted_length v.coord.bits (An[v.parent]?.getD 0).bits (weighted v.coord.bits v.minus.bits q.2.1)
      simp only [List.map_cons,List.sum_cons] at hq2
      unfold nodeStep
      split_ifs <;> simp only [Nat.max_def] at hw1 hw2 hq2 ⊢ <;> split_ifs at hw1 hw2 hq2 ⊢ <;> omega
    have hnext3 : (nodeStep Ap An root v q).2.2.length+2*(vs.map fun u => u.coord.bits.length).sum≤ max B 1+W := by
      have hw := weighted_length v.coord.bits [true] q.2.2
      simp only [List.length_cons,List.length_nil] at hw
      simp only [List.map_cons,List.sum_cons] at hq3
      unfold nodeStep
      split_ifs <;> simp only [Nat.max_def] at hw hq3 ⊢ <;> split_ifs at hw hq3 ⊢ <;> omega
    have htail := ih (nodeStep Ap An root v q) (by intro u hu; exact hp u (by simp [hu]))
      hbP' hbH' hbU' hbAp' hbAn' (by intro u hu; exact hvB u (by simp [hu])) hnext1 hnext2 hnext3
    have hstep : (loop_run base rows Ap An root hr hrow hap han (v::vs) q hp).val=
        if nodePass rows root v then
          (vertex_run base rows Ap An root hr hrow hap han v vs q hv.1 hv.2.1 hv.2.2).val+
          (loop_run base rows Ap An root hr hrow hap han vs (nodeStep Ap An root v q)
            (by intro u hu; exact hp u (by simp [hu]))).val
        else (vertex_run base rows Ap An root hr hrow hap han v vs q hv.1 hv.2.1 hv.2.2).val := by
      simp only [loop_run]
      split_ifs <;> rfl
    cases hpass : nodePass rows root v with
    | true =>
      simp only [hpass, if_true] at hstep
      rw [hstep]
      simp only [List.length_cons]
      have hmul : (vs.length+1+1)*4096*(B+W+1)^2=
          4096*(B+W+1)^2+(vs.length+1)*4096*(B+W+1)^2 := by ring
      omega
    | false =>
      simp only [hpass, Bool.false_eq_true, if_false] at hstep
      rw [hstep]
      simp only [List.length_cons]
      have hmul : (vs.length+1+1)*4096*(B+W+1)^2=
          4096*(B+W+1)^2+(vs.length+1)*4096*(B+W+1)^2 := by ring
      omega

theorem root_gate_val (P H plus minus tp tn ctx suffix : Bits) (rows : List ℕ) (root : ℕ)
    (hr : root<rows.length) (B W : ℕ)
    (hrows : (rows.flatMap encodeNat).length≤W) (hroot : root.bits.length≤B) :
    (root_gate_run P H plus minus tp tn ctx suffix rows root hr).val≤2048*(B+W+1)^2 := by
  dsimp only [root_gate_run,id]
  have hsq : ((rows.flatMap encodeNat).length+root.bits.length+1)^2≤(B+W+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h1 : B+W+1≤(B+W+1)^2 := Nat.le_self_pow (by decide) (B+W+1)
  by_cases hz : rows[root]=0
  · simp only [hz,↓reduceDIte]
    change ((256*((rows.flatMap encodeNat).length+root.bits.length+1)^2+2)+1)+2≤_
    omega
  · simp only [hz,↓reduceDIte]
    have hrl : rows[root].bits.length≤W := (bits_len_le_flatMap rows root hr).trans hrows
    have hw : workSize (set (store P H (rows.flatMap encodeNat) plus minus root.bits tp tn ctx suffix)
        23 rows[root].bits)≤35*W := by
      apply workSize_le
      intro k hk
      fin_cases k <;> simp_all [set,store,reg,hrl]
    change ((256*((rows.flatMap encodeNat).length+root.bits.length+1)^2+2)+1)+
      (25*(workSize _+2)+1)≤_
    omega

theorem row_run_val {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n)
    (budget : ℤ) (ctx suffix : Bits) (B W : ℕ)
    (hP : ((P.parents.toList.map Fin.val).flatMap encodeNat).length≤B)
    (hH : (H.toList.flatMap encodeNat).length≤B)
    (hAp : (Ap.toList.flatMap encodeNat).length≤B)
    (hAn : (An.toList.flatMap encodeNat).length≤B)
    (hroot : P.root.val.bits.length≤B)
    (htp : budget.toNat.bits.length≤B) (htn : (-budget).toNat.bits.length≤B)
    (hp : (p.toList.flatMap encodeNat).length≤W) :
    (row_run P H Ap An p budget ctx suffix).val≤8192*(B+W+1)^3 := by
  have hnW : n≤W := by
    have h := length_le_flatMap_nat p.toList
    simpa only [Vector.length_toList] using h.trans hp
  have hgate := root_gate_val ((P.parents.toList.map Fin.val).flatMap encodeNat)
    (H.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
    budget.toNat.bits (-budget).toNat.bits ctx suffix p.toList P.root.val
    (by simpa using P.root.isLt) B W hp hroot
  have hprep := prepare_run_val ((P.parents.toList.map Fin.val).flatMap encodeNat)
    (H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat)
    (An.toList.flatMap encodeNat) P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix
  have bodies := nodes_body P H Ap An p
  have hcs : 2*((nodes P H Ap An p).map fun v => v.coord.bits.length).sum≤W := by
    have h := coordSum_le_body (nodes P H Ap An p)
    rw [bodies.2.2.1] at h
    exact h.trans hp
  have hvB : ∀ v∈nodes P H Ap An p,
      v.parent.bits.length≤B ∧ v.cap.bits.length≤B ∧ v.plus.bits.length≤B ∧ v.minus.bits.length≤B := by
    intro v hv
    simp only [nodes,List.mem_ofFn] at hv
    obtain ⟨i,rfl⟩ := hv
    have hpar_list : (P.parents.toList.map Fin.val)[i.val]=P.parents[i].val := by simp
    have hp1 : P.parents[i].val.bits.length≤B := by
      have h := bits_len_le_flatMap (P.parents.toList.map Fin.val) i.val (by simp)
      rw [hpar_list] at h
      exact h.trans hP
    have hp2 : H[i].bits.length≤B := by
      have h := bits_len_le_flatMap H.toList i.val (by simp)
      simp only [Vector.getElem_toList] at h
      exact h.trans hH
    have hp3 : Ap[i].bits.length≤B := by
      have h := bits_len_le_flatMap Ap.toList i.val (by simp)
      simp only [Vector.getElem_toList] at h
      exact h.trans hAp
    have hp4 : An[i].bits.length≤B := by
      have h := bits_len_le_flatMap An.toList i.val (by simp)
      simp only [Vector.getElem_toList] at h
      exact h.trans hAn
    exact ⟨hp1,hp2,hp3,hp4⟩
  have hq1 : (-budget).toNat.bits.length+2*((nodes P H Ap An p).map fun v => v.coord.bits.length).sum≤
      max B 1+W := by omega
  have hq2 : budget.toNat.bits.length+2*((nodes P H Ap An p).map fun v => v.coord.bits.length).sum≤
      max B 1+W := by omega
  have hq3 : ([] : Bits).length+2*((nodes P H Ap An p).map fun v => v.coord.bits.length).sum≤
      max B 1+W := by simp; omega
  have hloop := loop_run_val (store ((P.parents.toList.map Fin.val).flatMap encodeNat)
    (H.toList.flatMap encodeNat) (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat)
    (An.toList.flatMap encodeNat) P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix)
    p.toList Ap.toList An.toList P.root.val rfl rfl rfl rfl
    (nodes P H Ap An p) ((-budget).toNat.bits,budget.toNat.bits,[])
    (by
      intro v hv
      simp only [nodes,List.mem_ofFn] at hv
      obtain ⟨i,rfl⟩ := hv
      simpa using (show (P.parents[i]).val<n ∧ (P.parents[i]).val<n ∧ (P.parents[i]).val<n from
        ⟨(P.parents[i]).isLt,(P.parents[i]).isLt,(P.parents[i]).isLt⟩))
    B W hp hAp hAn hroot
    (by rw [bodies.1]; exact hP) (by rw [bodies.2.1]; exact hH)
    (by rw [bodies.2.2.1]; exact hp) (by rw [bodies.2.2.2.1]; exact hAp)
    (by rw [bodies.2.2.2.2]; exact hAn)
    hvB hq1 hq2 hq3
  have hnodes_len : (nodes P H Ap An p).length=n := by simp [nodes]
  rw [hnodes_len] at hloop
  dsimp only [row_run,id]
  by_cases hz : p[P.root]=0
  · simp only [hz,↓reduceDIte]
    have h1 : B+W+1≤(B+W+1)^2 := Nat.le_self_pow (by decide) (B+W+1)
    have hsq : (B+W+1)^2≤(B+W+1)^3 := by
      calc (B+W+1)^2=(B+W+1)^2*1 := by ring
        _ ≤ (B+W+1)^2*(B+W+1) := by gcongr; omega
        _ = (B+W+1)^3 := by ring
    have hn' : (n+1)*4096*(B+W+1)^2≤(W+1)*4096*(B+W+1)^2 := by gcongr
    have hmul : (W+1)*(B+W+1)^2≤(B+W+1)^3 := by
      calc (W+1)*(B+W+1)^2≤(B+W+1)*(B+W+1)^2 := by gcongr; omega
        _ = (B+W+1)^3 := by ring
    have hmul' : (W+1)*4096*(B+W+1)^2≤4096*(B+W+1)^3 := by
      calc (W+1)*4096*(B+W+1)^2=4096*((W+1)*(B+W+1)^2) := by ring
        _ ≤ 4096*(B+W+1)^3 := Nat.mul_le_mul_left 4096 hmul
    change ((root_gate_run _ _ _ _ _ _ _ _ _ _ _).val+(prepare_run _ _ _ _ _ _ _ _ _ _).val)+
      (loop_run _ _ _ _ _ _ _ _ _ _ _ _).val≤_
    omega
  · simp only [hz,↓reduceDIte]
    have hsq : (B+W+1)^2≤(B+W+1)^3 := by
      calc (B+W+1)^2=(B+W+1)^2*1 := by ring
        _ ≤ (B+W+1)^2*(B+W+1) := by gcongr; omega
        _ = (B+W+1)^3 := by ring
    change (root_gate_run _ _ _ _ _ _ _ _ _ _ _).val≤_
    omega

def row_run_in_time {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (ctx suffix : Bits) (B W : ℕ)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v])
    (hP : ((P.parents.toList.map Fin.val).flatMap encodeNat).length≤B)
    (hH : (H.toList.flatMap encodeNat).length≤B)
    (hAp : (Ap.toList.flatMap encodeNat).length≤B)
    (hAn : (An.toList.flatMap encodeNat).length≤B)
    (hroot : P.root.val.bits.length≤B)
    (htp : budget.toNat.bits.length≤B) (htn : (-budget).toNat.bits.length≤B)
    (hp : (p.toList.flatMap encodeNat).length≤W) :
    EvalsToInTime machine.step
      (start ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
        (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix)
      (some (stopped (rowCheck P H A budget p).value
        ((P.parents.toList.map Fin.val).flatMap encodeNat) (H.toList.flatMap encodeNat)
        (p.toList.flatMap encodeNat) (Ap.toList.flatMap encodeNat) (An.toList.flatMap encodeNat)
        P.root.val.bits budget.toNat.bits (-budget).toNat.bits ctx suffix))
      (8192*(B+W+1)^3) := by
  have he := rowResult_eq_rowCheck P H Ap An A p budget ha
  have run := weaken (row_run P H Ap An p budget ctx suffix).property
    (row_run_val P H Ap An p budget ctx suffix B W hP hH hAp hAn hroot htp htn hp)
  simpa only [he] using run

end UAVProof.A4RowCheck
