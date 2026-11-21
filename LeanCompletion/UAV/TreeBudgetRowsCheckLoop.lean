import LeanCompletion.UAV.TreeBudgetRowsCheckRuns

namespace UAVProof.A4RowsCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def work (d : Data) (xs : RawCertificate) (a : Bits) : Data :=
  {d with
    todo := List.replicate xs.length true
    cursor := xs.flatMap encodeEntry
    entryRow := []
    mult := []
    total := a
    sum := []
    scratch := []
    spare := []
    cmp0 := []
    cmp1 := []
    cmp2 := []
    cmp3 := []}

def ready (d : Data) (es : RawCertificate) (e : RawEntry) (a : Bits) : Data :=
  {work d es a with mult := e.1.bits,rowSaved := Function.update d.rowSaved (A4RowCheck.reg 2) (e.2.flatMap encodeNat)}

def finish_run (d : Data) (ht : d.scratch=[]) (h0 : d.cmp0=[]) (h1 : d.cmp1=[])
    (h2 : d.cmp2=[]) (h3 : d.cmp3=[]) :
    Run (cfg (.job .totalLeft .reverse) d)
      (stop (decide (value d.total=value d.routes)) d)
      (6*(d.total.length+d.routes.length)+13) := by
  let d1 := {d with cmp0 := d.total}
  let d2 := {d1 with cmp1 := d.routes}
  have a : Run (cfg (.job .totalLeft .reverse) d)
      (cfg (.job .routesRight .reverse) d1) (2*d.total.length+2) := by
    simpa [copied,replace,source,dest,next,h0,d1,ht] using copy_job .totalLeft d ht
  have b : Run (cfg (.job .routesRight .reverse) d1)
      (cfg (.compareCall false ()) d2) (2*d.routes.length+2) := by
    simpa [copied,replace,source,dest,next,h1,d1,d2,ht] using copy_job .routesRight d1 ht
  have c := compare_result false d2 h2 h3
  have hc : compared d2=d := by cases d; simp_all [compared,d1,d2]
  rw [hc] at c
  by_cases hle : value d.total≤value d.routes
  · simp only [d1,d2,if_true,hle,Bool.false_eq_true,↓reduceIte] at c
    let d3 := {d with cmp0 := d.routes}
    let d4 := {d3 with cmp1 := d.total}
    have e : Run (cfg (.job .routesLeft .reverse) d)
        (cfg (.job .totalRight .reverse) d3) (2*d.routes.length+2) := by
      simpa [copied,replace,source,dest,next,h0,d3,ht] using copy_job .routesLeft d ht
    have f : Run (cfg (.job .totalRight .reverse) d3)
        (cfg (.compareCall true ()) d4) (2*d.total.length+2) := by
      simpa [copied,replace,source,dest,next,h1,d3,d4,ht] using copy_job .totalRight d3 ht
    have g := compare_result true d4 h2 h3
    have hg : compared d4=d := by cases d; simp_all [compared,d3,d4]
    rw [hg] at g
    by_cases hge : value d.routes≤value d.total
    · simp only [d3,d4,if_true,hge,↓reduceIte] at g
      have last : Run (cfg .good d) (stop true d) 1 := by
        exact once rfl
      have heq : value d.total=value d.routes := by omega
      simpa only [heq,decide_true] using weaken
        (seq (seq (seq (seq (seq (seq a b) c) e) f) g) last)
        (show _≤6*(d.total.length+d.routes.length)+13 by omega)
    · simp only [d3,d4,if_neg hge] at g
      have hne : value d.total≠value d.routes := by omega
      simpa only [hne,decide_false] using weaken
        (seq (seq (seq (seq (seq a b) c) e) f) g)
        (show _≤6*(d.total.length+d.routes.length)+13 by omega)
  · simp only [d1,d2,if_neg hle] at c
    have hne : value d.total≠value d.routes := by omega
    simpa only [hne,decide_false] using weaken (seq (seq a b) c)
      (show _≤6*(d.total.length+d.routes.length)+13 by omega)

def tick_empty (d : Data) (a : Bits) :
    Run (cfg .tick (work d [] a))
      (cfg (.job .totalLeft .reverse) (work d [] a)) 1 := by
  apply once
  simp [machine,FinTM2.step,cfg,work,program,TM2.step,TM2.stepAux,jump,
    TreeBudgetStackRoutine.jump,store,ax]
  congr 2
  exact Function.update_eq_self _ _

def tick_cons (d : Data) (e : RawEntry) (es : RawCertificate) (a : Bits) :
    Run (cfg .tick (work d (e::es) a))
      (cfg (.entryCall TreeBudgetEntryTM2.machine.main)
        {work d es a with cursor := encodeEntry e++es.flatMap encodeEntry}) 1 := by
  apply once
  simp [machine,FinTM2.step,cfg,work,program,TM2.step,TM2.stepAux,jump,
    TreeBudgetStackRoutine.jump,store,ax,List.replicate_succ]
  congr 2
  funext k
  rcases k with ((i|u)|r)|z
  · fin_cases i <;> rfl
  · cases u; rfl
  · rfl
  · cases z <;> rfl

def prepare_record (d : Data) (e : RawEntry) (es : RawCertificate) (a : Bits)
    (hr : d.rowSaved (A4RowCheck.reg 2)=[]) :
    Run (cfg .tick (work d (e::es) a)) (cfg .rowStart (ready d es e a))
      (24*((encodeEntry e++es.flatMap encodeEntry).length+1)^2+
        3*(e.2.flatMap encodeNat).length+5) := by
  let d1 := {work d es a with cursor := encodeEntry e++es.flatMap encodeEntry}
  let d2 := parsed d1 e (es.flatMap encodeEntry)
  let d3 := {ready d es e a with entryRow := e.2.flatMap encodeNat}
  have a1 := tick_cons d e es a
  have a2 := entry_success d1 e (es.flatMap encodeEntry)
    (parseEntry_append e (es.flatMap encodeEntry)) rfl rfl
  have hc : copied .copyRow d2=d3 := by
    simp [copied,replace,source,dest,d2,d1,d3,parsed,ready,work,hr]
  have a3 := copy_job .copyRow d2 (by rfl)
  rw [hc] at a3
  have a4 := clear_job .clearEntryRow d3
  have hd : cleared .clearEntryRow d3=ready d es e a := rfl
  rw [hd] at a4
  have allRun := seq (seq (seq a1 a2) a3) a4
  simpa only [d1,d2,d3,parsed,work,ready,source,next] using weaken allRun
    (show _≤24*((encodeEntry e++es.flatMap encodeEntry).length+1)^2+
      3*(e.2.flatMap encodeNat).length+5 by simp [source,d1,d2,d3,parsed,work,ready]; omega)

def after_add (d : Data) (es : RawCertificate) (e : RawEntry) (a : Bits)
    (hr : d.rowSaved (A4RowCheck.reg 2)=[]) :
    Run (cfg .addStart (ready d es e a))
      (cfg .tick (work d es (TreeBudgetAddWordsTM2.addWords a e.1.bits false)))
      (2*(a.length+e.1.bits.length)+
        3*(TreeBudgetAddWordsTM2.addWords a e.1.bits false).length+
        (e.2.flatMap encodeNat).length+10) := by
  let d1 := added (ready d es e a)
  let d2 := copied .copySum d1
  let d3 := cleared .clearSum d2
  have a1 := add_result (ready d es e a) rfl rfl
  have a2 := copy_job .copySum d1 rfl
  have a3 := clear_job .clearSum d2
  have a4 := clear_job .clearRow d3
  have he : cleared .clearRow d3=work d es (TreeBudgetAddWordsTM2.addWords a e.1.bits false) := by
    simp [d1,d2,d3,cleared,copied,replace,source,dest,added,ready,work,Function.update_idem,
      ← hr,Function.update_eq_self]
  rw [he] at a4
  have allRun := seq (seq (seq a1 a2) a3) a4
  simpa only [d1,d2,d3,copied,cleared,replace,source,dest,next,added,ready,work,
    List.append_nil,Function.update_self] using weaken allRun
      (show _≤2*(a.length+e.1.bits.length)+
        3*(TreeBudgetAddWordsTM2.addWords a e.1.bits false).length+
        (e.2.flatMap encodeNat).length+10 by
        simp [source,dest,d1,d2,d3,added,ready,work,copied,cleared,replace]; omega)

theorem entry_parts_width (e : RawEntry) :
    (e.2.flatMap encodeNat).length≤(encodeEntry e).length ∧
    e.1.bits.length+1≤(encodeEntry e).length := by
  simp only [encodeEntry,encodeNats,encodeList,List.length_append,encodeNat_length,
    Nat.size_eq_bits_len]
  constructor <;> omega

theorem addition_suffix_width (a : Bits) (e : RawEntry) (es : RawCertificate) (W : ℕ)
    (hw : a.length+(encodeEntry e++es.flatMap encodeEntry).length≤W) :
    (TreeBudgetAddWordsTM2.addWords a e.1.bits false).length+
      (es.flatMap encodeEntry).length≤W := by
  have ha := TreeBudgetAddWordsTM2.addWords_length a e.1.bits false
  have he := (entry_parts_width e).2
  simp only [List.length_append] at hw
  omega

def record_run (d : Data) (e : RawEntry) (es : RawCertificate) (a : Bits)
    (b : Bool) (T W : ℕ) (hr : d.rowSaved (A4RowCheck.reg 2)=[])
    (hw : a.length+(encodeEntry e++es.flatMap encodeEntry).length≤W)
    (sub : EvalsToInTime A4RowCheck.machine.step
      ⟨some A4RowCheck.machine.main,(none,true),(ready d es e a).rowSaved⟩
      (some ⟨none,(none,b),(ready d es e a).rowSaved⟩) T) :
    Run (cfg .tick (work d (e::es) a))
      (if b then cfg .tick (work d es (TreeBudgetAddWordsTM2.addWords a e.1.bits false))
       else stop false (ready d es e a)) (T+64*(W+1)^2) := by
  have prep := prepare_record d e es a hr
  have row := row_result (ready d es e a) b T sub
  have he := entry_parts_width e
  have hw' := addition_suffix_width a e es W hw
  have hs : ((encodeEntry e++es.flatMap encodeEntry).length+1)^2≤(W+1)^2 := by
    gcongr
    omega
  have bounds : a.length≤W ∧ e.1.bits.length≤W ∧ (e.2.flatMap encodeNat).length≤W ∧
      (TreeBudgetAddWordsTM2.addWords a e.1.bits false).length≤W := by
    simp only [List.length_append] at hw
    omega
  cases b with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at row ⊢
    exact weaken (seq prep row) (by nlinarith)
  | true =>
    simp only [↓reduceIte] at row ⊢
    exact weaken (seq (seq prep row) (after_add d es e a hr)) (by nlinarith)

def outcome (d : Data) (q : RawEntry → Bool) : RawCertificate → Bits → Cfg
  | [],a => stop (decide (value a=value d.routes)) (work d [] a)
  | e::es,a => if q e then outcome d q es (TreeBudgetAddWordsTM2.addWords a e.1.bits false)
      else stop false (ready d es e a)

theorem outcome_flag (d : Data) (q : RawEntry → Bool) (xs : RawCertificate) (a : Bits) :
    (outcome d q xs a).var.2=
      (xs.all q && decide (value a+(xs.map Prod.fst).sum=value d.routes)) := by
  induction xs generalizing a with
  | nil => simp [outcome,stop]
  | cons e es ih =>
    cases hq : q e <;> simp [outcome,hq,stop,ih,TreeBudgetAddWordsTM2.addWords_value,Nat.add_assoc] <;> rfl

theorem outcome_halted (d : Data) (q : RawEntry → Bool) (xs : RawCertificate) (a : Bits) :
    (outcome d q xs a).l=none := by
  induction xs generalizing a with
  | nil => rfl
  | cons e es ih => cases hq : q e <;> simp [outcome,hq,stop,ih]

/-- Prefix induction charges each successful record exactly once and stops
at the first failed row, including any failed row of multiplicity zero. -/
def records_loop (d : Data) (q : RawEntry → Bool) (xs : RawCertificate)
    (a : Bits) (T W : ℕ) (hr : d.rowSaved (A4RowCheck.reg 2)=[])
    (hw : a.length+(xs.flatMap encodeEntry).length≤W) (hm : d.routes.length≤W)
    (rows : ∀ e∈xs,
      EvalsToInTime A4RowCheck.machine.step
        ⟨some A4RowCheck.machine.main,(none,true),
          Function.update d.rowSaved (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩
        (some ⟨none,(none,q e),
          Function.update d.rowSaved (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩) T) :
    Run (cfg .tick (work d xs a)) (outcome d q xs a)
      ((xs.length+1)*(T+64*(W+1)^2)) := by
  induction xs generalizing a with
  | nil =>
    have last := finish_run (work d [] a) rfl rfl rfl rfl rfl
    have hh := seq (tick_empty d a) last
    simpa only [outcome,work,List.length_nil,Nat.zero_add,Nat.one_mul] using weaken hh
      (show _≤T+64*(W+1)^2 by simp only [work] at *; simp only [List.flatMap_nil,List.length_nil,Nat.add_zero] at hw; nlinarith)
  | cons e es ih =>
    have hs := rows e (by simp)
    have hpre := record_run d e es a (q e) T W hr (by simpa using hw) hs
    cases hq : q e with
    | false =>
      simp only [hq,Bool.false_eq_true,↓reduceIte] at hpre
      simpa only [outcome,hq,Bool.false_eq_true,↓reduceIte] using weaken hpre
        (show T+64*(W+1)^2≤((e::es).length+1)*(T+64*(W+1)^2) by simp <;> nlinarith)
    | true =>
      simp only [hq,↓reduceIte] at hpre
      have ht := ih (TreeBudgetAddWordsTM2.addWords a e.1.bits false)
        (addition_suffix_width a e es W (by simpa using hw))
        (by intro t ht; exact rows t (List.mem_cons_of_mem e ht))
      simpa only [outcome,hq,↓reduceIte] using weaken (seq hpre ht)
        (show _≤((e::es).length+1)*(T+64*(W+1)^2) by simp <;> nlinarith)

def Kept (d : Data) (out : Cfg) : Prop :=
  out.stk (ax .body)=d.body ∧ out.stk (ax .markers)=d.markers ∧
    out.stk (ax .routes)=d.routes ∧
    ∀ k : A4RowCheck.K, k≠A4RowCheck.reg 2 → out.stk (rs k)=d.rowSaved k

theorem outcome_kept (d : Data) (q : RawEntry → Bool) (xs : RawCertificate) (a : Bits) :
    Kept d (outcome d q xs a) := by
  induction xs generalizing a with
  | nil => simp [Kept,outcome,stop,work,store,ax,rs]
  | cons e es ih =>
    cases hq : q e with
    | false =>
      simp [Kept,outcome,hq,stop,ready,work,store,ax,rs]
      intro b hb
      simp [Function.update_of_ne hb]
    | true => simpa only [outcome,hq,↓reduceIte] using
        (ih (TreeBudgetAddWordsTM2.addWords a e.1.bits false))

def start (d : Data) : Cfg := cfg machine.main (work d [] [])

def prepare_table (d : Data) (xs : RawCertificate)
    (hb : d.body=xs.flatMap encodeEntry) (hk : d.markers=List.replicate xs.length true) :
    Run (start d) (cfg .tick (work d xs []))
      (2*d.body.length+2*d.markers.length+4) := by
  let d1 := copied .copyBody (work d [] [])
  have a := copy_job .copyBody (work d [] []) rfl
  have b := copy_job .copyMarkers d1 rfl
  have he : copied .copyMarkers d1=work d xs [] := by
    simp [d1,copied,replace,source,dest,work,hb,hk]
  rw [he] at b
  simpa only [start,machine,next,source,work,d1,copied,replace,dest] using weaken (seq a b)
    (show _≤2*d.body.length+2*d.markers.length+4 by simp [source,d1,copied,replace,work]; omega)

def records_from_start (d : Data) (q : RawEntry → Bool) (xs : RawCertificate)
    (T W : ℕ) (hr : d.rowSaved (A4RowCheck.reg 2)=[])
    (hb : d.body=xs.flatMap encodeEntry) (hk : d.markers=List.replicate xs.length true)
    (hw : d.body.length≤W) (hm : d.routes.length≤W)
    (rows : ∀ e∈xs,
      EvalsToInTime A4RowCheck.machine.step
        ⟨some A4RowCheck.machine.main,(none,true),
          Function.update d.rowSaved (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩
        (some ⟨none,(none,q e),
          Function.update d.rowSaved (A4RowCheck.reg 2) (e.2.flatMap encodeNat)⟩) T) :
    Run (start d) (outcome d q xs []) ((xs.length+1)*(T+72*(W+1)^2)) := by
  have prep := prepare_table d xs hb hk
  have body := records_loop d q xs [] T W hr (by simpa [← hb]) hm rows
  have hlen := length_le_flatMap encodeEntry encodeEntry_nonempty xs
  have hmarkers : d.markers.length=xs.length := by simp [hk]
  rw [← hb] at hlen
  exact weaken (seq prep body) (by nlinarith)

end UAVProof.A4RowsCheck
