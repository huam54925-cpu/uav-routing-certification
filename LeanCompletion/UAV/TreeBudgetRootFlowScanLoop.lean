import LeanCompletion.UAV.TreeBudgetRootFlowScanRuns
import LeanCompletion.UAV.TreeBudgetRootFlowSpec

namespace UAVProof.TreeBudgetRootFlowScanTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open TreeBudgetRootFlowSpec

def seq {a b c : Cfg} {x y : ℕ} (h : Run a b x) (g : Run b c y) : Run a c (x+y) :=
  by simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step x y a b (some c) h g

theorem body_cons_ne_nil (p : ℕ) (ps : List ℕ) : ((p::ps).flatMap encodeNat)≠[] := by
  have h := encodeNat_nonempty p
  intro he
  have := congrArg List.length he
  simp only [List.flatMap_cons,List.length_append,List.length_nil] at this
  omega

def pending (d : Data) (i : ℕ) (ps hs : List ℕ) (u : Bits) (h : ℕ) :=
  {work d i ps hs u with b:=h.bits}

def skip_run (d : Data) (i : ℕ) (ps hs : List ℕ) (u : Bits) (h : ℕ) :
    Run (cfg (entry .clearH) (pending d i ps hs u h))
      (cfg (.control .loop) (work d (i+1) ps hs u))
      (h.bits.length+2*i.bits.length+3) := by
  have hc := clear_job .clearH (pending d i ps hs u h)
  have hi := increment_job (work d i ps hs u) rfl
  exact weaken (by simpa [pending,work,replace,dest,source,TreeBudgetStackRoutine.increment_bits] using seq hc hi) (by omega)

def take_run (d : Data) (i : ℕ) (ps hs : List ℕ) (u : Bits) (h : ℕ) :
    Run (cfg (entry .operand) (pending d i ps hs u h))
      (cfg (.control .loop) (work d (i+1) ps hs (TreeBudgetAddWordsTM2.addWords u h.bits false)))
      (5*u.length+2*h.bits.length+2*i.bits.length+11) := by
  have ha := addition_job (pending d i ps hs u h) rfl rfl rfl
  have hi := increment_job (work d i ps hs (TreeBudgetAddWordsTM2.addWords u h.bits false)) rfl
  exact weaken (by simpa [pending,work,TreeBudgetStackRoutine.increment_bits] using seq ha hi) (by omega)

def parent_run (d : Data) (r i p h : ℕ) (ps hs : List ℕ) (u : Bits) (hr : d.r=r.bits) :
    Run (cfg (.control .loop) (work d i (p::ps) (h::hs) u))
      (cfg (if p=r then entry .index else entry .clearH) (pending d i ps hs u h))
      (2*((p::ps).flatMap encodeNat).length+2*((h::hs).flatMap encodeNat).length+
        3*r.bits.length+p.bits.length+9) := by
  let d₀ := work d i (p::ps) (h::hs) u
  let d₁ := frameSet false d₀ (ps.flatMap encodeNat) [] p.bits
  let d₂ := frameSet true d₁ (hs.flatMap encodeNat) [] h.bits
  let d₃ := copied .rootP d₂
  have test : Run (cfg (.control .loop) d₀) (cfg (.frame false .marker) d₀) 1 := by
    apply once
    simpa only [testEnd,d₀,work,body_cons_ne_nil,if_false] using test_step d₀
  have hp := field_run false d₀ p (ps.flatMap encodeNat) rfl rfl rfl
  have hh := field_run true d₁ h (hs.flatMap encodeNat) rfl rfl rfl
  have cp := copy_job .rootP d₂ rfl
  have cmp := compare_job .parent d₃
  have ce : comparison .parent d₃=decide (p=r) := by
    rw [comparison_eq _ rfl]
    simpa [d₃,d₂,d₁,d₀,copied,source,dest,replace,frameSet,work,hr] using bits_eq p r
  simp only [compared,ce] at cmp
  exact weaken (by simpa [compared,ce,d₃,d₂,d₁,d₀,copied,source,dest,replace,frameSet,
      frameSource,pending,work,hr] using seq (seq (seq (seq test hp) hh) cp) cmp)
    (by simp only [List.flatMap_cons,List.length_append,List.length_flatMap]; omega)

def index_run (d : Data) (r i h : ℕ) (ps hs : List ℕ) (u : Bits) (hr : d.r=r.bits) :
    Run (cfg (entry .index) (pending d i ps hs u h))
      (cfg (if i=r then entry .clearH else entry .operand) (pending d i ps hs u h))
      (3*i.bits.length+3*r.bits.length+6) := by
  let d₀ := pending d i ps hs u h
  let d₁ := copied .index d₀
  let d₂ := copied .rootI d₁
  have ci := copy_job .index d₀ rfl
  have cr := copy_job .rootI d₁ rfl
  have cmp := compare_job .index d₂
  have ce : comparison .index d₂=decide (i=r) := by
    rw [comparison_eq _ rfl]
    simpa [d₂,d₁,d₀,copied,source,dest,replace,pending,work,hr] using bits_eq i r
  simp only [compared,ce] at cmp
  exact weaken (by simpa [compared,ce,d₂,d₁,d₀,copied,source,dest,replace,pending,work,hr] using seq (seq ci cr) cmp) (by omega)

/-- One actual synchronized round, including parsing, copies, branches and return. -/
def round_run (d : Data) (r i p h S : ℕ) (ps hs : List ℕ) (u : Bits)
    (hr : d.r=r.bits) (br : r.bits.length≤S) (bi : i.bits.length≤S)
    (bp : ((p::ps).flatMap encodeNat).length≤S)
    (bh : ((h::hs).flatMap encodeNat).length≤S) (bu : u.length≤S) :
    Run (cfg (.control .loop) (work d i (p::ps) (h::hs) u))
      (cfg (.control .loop) (work d (i+1) ps hs
        (if selected r i p then TreeBudgetAddWordsTM2.addWords u h.bits false else u)))
      (128*(S+1)) := by
  have bpb : p.bits.length≤S := by
    simp only [List.flatMap_cons,List.length_append,encodeNat_length,Nat.size_eq_bits_len] at bp ⊢
    omega
  have bhb : h.bits.length≤S := by
    simp only [List.flatMap_cons,List.length_append,encodeNat_length,Nat.size_eq_bits_len] at bh ⊢
    omega
  have hp := parent_run d r i p h ps hs u hr
  by_cases he : p=r
  · subst p
    simp only [if_pos rfl] at hp
    have hi := index_run d r i h ps hs u hr
    by_cases hiR : i=r
    · simp only [if_pos hiR] at hi
      have ht := skip_run d i ps hs u h
      exact weaken (by simpa [selected,hiR] using seq (seq hp hi) ht)
        (by simp only [List.flatMap_cons,List.length_append,List.length_flatMap] at bp bh; omega)
    · simp only [if_neg hiR] at hi
      have ht := take_run d i ps hs u h
      exact weaken (by simpa [selected,hiR] using seq (seq hp hi) ht)
        (by simp only [List.flatMap_cons,List.length_append,List.length_flatMap] at bp bh; omega)
  · simp only [if_neg he] at hp
    have ht := skip_run d i ps hs u h
    exact weaken (by simpa [selected,he] using seq hp ht)
      (by simp only [List.flatMap_cons,List.length_append,List.length_flatMap] at bp bh; omega)

def scanEnd (d : Data) (r : ℕ) : ℕ → List ℕ → List ℕ → Bits → Cfg
  | i,[],[],u => cfg (entry .finalA) (work d i [] [] u)
  | i,[],h::hs,u => stop (work d i [] (h::hs) u) false
  | i,p::ps,[],u => stop (work d i (p::ps) [] u) false
  | i,p::ps,h::hs,u => scanEnd d r (i+1) ps hs
      (if selected r i p then TreeBudgetAddWordsTM2.addWords u h.bits false else u)

/-- Arbitrary starting coordinate and accumulator, including padded words. -/
def scan_run (d : Data) (r S i : ℕ) (ps hs : List ℕ) (u : Bits)
    (hr : d.r=r.bits) (br : r.bits.length≤S) (bi : i+ps.length≤S)
    (bp : (ps.flatMap encodeNat).length≤S) (bu : u.length+(hs.flatMap encodeNat).length≤S) :
    Run (cfg (.control .loop) (work d i ps hs u)) (scanEnd d r i ps hs u)
      (128*(S+1)*(ps.length+1)) := by
  induction ps generalizing i hs u with
  | nil =>
    cases hs with
    | nil => exact weaken (once (by simpa only [scanEnd,testEnd,work,if_pos rfl] using test_step (work d i [] [] u))) (by simp only [List.length_nil]; omega)
    | cons h hs => exact weaken (once (by simpa only [scanEnd,testEnd,work,body_cons_ne_nil,if_pos rfl,if_false] using test_step (work d i [] (h::hs) u))) (by simp only [List.length_nil]; omega)
  | cons p ps ih =>
    cases hs with
    | nil => exact weaken (once (by simpa only [scanEnd,testEnd,work,body_cons_ne_nil,if_pos rfl,if_false] using test_step (work d i (p::ps) [] u))) (by simp only [List.length_cons]; nlinarith)
    | cons h hs =>
      let u' := if selected r i p then TreeBudgetAddWordsTM2.addWords u h.bits false else u
      have bi' : (i+1)+ps.length≤S := by simp only [List.length_cons] at bi; omega
      have bp' : (ps.flatMap encodeNat).length≤S := by
        simp only [List.flatMap_cons,List.length_append] at bp; omega
      have bu' : u'.length+(hs.flatMap encodeNat).length≤S := by
        have ha := TreeBudgetAddWordsTM2.addWords_length u h.bits false
        simp only [List.flatMap_cons,List.length_append,encodeNat_length,Nat.size_eq_bits_len] at bu ha
        dsimp [u']; split <;> omega
      have bitsI : i.bits.length≤S := by
        have hn := TreeBudgetCostedCodec.nat_size_le i
        simp only [Nat.size_eq_bits_len] at ⊢
        simp only [List.length_cons] at bi
        omega
      have run := round_run d r i p h S ps hs u hr br bitsI bp (by omega) (by omega)
      have tail := ih (i+1) hs u' bi' bp' bu'
      exact weaken (seq run tail) (by simp only [List.length_cons]; nlinarith)

theorem scanEnd_equal (d : Data) (r i : ℕ) (ps hs : List ℕ) (u : Bits) (he : ps.length=hs.length) :
    scanEnd d r i ps hs u = cfg (entry .finalA)
      (work d (i+ps.length) [] [] (accumulated r i ps hs u)) := by
  induction ps generalizing i hs u with
  | nil => cases hs <;> simp_all [scanEnd,accumulated]
  | cons p ps ih =>
    cases hs with
    | nil => simp at he
    | cons h hs =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at he
      simpa [scanEnd,accumulated,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (i+1) hs (if selected r i p then TreeBudgetAddWordsTM2.addWords u h.bits false else u) he

theorem scanEnd_unequal (d : Data) (r i : ℕ) (ps hs : List ℕ) (u : Bits) (he : ps.length≠hs.length) :
    (scanEnd d r i ps hs u).l=none ∧ (scanEnd d r i ps hs u).var.2=false := by
  induction ps generalizing i hs u with
  | nil => cases hs <;> simp_all [scanEnd,stop]
  | cons p ps ih =>
    cases hs with
    | nil => exact ⟨rfl,rfl⟩
    | cons h hs => exact ih _ _ _ (by simpa using he)

theorem scanEnd_kept (d : Data) (r i : ℕ) (ps hs : List ℕ) (u : Bits) : Kept d (scanEnd d r i ps hs u) := by
  induction ps generalizing i hs u with
  | nil => cases hs <;> exact ⟨rfl,rfl,rfl,rfl⟩
  | cons p ps ih => cases hs with
    | nil => exact ⟨rfl,rfl,rfl,rfl⟩
    | cons h hs => exact ih _ _ _

end UAVProof.TreeBudgetRootFlowScanTM2
