import LeanCompletion.UAV.TreeBudgetWeightedWidth
import LeanCompletion.UAV.TreeBudgetBinaryPreprocessing
import LeanCompletion.UAV.TreeBudgetPairedParserTotal

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetBinaryPreprocessing TreeBudgetVectorChecker

abbrev Row := ℤ × ℕ
def mulWord (u v : Bits) := TreeBudgetWeightedTM2.weighted u v []

@[simp] theorem mulWord_value (u v : Bits) : value (mulWord u v)=value u*value v := by
  simp [mulWord,TreeBudgetWeightedTM2.weighted_value,value]
theorem mulWord_length (u v : Bits) : (mulWord u v).length ≤ u.length+v.length :=
  TreeBudgetWeightedTM2.product_length u v

structure Item where
  a : ℤ
  b : ℕ
  pre : Bits

def prefixEnd : Bits → List Row → Bits
  | p,[] => p
  | p,e::es => prefixEnd (mulWord p e.2.bits) es

/-- Last vertex first, exactly as the three physical history stacks. -/
def history : Bits → List Row → List Item
  | _,[] => []
  | p,e::es => history (mulWord p e.2.bits) es ++ [⟨e.1,e.2,p⟩]

def denProd (es : List Row) := (es.map Prod.snd).prod
def denWidth (es : List Row) := (es.map fun e => e.2.bits.length).sum
def mass (es : List Row) := (es.map fun e => e.1.natAbs.bits.length+e.2.bits.length).sum
def historyWidth (hs : List Item) := (hs.map fun e => e.b.bits.length).sum

theorem denWidth_le_mass (es : List Row) : denWidth es ≤ mass es := by
  induction es <;> simp_all [denWidth,mass] <;> omega

theorem prefixEnd_value (p : Bits) (es : List Row) :
    value (prefixEnd p es)=value p*denProd es := by
  induction es generalizing p <;> simp_all [prefixEnd,denProd,Nat.mul_assoc]

theorem prefixEnd_length (p : Bits) (es : List Row) :
    (prefixEnd p es).length ≤ p.length+denWidth es := by
  induction es generalizing p with
  | nil => simp [prefixEnd,denWidth]
  | cons e es ih =>
    have h := ih (mulWord p e.2.bits)
    have hm := mulWord_length p e.2.bits
    simp only [prefixEnd,denWidth,List.map_cons,List.sum_cons] at *
    omega

theorem history_width (p : Bits) (es : List Row) : historyWidth (history p es)=denWidth es := by
  induction es generalizing p <;>
    simp_all [history,historyWidth,denWidth,List.map_append,List.sum_append,Nat.add_comm]

def Fits : List Item → ℕ → ℕ → Prop
  | [],_,_ => True
  | e::es,u,B => e.pre.length+u+e.a.natAbs.bits.length+e.b.bits.length ≤ B ∧
      Fits es (u+e.b.bits.length) B

theorem fits_append (hs ts : List Item) (u B : ℕ) :
    Fits (hs++ts) u B ↔ Fits hs u B ∧ Fits ts (u+historyWidth hs) B := by
  induction hs generalizing u <;>
    simp_all [Fits,historyWidth,Nat.add_assoc,and_assoc]

theorem fits_mono (hs : List Item) (u v B : ℕ) (hv : v≤u) (h : Fits hs u B) : Fits hs v B := by
  induction hs generalizing u v with
  | nil => trivial
  | cons e es ih => exact ⟨by have := h.1; omega,ih _ _ (by omega) h.2⟩

/-- The prefix and active suffix use disjoint denominator positions. -/
theorem history_fits (p : Bits) (es : List Row) (u B : ℕ)
    (h : p.length+u+mass es ≤ B) : Fits (history p es) u B := by
  induction es generalizing p with
  | nil => trivial
  | cons e es ih =>
    rw [history,fits_append]
    have hm := mulWord_length p e.2.bits
    have hd := denWidth_le_mass es
    change p.length+u+(e.1.natAbs.bits.length+e.2.bits.length+mass es) ≤ B at h
    refine ⟨ih _ (by omega),?_⟩
    simp only [Fits,history_width,and_true]
    omega

def coefficient (e : Item) (u : Bits) : ℤ := e.a * ((value e.pre*value u : ℕ):ℤ)

def backward : List Item → Bits → Bits × List ℤ
  | [],u => (u,[])
  | e::es,u =>
    let tail := backward es (mulWord e.b.bits u)
    (tail.1,tail.2++[coefficient e u])

theorem backward_append (hs ts : List Item) (u : Bits) :
    backward (hs++ts) u=
      ((backward ts (backward hs u).1).1,
       (backward ts (backward hs u).1).2++(backward hs u).2) := by
  induction hs generalizing u <;> simp_all [backward,List.append_assoc]

def formula : ℕ → ℕ → List Row → List ℤ
  | _,_,[] => []
  | p,t,e::es => e.1*((p*(t*denProd es):ℕ):ℤ)::formula (p*e.2) t es

theorem backward_history (p u : Bits) (es : List Row) :
    value (backward (history p es) u).1=value u*denProd es ∧
    (backward (history p es) u).2=formula (value p) (value u) es := by
  induction es generalizing p with
  | nil => simp [backward,history,denProd,formula]
  | cons e es ih =>
    have h := ih (mulWord p e.2.bits)
    simp only [history,backward_append,backward,List.nil_append]
    constructor
    · simp [h.1,denProd,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    · simp [coefficient,h.1,h.2,formula]

@[simp] theorem formula_length (p t : ℕ) (es : List Row) : (formula p t es).length=es.length := by
  induction es generalizing p <;> simp_all [formula]

theorem formula_get (p t : ℕ) (es : List Row) (i : ℕ) (hi : i<es.length) :
    (formula p t es)[i]'(by simpa using hi)=
      es[i].1 * ((p*t*((es.map Prod.snd).eraseIdx i).prod : ℕ):ℤ) := by
  induction es generalizing p i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero => simp [formula,denProd,Nat.mul_assoc]
    | succ i =>
      have ht : i<es.length := by simpa using hi
      simpa [formula,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using ih (p*e.2) i ht

def rows {n : ℕ} (a : Vector ℤ n) (b : Vector ℕ n) : List Row :=
  List.ofFn fun v : Fin n => (a[v],b[v])

theorem vector_list {α : Type} {n : ℕ} (v : Vector α n) : v.toList=List.ofFn (fun i : Fin n => v[i]) := by
  apply List.ext_getElem <;> simp

theorem rows_fst {n : ℕ} (a : Vector ℤ n) (b : Vector ℕ n) : (rows a b).map Prod.fst=a.toList := by
  simp [rows,vector_list,List.map_ofFn]
  rfl
theorem rows_snd {n : ℕ} (a : Vector ℤ n) (b : Vector ℕ n) : (rows a b).map Prod.snd=b.toList := by
  simp [rows,vector_list,List.map_ofFn]
  rfl

theorem formula_scaleFees {n : ℕ} (a : Vector ℤ n) (b : Vector ℕ n) (t : ℕ)
    (hb : ∀ v : Fin n, 0<b[v]) : formula 1 t (rows a b)=(scaleFees a b t).toList := by
  apply List.ext_getElem
  · simp [rows]
  · intro i hi hj
    have hv : i<n := by simpa [rows] using hi
    have hc := cofactorCost_value b t ⟨i,hv⟩ (hb ⟨i,hv⟩)
    simp only [cofactorCost,productCost_value,omitAt_value,List.prod_cons] at hc
    rw [formula_get 1 t (rows a b) i (by simpa [rows] using hv),rows_snd]
    simp [rows,scaleFees,TreeBudgetIntegerCost.scaledNumerator,hc]

theorem budget_scaleBudget {n : ℕ} (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT : ℕ)
    (hbT : 0<bT) : aT*((value (prefixEnd [true] (rows a b)):ℕ):ℤ)=scaleBudget b aT bT := by
  have h := scaleBudgetCost_value b aT bT hbT
  simpa [scaleBudgetCost,prefixEnd_value,denProd,rows_snd,value,productCost_value] using h

end UAVProof.A4FeeScaling
