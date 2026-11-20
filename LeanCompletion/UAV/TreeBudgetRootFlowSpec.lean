import LeanCompletion.UAV.TreeBudgetParentPrefixTotal
import LeanCompletion.UAV.TreeBudgetAddWordsTM2

/-! Root-flow semantics and actual accumulator word lengths. Equal list lengths
are a separate guard: a truncated zip must never accept a mismatching H. -/
namespace UAVProof.TreeBudgetRootFlowSpec
open TreeBudgetBinaryCodec TreeBudgetParentArray TreeBudgetAddWordsTM2

def selected (r i p : ℕ) : Bool := decide (i≠r ∧ p=r)

def rootSum (r : ℕ) : ℕ → List ℕ → List ℕ → ℕ
  | _,[],_ => 0
  | _,_,[] => 0
  | i,p::ps,h::hs => (if selected r i p then h else 0)+rootSum r (i+1) ps hs

def accumulated (r : ℕ) : ℕ → List ℕ → List ℕ → Bits → Bits
  | _,[],_,u => u
  | _,_,[],u => u
  | i,p::ps,h::hs,u => accumulated r (i+1) ps hs
      (if selected r i p then addWords u h.bits false else u)

theorem accumulated_value (r i : ℕ) (ps hs : List ℕ) (u : Bits) :
    value (accumulated r i ps hs u)=value u+rootSum r i ps hs := by
  induction ps generalizing i hs u with
  | nil => simp [accumulated,rootSum]
  | cons p ps ih =>
    cases hs with
    | nil => simp [accumulated,rootSum]
    | cons h hs =>
      cases he : selected r i p <;>
        simp [accumulated,rootSum,he,ih,addWords_value,Nat.add_assoc]

/-- Bounds actual stored bits, including high zero padding and rejecting inputs. -/
theorem accumulated_length (r i : ℕ) (ps hs : List ℕ) (u : Bits) :
    (accumulated r i ps hs u).length ≤ u.length+(hs.flatMap encodeNat).length := by
  induction ps generalizing i hs u with
  | nil => simp [accumulated]
  | cons p ps ih =>
    cases hs with
    | nil => simp [accumulated]
    | cons h hs =>
      cases he : selected r i p with
      | false =>
        have ht := ih (i+1) hs u
        simp only [accumulated,he,Bool.false_eq_true,if_false,List.flatMap_cons,List.length_append]
        omega
      | true =>
        have ht := ih (i+1) hs (addWords u h.bits false)
        have ha := addWords_length u h.bits false
        simp only [accumulated,he,if_true,List.flatMap_cons,List.length_append,encodeNat_length]
        simp only [Nat.size_eq_bits_len] at ha
        omega

theorem rootSum_ofFn (n r i : ℕ) (p h : Fin n → ℕ) :
    rootSum r i (List.ofFn p) (List.ofFn h) =
      ∑ v : Fin n, if i+v.val≠r ∧ p v=r then h v else 0 := by
  induction n generalizing i with
  | zero => simp [rootSum]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,rootSum,ih,Fin.sum_univ_succ]
    simp [selected,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rfl

theorem reference (n : ℕ) (P : ParentArray n) (H : Vector ℕ n) :
    rootSum P.root.val 0 (TreeBudgetParentWalkTM2.table P) H.toList =
      (TreeBudgetCostedCandidates.rootCountCost P H).value := by
  have hp : TreeBudgetParentWalkTM2.table P=List.ofFn (fun v : Fin n => P.parents[v].val) := by
    apply List.ext_getElem <;> simp [TreeBudgetParentWalkTM2.table]
  have hh : H.toList=List.ofFn (fun v : Fin n => H[v]) := by
    apply List.ext_getElem <;> simp
  rw [hp,hh,rootSum_ofFn]
  simp [TreeBudgetCostedCandidates.rootCountCost,
    TreeBudgetCostedCandidates.sumNatCost_value,List.map_ofFn,List.sum_ofFn,Fin.ext_iff]

structure Raw where
  routes : ℕ
  vertices : ℕ
  root : ℕ
  parents : List ℕ
  demands : List ℕ
  rest : Bits
  deriving DecidableEq

def front (a : Raw) : TreeBudgetParentPrefix.Raw :=
  ⟨a.routes,a.vertices,a.root,a.parents,encodeNats a.demands ++ a.rest⟩
def encode (a : Raw) := TreeBudgetParentPrefix.encode (front a)
def parse (s : Bits) : Option Raw := do
  let a ← TreeBudgetParentPrefix.parse s
  let (hs,t) ← parseNats a.rest
  return ⟨a.routes,a.vertices,a.root,a.parents,hs,t⟩

theorem parse_encode (a : Raw) : parse (encode a)=some a := by
  simp [parse,encode,TreeBudgetParentPrefix.parse_encode,front]

theorem canonical (s : Bits) (a : Raw) (h : parse s=some a) : s=encode a := by
  simp only [parse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨b,hb,⟨⟨hs,t⟩,hh,ha⟩⟩ := h
  cases ha
  rw [TreeBudgetParentPrefix.canonical s b hb]
  have ht := parseList_canonical encodeNat parseNat parseNat_canonical b.rest t hs hh
  simp [encode,front,TreeBudgetParentPrefix.encode,ht]

def listOK (a : TreeBudgetParentPrefix.Raw) (hs : List ℕ) : Bool :=
  decide (hs.length=a.parents.length) && decide (rootSum a.root 0 a.parents hs=a.routes)
def suffixOK (a : TreeBudgetParentPrefix.Raw) : Bool := (parseNats a.rest).any fun e => listOK a e.1
def accepted (s : Bits) : Bool := TreeBudgetParentPrefix.accepted s &&
  (TreeBudgetParentPrefix.parse s).any suffixOK

theorem accepted_encode (a : Raw) : accepted (encode a) =
    (TreeBudgetParentPrefix.accepted (encode a) && listOK (front a) a.demands) := by
  simp [accepted,encode,TreeBudgetParentPrefix.parse_encode,suffixOK,front]

theorem accepts_iff (a : Raw) : accepted (encode a)=true ↔
    a.vertices=a.parents.length ∧ (decodeParents a.root a.parents).isSome=true ∧
    a.demands.length=a.vertices ∧ rootSum a.root 0 a.parents a.demands=a.routes := by
  rw [accepted_encode]
  simp only [encode,TreeBudgetParentPrefix.accepted_encode,front,listOK,Bool.and_eq_true,
    decide_eq_true_eq]
  aesop

theorem occupied (a : Raw) : (a.demands.flatMap encodeNat).length ≤ (encode a).length ∧
    (TreeBudgetParentPrefix.body (front a)).length≤(encode a).length ∧
    a.routes.bits.length≤(encode a).length ∧ a.root.bits.length≤(encode a).length ∧
    a.parents.length≤(encode a).length := by
  have h := TreeBudgetParentPrefix.occupied (front a)
  have he : (a.demands.flatMap encodeNat).length ≤ (front a).rest.length := by
    simp only [front,encodeNats,encodeList,List.length_append]
    omega
  dsimp [encode] at *
  dsimp [front] at h he ⊢
  omega

end UAVProof.TreeBudgetRootFlowSpec
