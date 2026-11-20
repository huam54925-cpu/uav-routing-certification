import LeanCompletion.UAV.TreeBudgetWholeTreeTotal
import LeanCompletion.UAV.TreeBudgetEntryTM2

/-! The actual instance prefix has three scalar headers followed by a counted
parent list. The remaining input starts at H and is deliberately not parsed. -/
namespace UAVProof.TreeBudgetParentPrefix
open TreeBudgetBinaryCodec TreeBudgetParentArray

structure Raw where
  routes : ℕ
  vertices : ℕ
  root : ℕ
  parents : List ℕ
  rest : Bits
  deriving DecidableEq

def encode (a : Raw) : Bits := encodeNat a.routes ++ (encodeNat a.vertices ++
  (encodeNat a.root ++ (encodeNats a.parents ++ a.rest)))

def parse (s : Bits) : Option Raw := do
  let (m,s) ← parseNat s
  let (n,s) ← parseNat s
  let ((r,p),s) ← TreeBudgetSparseCodec.parseEntry s
  return ⟨m,n,r,p,s⟩

theorem parse_encode (a : Raw) : parse (encode a) = some a := by
  simp [parse,encode,TreeBudgetSparseCodec.parseEntry,parseNat_append]

theorem canonical (s : Bits) (a : Raw) (h : parse s = some a) : s = encode a := by
  simp only [parse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨m,t⟩,hm,⟨⟨n,u⟩,hn,⟨⟨⟨r,p⟩,v⟩,hr,ha⟩⟩⟩ := h
  cases ha
  rw [parseNat_canonical s t m hm,parseNat_canonical t u n hn,
    TreeBudgetSparseCodec.parseEntry_canonical u v (r,p) hr]
  simp [encode,TreeBudgetSparseCodec.encodeEntry,List.append_assoc]

def body (a : Raw) := a.parents.flatMap encodeNat

theorem occupied (a : Raw) :
    (encodeNat a.root).length+(body a).length ≤ (encode a).length ∧
    a.routes.bits.length ≤ (encode a).length ∧ a.vertices.bits.length ≤ (encode a).length ∧
    a.root.bits.length ≤ (encode a).length ∧ a.parents.length ≤ (encode a).length ∧
    a.rest.length ≤ (encode a).length := by
  have hp := length_le_flatMap encodeNat encodeNat_nonempty a.parents
  simp only [encode,body,encodeNats,encodeList,List.length_append,encodeNat_length,
    Nat.size_eq_bits_len] at hp ⊢
  omega

def accepted (s : Bits) : Bool := (parse s).any fun a =>
  decide (a.vertices = a.parents.length) && (decodeParents a.root a.parents).isSome

def typed (a : Raw) (hr : a.root < a.parents.length)
    (hp : ∀ x ∈ a.parents, x < a.parents.length) : ParentArray a.parents.length :=
  ⟨⟨a.root,hr⟩,Vector.ofFn fun i => ⟨a.parents[i],hp _ (List.getElem_mem i.isLt)⟩⟩

theorem typed_table (a : Raw) (hr : a.root < a.parents.length)
    (hp : ∀ x ∈ a.parents, x < a.parents.length) :
    TreeBudgetParentWalkTM2.table (typed a hr hp) = a.parents := by
  apply List.ext_getElem
  · simp [TreeBudgetParentWalkTM2.table,typed]
  · intro i hi hj
    simp [TreeBudgetParentWalkTM2.table,typed]

theorem typed_body (a : Raw) (hr : a.root < a.parents.length)
    (hp : ∀ x ∈ a.parents, x < a.parents.length) :
    TreeBudgetParentWalkTM2.body (typed a hr hp) = body a := by
  rw [TreeBudgetParentWalkTM2.body,typed_table]
  rfl

theorem decode_typed (a : Raw) (hr : a.root < a.parents.length)
    (hp : ∀ x ∈ a.parents, x < a.parents.length) :
    (decodeParents a.root a.parents).isSome =
      (TreeBudgetCostedInput.validateCost (typed a hr hp)).value := by
  simp only [decodeParents,dif_pos hr,dif_pos hp,TreeBudgetCostedInput.validateCost_value,typed]
  split
  · rename_i h
    exact h.symm
  · rename_i h
    exact (Bool.eq_false_iff.mpr h).symm

theorem accepted_encode (a : Raw) : accepted (encode a) =
    (decide (a.vertices = a.parents.length) && (decodeParents a.root a.parents).isSome) := by
  simp [accepted,parse_encode]

end UAVProof.TreeBudgetParentPrefix
