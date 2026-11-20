import LeanCompletion.UAV.TreeBudgetRootFlowTotal

/-! Exact contract of the fee suffix consumed after `saved_fields`. -/
namespace UAVProof.A4FeeTailSpec
open TreeBudgetBinaryCodec TreeBudgetParentArray

structure Fields where
  nums : List ℤ
  dens : List ℕ
  budgetNum : ℤ
  budgetDen : ℕ
  deriving DecidableEq, Repr

def wire (f : Fields) : Bits :=
  encodeInts f.nums ++ encodeNats f.dens ++ encodeInt f.budgetNum ++ encodeNat f.budgetDen

def good (n : ℕ) (f : Fields) : Bool :=
  decide (f.nums.length = n) && decide (f.dens.length = n) &&
    denominatorsPositiveB f.dens f.budgetDen

def readPrefix (s : Bits) : Option (Fields × Bits) := do
  let (a, t₁) ← parseInts s
  let (d, t₂) ← parseNats t₁
  let (b, t₃) ← parseInt t₂
  let (q, u) ← parseNat t₃
  pure (⟨a, d, b, q⟩, u)

def read (n : ℕ) (s : Bits) : Option Fields := do
  let (f, u) ← readPrefix s
  if u = [] ∧ good n f = true then some f else none

theorem prefix_append (f : Fields) (u : Bits) :
    readPrefix (wire f ++ u) = some (f,u) := by
  cases f
  simp [readPrefix, wire, List.append_assoc, parseInts_append, parseNats_append,
    parseInt_append, parseNat_append]

theorem prefix_canonical (s u : Bits) (f : Fields) (h : readPrefix s = some (f,u)) :
    s = wire f ++ u := by
  simp only [readPrefix, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a,t₁⟩, ha, ⟨⟨d,t₂⟩, hd, ⟨⟨b,t₃⟩, hb, ⟨⟨q,t₄⟩, hq, he⟩⟩⟩⟩ := h
  cases he
  dsimp only at hd hb hq ⊢
  rw [parseList_canonical encodeInt parseInt parseInt_canonical _ _ _ ha,
      parseList_canonical encodeNat parseNat parseNat_canonical _ _ _ hd,
      parseInt_canonical _ _ _ hb, parseNat_canonical _ _ _ hq]
  simp [wire, List.append_assoc]

theorem read_iff (n : ℕ) (s : Bits) (f : Fields) :
    read n s = some f ↔ s = wire f ∧ good n f = true := by
  constructor
  · intro h
    simp only [read, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨g,u⟩, hp, h⟩ := h
    dsimp only at h
    split_ifs at h with hg
    have he : g = f := Option.some.inj h
    simpa only [← he] using
      And.intro (show s = wire g by simpa only [hg.1, List.append_nil] using prefix_canonical s u g hp) hg.2
  · rintro ⟨rfl,hg⟩
    have hp := prefix_append f []
    rw [List.append_nil] at hp
    simp [read,hp,hg]

theorem good_iff (n : ℕ) (f : Fields) :
    good n f = true ↔ f.nums.length = n ∧ f.dens.length = n ∧
      0 < f.budgetDen ∧ ∀ d ∈ f.dens, 0 < d := by
  simp [good, denominatorsPositiveB_eq_true, and_assoc]

def rebuild (a : TreeBudgetRootFlowSpec.Raw) (f : Fields) : RawInput :=
  ⟨a.vertices,a.root,a.parents,a.demands,f.nums,f.dens,f.budgetNum,f.budgetDen⟩

theorem rebuild_wire (s : Bits) (a : TreeBudgetRootFlowSpec.Raw) (f : Fields)
    (hp : TreeBudgetRootFlowSpec.parse s = some a) (ht : read a.vertices a.rest = some f) :
    s = TreeBudgetSparseVerifier.encodeSpecified a.routes (rebuild a f) := by
  rw [TreeBudgetRootFlowSpec.canonical s a hp]
  have hr := ((read_iff _ _ _).mp ht).1
  simp [TreeBudgetRootFlowSpec.encode,TreeBudgetRootFlowSpec.front,TreeBudgetParentPrefix.encode,
    TreeBudgetSparseVerifier.encodeSpecified,rebuild,encodeInput,hr,wire,List.append_assoc]

theorem parseInstance_finish (s : Bits) (a : TreeBudgetRootFlowSpec.Raw) (f : Fields)
    (hp : TreeBudgetRootFlowSpec.parse s = some a) (ht : read a.vertices a.rest = some f)
    (hn : a.parents.length = a.vertices) (hh : a.demands.length = a.vertices) :
    TreeBudgetSparseVerifier.parseInstance s =
      TreeBudgetSparseVerifier.decodeSpecified a.routes (rebuild a f) := by
  have hg := (good_iff _ _).mp ((read_iff _ _ _).mp ht).2
  have hs : Shape (rebuild a f) := ⟨hn,hh,hg.1,hg.2.1⟩
  rw [rebuild_wire s a f hp ht, TreeBudgetSparseVerifier.parseInstance_encode _ _ hs]

end UAVProof.A4FeeTailSpec
