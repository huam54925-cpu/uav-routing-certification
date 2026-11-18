import LeanCompletion.UAV.TreeBudgetSubtreeHeapDedup
import LeanCompletion.UAV.TreeBudgetChargedCache

/-! Primitive charges for the linked deduplication pass. Reference loads,
node construction, and key decoding/comparison have disjoint step counters.
Temporary cells count cumulative allocations by the bit primitives. Host control
and bookkeeping of the observation counters are outside these three counters. -/
namespace UAVProof.TreeBudgetSubtreeHeapDedup.Work
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetAddressedBlocks
open TreeBudgetSharedAnswerStore TreeBudgetBitMachine TreeBudgetBitPrimitives
open TreeBudgetChargedCache TreeBudgetCostedCodec TreeBudgetSearchStore

structure Charges where
  refSteps : Nat := 0
  nodeSteps : Nat := 0
  keySteps : Nat := 0
  temporaryCells : Nat := 0
  persistentSlots : Nat := 0
  deriving Inhabited

def Charges.add (a b : Charges) : Charges :=
  ⟨a.refSteps+b.refSteps, a.nodeSteps+b.nodeSteps, a.keySteps+b.keySteps,
    a.temporaryCells+b.temporaryCells, a.persistentSlots+b.persistentSlots⟩

structure Measured (α : Type) where
  value : α
  work : Charges

instance : Monad Measured where
  pure a := ⟨a, {}⟩
  bind a f := let b := f a.value; ⟨b.value, a.work.add b.work⟩

@[simp] theorem pure_value {α : Type} (x : α) : (pure x : Measured α).value = x := rfl
@[simp] theorem bind_value {α β : Type} (x : Measured α) (f : α → Measured β) :
    (x >>= f).value = (f x.value).value := rfl

/-- Charge offset arithmetic and transfer both the selected address and the
reference payload. Measuring each word's width includes its workspace. -/
def field (h : Heap) (a i : Nat) : Measured Nat :=
  let addr := addNatD a i
  let w := widthNat addr.value
  let cell := readCell w.value h addr.value
  let base := addr.steps + w.steps + cell.steps + 1
  let tmp := addr.allocations + w.allocations + cell.allocations
  match cell.value with
  | some (.ref r) =>
    let p := widthNat r
    let x := transferAddress p.value r
    ⟨x.value, { refSteps := base + p.steps + x.steps, temporaryCells := tmp + p.allocations + x.allocations }⟩
  | _ => ⟨0, { refSteps := base, temporaryCells := tmp }⟩

@[simp] theorem field_value (h : Heap) (a i : Nat) : (field h a i).value = refAt h (a+i) := by
  simp only [field, addNatD_value, (widthNat_spec _).1, refAt,
    readCell_value _ _ _ (Nat.lt_size_self _)]
  cases read h (a+i) with
  | none => rfl
  | some s => cases s <;> simp [transferAddress_value _ _ (Nat.lt_size_self _)]

private def maxD (a b : Nat) : Costed Nat :=
  let q := leNatD a b
  ⟨if q.value then b else a, q.steps+1, q.allocations⟩

private theorem maxD_value (a b : Nat) : (maxD a b).value = max a b := by
  by_cases h : a ≤ b <;> simp [maxD, h, max_def]

def consNode (h : Heap) (x t : Nat) : Measured (Nat × Heap) :=
  let top := addNatD h.size 3
  let refs := maxD x t
  let bound := maxD top.value refs.value
  let w := widthNat bound.value
  let node := nodeD w.value h [.bit true, .ref x, .ref t]
  let work : Charges := {
    nodeSteps := top.steps + refs.steps + bound.steps + w.steps + node.steps
    temporaryCells := top.allocations + refs.allocations + bound.allocations + w.allocations
    persistentSlots := node.allocations }
  ⟨node.value, work⟩

@[simp] theorem consNode_value (h : Heap) (x t : Nat) : (consNode h x t).value = push h x t := by
  simp [consNode, push, maxD_value, (widthNat_spec _).1]

theorem consNode_slots (h : Heap) (x t : Nat) : (consNode h x t).work.persistentSlots = 3 := by
  simp [consNode]

def loadKey (base : Heap) (a : Nat) : Measured (Option (List Bool)) :=
  let k := blobRead base a
  ⟨k.value, { keySteps := k.steps, temporaryCells := k.allocations }⟩

def compareKeys (x y : Option (List Bool)) : Measured Bool :=
  match x, y with
  | some xs, some ys =>
    let q := eqBitsD xs ys
    ⟨q.value, { keySteps := q.steps + 1, temporaryCells := q.allocations }⟩
  | none, none => ⟨true, { keySteps := 1 }⟩
  | _, _ => ⟨false, { keySteps := 1 }⟩

@[simp] theorem compareKeys_value (x y : Option (List Bool)) :
    (compareKeys x y).value = decide (x = y) := by
  cases x <;> cases y <;> simp [compareKeys]

def keyMap (base : Heap) (z : Nat) : Nat → Heap → Nat → Nat → Measured Result
  | 0, h, _, stack => pure ⟨h,z,stack⟩
  | n+1, h, a, stack => do
    let x ← field h a 1
    let key ← field base x 1
    let f ← consNode h key stack
    let t ← field h a 2
    let r ← keyMap base z n f.2 t f.1
    let k ← field r.heap r.stack 1
    let out ← consNode r.heap k r.head
    let parent ← field r.heap r.stack 2
    return ⟨out.2,out.1,parent⟩

@[simp] theorem keyMap_value (base : Heap) (z n : Nat) (h : Heap) (a stack : Nat) :
    (keyMap base z n h a stack).value = mapKeys (fun x => refAt base (x+1)) z n h a stack := by
  induction n generalizing h a stack <;> simp [keyMap, mapKeys, *]

def scan (base h : Heap) (x : Option (List Bool)) : Nat → Nat → Measured (Bool × Nat)
  | 0, _ => pure (false, 0)
  | n+1, a => do
    let k ← field h a 1
    let y ← loadKey base k
    if ← compareKeys x y then return (true,1)
    let t ← field h a 2
    let r ← scan base h x n t
    return (r.1,r.2+1)

@[simp] theorem scan_value (base h : Heap) (hh : WellFormed base) (x : Option (List Bool))
    (n a : Nat) : (scan base h x n a).value = member (readBlob base) h x n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [scan, bind_value, field_value, compareKeys_value, loadKey, blobRead_value _ _ hh,
      decide_eq_true_eq, member]
    split <;> simp [ih]

def execute (base : Heap) (z : Nat) : Nat → Heap → Nat → Nat → Measured DedupResult
  | 0, h, _, stack => pure ⟨⟨h,z,stack⟩,0,0,0⟩
  | n+1, h, a, stack => do
    let x ← field h a 1
    let f ← consNode h x stack
    let t ← field h a 2
    let r ← execute base z n f.2 t f.1
    let keys ← keyMap base z r.length r.heap r.head r.stack
    let entry ← field keys.heap keys.stack 1
    let parent ← field keys.heap keys.stack 2
    let k ← field base entry 1
    let v ← loadKey base k
    let hit ← scan base keys.heap v r.length keys.head
    let out ← if hit.1 then pure (r.head,keys.heap) else consNode keys.heap entry r.head
    return ⟨⟨out.2,out.1,parent⟩, if hit.1 then r.length else r.length+1,
      r.comparisons+hit.2, r.keyMapCells+r.length⟩

theorem execute_value (base : Heap) (hh : WellFormed base) (z n : Nat) (h : Heap) (a stack : Nat) :
    (execute base z n h a stack).value =
      run (fun x => refAt base (x+1)) (readBlob base) z n h a stack := by
  induction n generalizing h a stack with
  | zero => rfl
  | succ n ih =>
    simp only [execute, bind_value, field_value, consNode_value, ih, keyMap_value, loadKey,
      blobRead_value _ _ hh, scan_value _ _ hh, run]
    split <;> simp

/-- Run with the original input heap as the immutable prefix. -/
def dedupD (h : Heap) (z a n : Nat) := execute h z n h a z

theorem dedupD_value (h : Heap) (hh : WellFormed h) (z a n : Nat) :
    (dedupD h z a n).value = dedup h z a n := execute_value h hh z n h a z

private theorem bind_slots {α β : Type} (a : Measured α) (f : α → Measured β) :
    (a >>= f).work.persistentSlots = a.work.persistentSlots + (f a.value).work.persistentSlots := rfl

private theorem pure_slots {α : Type} (a : α) : (pure a : Measured α).work.persistentSlots = 0 := rfl

private theorem field_slots (h : Heap) (a i : Nat) : (field h a i).work.persistentSlots = 0 := by
  dsimp only [field]
  split <;> rfl

private theorem compare_slots (x y : Option (List Bool)) :
    (compareKeys x y).work.persistentSlots = 0 := by cases x <;> cases y <;> rfl

theorem keyMap_slots (base : Heap) (z n : Nat) (h : Heap) (a stack : Nat) :
    (keyMap base z n h a stack).work.persistentSlots = 6*n := by
  induction n generalizing h a stack with
  | zero => rfl
  | succ n ih =>
    simp only [keyMap, bind_slots, field_slots, consNode_slots, ih, pure_slots]
    omega

theorem scan_slots (base h : Heap) (x : Option (List Bool)) (n a : Nat) :
    (scan base h x n a).work.persistentSlots = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [scan, bind_slots, field_slots, loadKey, compare_slots, Nat.zero_add]
    split <;> simp only [pure_slots, bind_slots, field_slots, ih, Nat.zero_add]

/-- Summing nodeD allocation counters along the real execution gives the
same formula as the size difference proved from the heap representation. -/
theorem execute_slots (base : Heap) (z n : Nat) (h : Heap) (a stack : Nat) :
    let r := execute base z n h a stack
    r.work.persistentSlots = 3*n + 6*r.value.keyMapCells + 3*r.value.length := by
  induction n generalizing h a stack with
  | zero => rfl
  | succ n ih =>
    simp only [execute, bind_slots, bind_value, field_slots, consNode_slots,
      keyMap_slots, scan_slots, loadKey, Nat.zero_add]
    split <;> simp only [bind_slots, bind_value, pure_value, pure_slots, consNode_slots, ih,
      Nat.add_zero] <;> omega

theorem charged_slots_eq_growth (h : Heap) (hh : WellFormed h) (z a : Nat)
    (xs : List Nat) (hc : Chain h z a xs) :
    let r := dedupD h z a xs.length
    r.value.heap.size = h.size + r.work.persistentSlots := by
  have hw := execute_slots h z xs.length h a z
  change (dedupD h z a xs.length).work.persistentSlots = _ at hw
  have hv := dedupD_value h hh z a xs.length
  have hs := dedup_correct h z a xs hc
  change (dedupD h z a xs.length).value.heap.size = _
  rw [hw]
  change (dedupD h z a xs.length).value.heap.size = h.size + (3*xs.length +
    6*(dedupD h z a xs.length).value.keyMapCells + 3*(dedupD h z a xs.length).value.length)
  rw [hv, hs.2.2.2.2.1, hs.2.2.1, hs.2.2.2.2.2.2]
  omega

end UAVProof.TreeBudgetSubtreeHeapDedup.Work
