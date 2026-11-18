import LeanCompletion.UAV.TreeBudgetSharedAnswerStore
import LeanCompletion.UAV.TreeBudgetSubtreeScalarDedup

/-! Three-slot input frames, key-map frames, key cells and output cells share a
nil sentinel. The input length is supplied with its chain. Keys and payloads
belong to the immutable input prefix. Only their references enter new cells. -/
namespace UAVProof.TreeBudgetSubtreeHeapDedup
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetAddressedBlocks
open TreeBudgetSharedAnswerStore TreeBudgetBitMachine TreeBudgetSearchStore
open TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed

def refAt (h : Heap) (a : Nat) : Nat :=
  match (readCell a.size h a).value with
  | some (.ref p) => p
  | _ => 0

abbrev Header (h : Heap) (a x t : Nat) :=
  Represents h ⟨a,3⟩ [.bit true, .ref x, .ref t]

theorem fields {h : Heap} {a x t : Nat} (hr : Header h a x t) :
    refAt h (a+1) = x ∧ refAt h (a+2) = t := by
  have h₁ := hr.2.2 1 (by simp)
  have h₂ := hr.2.2 2 (by simp)
  simp [refAt, readCell_value _ _ _ (Nat.lt_size_self _), h₁, h₂]

def push (h : Heap) (x t : Nat) : Nat × Heap :=
  let w := (max (h.size + 3) (max x t)).size
  (nodeD w h [.bit true, .ref x, .ref t]).value

theorem push_eq (h : Heap) (x t : Nat) :
    push h x t = (h.size, allocateBlock h [.bit true, .ref x, .ref t]) := by
  let w := (max (h.size + 3) (max x t)).size
  have hw : max (h.size+3) (max x t) < 2^w := Nat.lt_size_self _
  have ha : h.size < 2^w := by omega
  have hs : ∀ a, Slot.ref a ∈ [.bit true, .ref x, .ref t] → a < 2^w := by
    intro a ha
    simp at ha
    rcases ha with rfl | rfl <;> omega
  change (nodeD w h _).value = _
  simp only [nodeD, readAddress_value _ _ ha, allocateSlotsD_value w h [.bit true,.ref x,.ref t]
    (by simp; omega) hs]

theorem pushed (h : Heap) (x t : Nat) :
    Header (push h x t).2 (push h x t).1 x t ∧
    Extends h (push h x t).2 ∧ (push h x t).2.size = h.size + 3 := by
  rw [push_eq]
  exact ⟨allocateTyped_represents .., allocateBlock_extends .., by simp [allocateBlock_size]⟩

inductive Chain (h : Heap) (nilRef : Nat) : Nat → List Nat → Prop where
  | nil : Chain h nilRef nilRef []
  | cons {a x t xs} : Header h a x t → Chain h nilRef t xs → Chain h nilRef a (x::xs)

theorem Chain.persist {h g : Heap} {z a xs} (hc : Chain h z a xs) (ext : Extends h g) :
    Chain g z a xs := by
  induction hc with
  | nil => exact .nil
  | cons hdr _ ih => exact .cons (represents_of_extends ext _ _ hdr) ih

structure Result where
  heap : Heap
  head : Nat
  stack : Nat

/-- Read the entire suffix, then pop key frames to rebuild its original order. -/
def mapKeys (keyRef : Nat → Nat) (z : Nat) : Nat → Heap → Nat → Nat → Result
  | 0, h, _, stack => ⟨h, z, stack⟩
  | n+1, h, a, stack =>
    let f := push h (keyRef (refAt h (a+1))) stack
    let r := mapKeys keyRef z n f.2 (refAt h (a+2)) f.1
    let out := push r.heap (refAt r.heap (r.stack+1)) r.head
    ⟨out.2, out.1, refAt r.heap (r.stack+2)⟩

theorem mapKeys_spec (keyRef : Nat → Nat) (z : Nat) (xs : List Nat) (h : Heap)
    (a stack : Nat) (hc : Chain h z a xs) :
    let r := mapKeys keyRef z xs.length h a stack
    Chain r.heap z r.head (xs.map keyRef) ∧ r.stack = stack ∧
      Extends h r.heap ∧ r.heap.size = h.size + 6*xs.length := by
  induction xs generalizing h a stack with
  | nil => exact ⟨.nil, rfl, extends_refl _, by simp [mapKeys]⟩
  | cons x xs ih =>
    cases hc with
    | @cons _ _ t _ hdr tail =>
      obtain ⟨hx, ht⟩ := fields hdr
      let f := push h (keyRef x) stack
      obtain ⟨hf, ef, sf⟩ := pushed h (keyRef x) stack
      let r := mapKeys keyRef z xs.length f.2 t f.1
      obtain ⟨hr, returned, er, sr⟩ := ih f.2 t f.1 (tail.persist ef)
      change r.stack = f.1 at returned
      have frame : Header r.heap r.stack (keyRef x) stack := by
        rw [returned]
        exact represents_of_extends er _ _ hf
      obtain ⟨hk, hs⟩ := fields frame
      obtain ⟨ho, eo, so⟩ := pushed r.heap (keyRef x) r.head
      simp only [List.length_cons, mapKeys, hx, ht, List.map_cons]
      change Chain (push r.heap (refAt r.heap (r.stack+1)) r.head).2 z
        (push r.heap (refAt r.heap (r.stack+1)) r.head).1 (keyRef x :: xs.map keyRef) ∧
        refAt r.heap (r.stack+2) = stack ∧ _
      rw [hk, hs]
      refine ⟨.cons ho (hr.persist eo), rfl, extends_trans ef (extends_trans er eo), ?_⟩
      change (push r.heap (keyRef x) r.head).2.size = _
      change r.heap.size = f.2.size + _ at sr
      change f.2.size = _ at sf
      omega

/-- Scans key references in order; equality acts on the represented value. -/
def member {κ : Type} [DecidableEq κ] (decode : Nat → κ) (h : Heap) (x : κ) :
    Nat → Nat → Bool × Nat
  | 0, _ => (false, 0)
  | n+1, a =>
    if x = decode (refAt h (a+1)) then (true, 1)
    else let r := member decode h x n (refAt h (a+2))
         (r.1, r.2+1)

theorem member_spec {κ : Type} [DecidableEq κ] (decode : Nat → κ) (h : Heap)
    (z a : Nat) (xs : List Nat) (hc : Chain h z a xs) (x : κ) :
    member decode h x xs.length a = memberCounted x (xs.map decode) := by
  induction hc with
  | nil => rfl
  | cons hdr _ ih =>
    obtain ⟨hy, ht⟩ := fields hdr
    simp only [member, hy, ht, List.map_cons, memberCounted, ih]

structure DedupResult extends Result where
  length : Nat
  comparisons : Nat
  keyMapCells : Nat

def run {κ : Type} [DecidableEq κ] (keyRef : Nat → Nat) (decode : Nat → κ)
    (z : Nat) : Nat → Heap → Nat → Nat → DedupResult
  | 0, h, _, stack => ⟨⟨h,z,stack⟩,0,0,0⟩
  | n+1, h, a, stack =>
    let f := push h (refAt h (a+1)) stack
    let r := run keyRef decode z n f.2 (refAt h (a+2)) f.1
    let keys := mapKeys keyRef z r.length r.heap r.head r.stack
    let x := refAt keys.heap (keys.stack+1)
    let tail := refAt keys.heap (keys.stack+2)
    let hit := member decode keys.heap (decode (keyRef x)) r.length keys.head
    let out := if hit.1 then (r.head, keys.heap) else push keys.heap x r.head
    ⟨⟨out.2,out.1,tail⟩, if hit.1 then r.length else r.length+1,
      r.comparisons+hit.2, r.keyMapCells+r.length⟩

/-- The input entry preserves the address of its payload, independently of the
key address. Equal bitstrings may reside at different addresses. -/
def EntryRep (h : Heap) (a key payload : Nat) (bits : List Bool) : Prop :=
  Header h a key payload ∧ BlobRep h key bits

theorem entry_key {h : Heap} {a key payload : Nat} {bits : List Bool}
    (hr : EntryRep h a key payload bits) :
    readBlob h (refAt h (a+1)) = some bits ∧ refAt h (a+2) = payload := by
  obtain ⟨hk, hp⟩ := fields hr.1
  exact ⟨hk ▸ readBlob_correct h key bits hr.2, hp⟩

theorem entry_persist {h g : Heap} {a key payload : Nat} {bits : List Bool}
    (ext : Extends h g) (hr : EntryRep h a key payload bits) : EntryRep g a key payload bits :=
  ⟨represents_of_extends ext _ _ hr.1, blobRep_persist ext _ _ hr.2⟩

/-- An entry stores a key-blob reference in field 1; field 2 can address an
arbitrary payload. The output chain borrows the complete original entry. -/
def dedup (h : Heap) (nilRef head length : Nat) : DedupResult :=
  run (fun a => refAt h (a+1)) (readBlob h) nilRef length h head nilRef

/-- The heap result represents the scalar trace, including order, the rightmost
entry address at collisions, the full map volume and short-circuit comparisons. -/
theorem run_spec {κ : Type} [DecidableEq κ] (keyRef : Nat → Nat) (decode : Nat → κ)
    (z : Nat) (xs : List Nat) (h : Heap) (a stack : Nat) (hc : Chain h z a xs) :
    let r := run keyRef decode z xs.length h a stack
    let d := dedupKeyCounted (decode ∘ keyRef) xs
    Chain r.heap z r.head d.value ∧ r.stack = stack ∧ r.length = d.value.length ∧
      r.comparisons = d.comparisons ∧ r.keyMapCells = d.keyMapCells ∧ Extends h r.heap ∧
      r.heap.size = h.size + 3*xs.length + 6*d.keyMapCells + 3*d.value.length := by
  induction xs generalizing h a stack with
  | nil => exact ⟨.nil, rfl, rfl, rfl, rfl, extends_refl _, by simp [run, dedupKeyCounted]⟩
  | cons x xs ih =>
    cases hc with
    | @cons _ _ t _ hdr tail =>
      obtain ⟨hx, ht⟩ := fields hdr
      let f := push h x stack
      obtain ⟨hf, ef, sf⟩ := pushed h x stack
      let r := run keyRef decode z xs.length f.2 t f.1
      let d := dedupKeyCounted (decode ∘ keyRef) xs
      obtain ⟨hr, ret, len, cmp, maps, er, sr⟩ := ih f.2 t f.1 (tail.persist ef)
      change r.length = d.value.length at len
      let keys := mapKeys keyRef z r.length r.heap r.head r.stack
      have mk := mapKeys_spec keyRef z d.value r.heap r.head r.stack hr
      rw [← len] at mk
      obtain ⟨hk, retk, ek, sk⟩ := mk
      have frame : Header keys.heap keys.stack x stack := by
        change keys.stack = r.stack at retk
        rw [retk, ret]
        exact represents_of_extends (extends_trans er ek) _ _ hf
      obtain ⟨fx, ft⟩ := fields frame
      let hit := memberCounted ((decode ∘ keyRef) x) (d.value.map (decode ∘ keyRef))
      have hm : member decode keys.heap (decode (keyRef x)) r.length keys.head = hit := by
        rw [len, ← List.length_map (f := keyRef) (as := d.value)]
        simpa only [List.map_map] using member_spec decode keys.heap z keys.head
          (d.value.map keyRef) hk (decode (keyRef x))
      have base := extends_trans ef (extends_trans er ek)
      have old := hr.persist ek
      have extra := pushed keys.heap x r.head
      change r.heap.size = f.2.size + 3*xs.length + 6*d.keyMapCells + 3*d.value.length at sr
      change f.2.size = h.size+3 at sf
      change keys.heap.size = r.heap.size + 6*_ at sk
      change r.keyMapCells = d.keyMapCells at maps
      change r.comparisons = d.comparisons at cmp
      simp only [List.length_cons, run, hx, ht, dedupKeyCounted]
      change (let y := refAt keys.heap (keys.stack+1)
        let scan := member decode keys.heap (decode (keyRef y)) r.length keys.head
        let out := if scan.1 then (r.head, keys.heap) else push keys.heap y r.head
        let entries := if hit.1 then d.value else x :: d.value
        Chain out.2 z out.1 entries ∧ refAt keys.heap (keys.stack+2) = stack ∧
          (if scan.1 then r.length else r.length+1) = entries.length ∧
          r.comparisons + scan.2 = d.comparisons + hit.2 ∧
          r.keyMapCells + r.length = d.keyMapCells + (d.value.map (decode ∘ keyRef)).length ∧
          Extends h out.2 ∧ out.2.size = h.size + 3*(xs.length+1) +
            6*(d.keyMapCells + (d.value.map (decode ∘ keyRef)).length) + 3*entries.length)
      dsimp only
      rw [fx, ft, hm]
      cases hh : hit.1 <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_map,
        List.length_cons, len, cmp, maps, true_and]
      · exact ⟨.cons extra.1 (old.persist extra.2.1), extends_trans base extra.2.1, by omega⟩
      · exact ⟨old, base, by omega⟩

/-- Specialization to the actual input blobs and the existing scalar deduplication
trace. The equality concerns the sizes of the input and returned heaps. -/
theorem dedup_correct (h : Heap) (z a : Nat) (xs : List Nat) (hc : Chain h z a xs) :
    let key := fun x => readBlob h (refAt h (x+1))
    let d := (TreeBudgetSubtreeScalar.dedupTraceC key (fun u v => ⟨decide (u=v), 1⟩) xs).value
    let r := dedup h z a xs.length
    Chain r.heap z r.head d.value ∧ r.stack = z ∧ r.length = d.value.length ∧
      r.comparisons = d.comparisons ∧ r.keyMapCells = d.keyMapCells ∧ Extends h r.heap ∧
      r.heap.size = h.size + 3*xs.length + 6*d.keyMapCells + 3*d.value.length := by
  dsimp only
  rw [TreeBudgetSubtreeScalar.dedupTraceC_value _ _ (fun _ _ => rfl)]
  exact run_spec (fun x => refAt h (x+1)) (readBlob h) z xs h a z hc

end UAVProof.TreeBudgetSubtreeHeapDedup
