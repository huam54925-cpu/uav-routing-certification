import LeanCompletion.UAV.TreeBudgetColumnCheckTotal
import LeanCompletion.UAV.TreeBudgetSparseVerifier

namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetCertificate A4ColumnAccumulator

theorem columnSum_toRaw {n : ℕ} (C : Certificate (Fin n)) (v : Fin n) :
    columnSum v.val (toRaw C)=(List.ofFn fun i => C.count i*C.row i v).sum := by
  have h (i : Fin C.size) : (List.ofFn (C.row i))[v.val]?.getD 0=C.row i v := by
    rw [List.getElem?_eq_getElem (by simpa using v.isLt)]
    simp
  simp [columnSum,toRaw,coord,List.map_ofFn,Function.comp_def,h]

theorem columns_public {n : ℕ} (C : Certificate (Fin n)) (r : Fin n) (H : Vector ℕ n) :
    columns r.val 0 (toRaw C) H.toList=
      (List.finRange n).all (fun v => decide (v≠r →
        (List.ofFn fun i => C.count i*C.row i v).sum=H[v])) := by
  apply Bool.eq_iff_iff.mpr
  rw [columns_true_iff]
  simp only [List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq,Nat.zero_add]
  constructor
  · intro h v hne
    have hv : v.val≠r.val := by intro he; exact hne (Fin.ext he)
    have out := h v.val (by simpa using v.isLt) hv
    rw [columnSum_toRaw C v] at out
    simpa [List.getElem?_eq_getElem (by simpa using v.isLt : v.val<H.toList.length)] using out
  · intro h i hi hne
    let v : Fin n := ⟨i,by simpa using hi⟩
    have hv : v≠r := by intro he; apply hne; exact congrArg Fin.val he
    have out := h v hv
    rw [← columnSum_toRaw C v] at out
    simpa [v,List.getElem?_eq_getElem hi] using out

end UAVProof.A4ColumnCheck
