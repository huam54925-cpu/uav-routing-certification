import LeanCompletion.UAV.TreeBudgetRootFlowScanLoop

namespace UAVProof.TreeBudgetRootFlowScanTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open TreeBudgetRootFlowSpec

/-- Equality of numeric values, with two separately prepared destructive comparisons. -/
def exit_run (d : Data) (i : ℕ) (u : Bits) :
    Run (cfg (entry .finalA) (work d i [] [] u))
      (stop (work d i [] [] u) (decide (value u=value d.m)))
      (6*(u.length+d.m.length)+12) := by
  let d₀ := work d i [] [] u
  let d₁ := copied .finalA d₀
  let d₂ := copied .finalM d₁
  have ca := copy_job .finalA d₀ rfl
  have cm := copy_job .finalM d₁ rfl
  have cl := compare_job .le d₂
  have ce : comparison .le d₂=decide (value u≤value d.m) := by
    simpa [d₂,d₁,d₀,copied,source,dest,replace,work] using comparison_le .le rfl d₂
  simp only [compared,ce] at cl
  by_cases he : value u≤value d.m
  · have first : Run (cfg (entry .finalA) d₀) (cfg (entry .reverseM) d₀)
        (3*(u.length+d.m.length)+6) := by
      exact weaken (by simpa [compared,ce,he,d₂,d₁,d₀,copied,source,dest,replace,work] using seq (seq ca cm) cl) (by omega)
    let d₃ := copied .reverseM d₀
    let d₄ := copied .reverseA d₃
    have cm' := copy_job .reverseM d₀ rfl
    have ca' := copy_job .reverseA d₃ rfl
    have cg := compare_job .ge d₄
    have ce' : comparison .ge d₄=decide (value u=value d.m) := by
      rw [comparison_le _ rfl]
      simp only [d₄,d₃,d₀,copied,source,dest,replace,work,List.append_nil]
      apply Bool.decide_congr
      omega
    simp only [compared,ce'] at cg
    exact weaken (by simpa [compared,ce',d₄,d₃,d₀,copied,source,dest,replace,work] using seq (seq (seq first cm') ca') cg) (by omega)
  · have hn : value u≠value d.m := by omega
    exact weaken (by simpa [compared,ce,he,hn,d₂,d₁,d₀,copied,source,dest,replace,work] using seq (seq ca cm) cl) (by omega)

/-- Total core on arbitrary canonical tables, including length mismatches.
S bounds occupied fields, not their natural-number values. -/
theorem scan_polynomial (ps hs : List ℕ) (r m S : ℕ)
    (bp : (ps.flatMap encodeNat).length≤S) (bh : (hs.flatMap encodeNat).length≤S)
    (br : r.bits.length≤S) (bm : m.bits.length≤S) (bn : ps.length≤S) :
    ∃ out, Nonempty (Run (start ps hs r m) out (256*(S+1)^2)) ∧ out.l=none ∧
      out.var.2=(decide (hs.length=ps.length) && decide (rootSum r 0 ps hs=m)) ∧
      Kept (initial ps hs r m) out := by
  let d := initial ps hs r m
  have pre := setup_run ps hs r m
  have loop := scan_run d r S 0 ps hs [] rfl br (by simpa only [Nat.zero_add] using bn) bp
    (by simpa only [List.length_nil,Nat.zero_add] using bh)
  have bound : 128*(S+1)*(ps.length+1)≤128*(S+1)^2 := by nlinarith only [bn]
  by_cases he : ps.length=hs.length
  · rw [scanEnd_equal d r 0 ps hs [] he] at loop
    have final := exit_run d (0+ps.length) (accumulated r 0 ps hs [])
    have bu : (accumulated r 0 ps hs []).length≤S := by
      have h := accumulated_length r 0 ps hs []; simp only [List.length_nil,Nat.zero_add] at h; omega
    refine ⟨_,⟨weaken (seq (seq pre loop) final) ?_⟩,rfl,?_,?_⟩
    · change _≤256*(S+1)^2
      have md : d.m.length≤S := bm
      nlinarith only [bp,bh,bound,bu,md]
    · simp [stop,work,he,accumulated_value,d,initial,value]
    · exact ⟨rfl,rfl,rfl,rfl⟩
  · obtain ⟨hl,hv⟩ := scanEnd_unequal d r 0 ps hs [] he
    refine ⟨_,⟨weaken (seq pre loop) ?_⟩,hl,?_,scanEnd_kept d r 0 ps hs []⟩
    · nlinarith only [bp,bh,bound]
    · simp [hv,Ne.symm he]

end UAVProof.TreeBudgetRootFlowScanTM2
