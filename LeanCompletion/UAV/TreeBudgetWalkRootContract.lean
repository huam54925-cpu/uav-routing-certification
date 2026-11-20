import LeanCompletion.UAV.TreeBudgetWalkRootTM2

/-! Exact successful return layout for repeated calls. Failure may leave
partially consumed words; the outer caller rejects without reusing them. -/
namespace UAVProof.TreeBudgetWalkRootTM2
open TreeBudgetBinaryCodec TreeBudgetParentArray TreeBudgetTM2Call

theorem walkEnd_success (ticks q out ctx : Bits)
    (h : TreeBudgetParentWalkTM2.walkQuery ticks q = some out) :
    TreeBudgetParentWalkTM2.walkEnd ticks q ctx = TreeBudgetParentWalkTM2.done out ctx := by
  induction ticks generalizing q with
  | nil => cases Option.some.inj h; rfl
  | cons b ticks ih =>
    cases hp : TreeBudgetParentWalkTM2.parts q with
    | none => simp [TreeBudgetParentWalkTM2.walkQuery,hp] at h
    | some p =>
      obtain ⟨xs,a,t⟩ := p
      simp only [TreeBudgetParentWalkTM2.walkQuery,hp,Option.bind_some] at h
      simpa [TreeBudgetParentWalkTM2.walkEnd,hp] using ih _ h

theorem typed_end {n : ℕ} (P : ParentArray n) (ticks ctx : Bits) (v : Fin n) :
    TreeBudgetParentWalkTM2.walkEnd ticks (TreeBudgetParentWalkTM2.query P v) ctx =
      TreeBudgetParentWalkTM2.done (TreeBudgetParentWalkTM2.query P (follow P ticks.length v)) ctx :=
  walkEnd_success _ _ _ _ (typed_walk P ticks v)

theorem compare_same (base : K → Bits) (r tail : Bits) :
    finishCheck base r (r ++ tail) = {checkCfg base tail [] with l := none,var := (none,true)} := by
  induction r with
  | nil => rfl
  | cons b r ih => simpa [finishCheck] using ih

theorem finishCheck_terminal (base : K → Bits) (r q : Bits) :
    (finishCheck base r q).l = none := by
  induction r generalizing q with
  | nil => rfl
  | cons b r ih =>
    cases q with
    | nil => rfl
    | cons d q => simp only [finishCheck]; split <;> first | rfl | exact ih _

theorem finish_terminal (ticks q root ctx : Bits) : (finish ticks q root ctx).l = none := by
  dsimp only [finish]
  split
  · exact finishCheck_terminal ..
  · rfl

theorem successful_layout {n : ℕ} (P : ParentArray n) (ticks ctx : Bits) (v : Fin n)
    (h : (finish ticks (TreeBudgetParentWalkTM2.query P v) (encodeNat P.root.val) ctx).var.2 = true) :
    finish ticks (TreeBudgetParentWalkTM2.query P v) (encodeNat P.root.val) ctx =
      {start [] (TreeBudgetParentWalkTM2.body P) [] ctx with l := none} := by
  have he : follow P ticks.length v = P.root := by
    simpa [endpoint_is_root,TreeBudgetCostedInput.followCost_value] using h
  simp only [finish,typed_end,TreeBudgetParentWalkTM2.done,he]
  change finishCheck _ (encodeNat P.root.val)
    (encodeNat P.root.val ++ TreeBudgetParentWalkTM2.body P) = _
  rw [compare_same]
  simp only [checkCfg,start,called,embed,TreeBudgetParentWalkTM2.cfg]
  congr 1
  funext k
  cases k with
  | inr u => cases u; rfl
  | inl k =>
    cases k with
    | inr u => cases u; rfl
    | inl k =>
      cases k with
      | inr b => cases b <;> rfl
      | inl i => fin_cases i <;> rfl

def scheduleSpec {n : ℕ} (P : ParentArray n) : Bool :=
  decide (parent P P.root = P.root) &&
    (List.finRange n).all (fun v => decide (follow P n v = P.root))

theorem scheduleSpec_correct {n : ℕ} (P : ParentArray n) :
    scheduleSpec P = (TreeBudgetCostedInput.validateCost P).value := by
  rw [TreeBudgetCostedInput.validateCost_value]
  rfl

end UAVProof.TreeBudgetWalkRootTM2
