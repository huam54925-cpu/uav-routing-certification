import LeanCompletion.UAV.TreeBudgetStandardOutputRuns
import LeanCompletion.UAV.TreeBudgetSparseNPBridge

namespace UAVProof.TreeBudgetStandardOutputTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetTransitionSpace TreeBudgetSparseNPBridge
variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]

def initial (input : K) (main : Λ) (s : Bits) : Configuration K Λ :=
  ⟨some main,(none,true),fun k => if k=input then s else []⟩

theorem initial_bound (input : K) (main : Λ) (s : Bits) :
    Bounded (initial input main s).stk s.length := by
  intro k; by_cases hk : k=input <;> simp [initial,hk]

theorem initial_embed (ks : List K) (input : K) (main : Λ) (M : Λ → Statement K Λ) (s : Bits) :
    embed wiring Label.body Label.write (fun _ => []) (initial input main s)=
      initList (machine ks input main M) s := by
  unfold embed initial initList machine
  congr 1
  funext k; cases k with
  | inl k => by_cases hk : k=input <;> simp [bank,wiring,hk]
  | inr u => simp [bank,wiring]

theorem return_embed (ks : List K) (out : Configuration K Λ) (h : out.l=none) :
    embed wiring Label.body Label.write (fun _ => []) out=
      (⟨some .write,out.var,store out.stk []⟩ : Configuration (K⊕Unit) (Label Λ ks.length)) := by
  simp only [embed,h,Option.elim_none]
  congr 1
  funext k; cases k <;> rfl

/-- A flag-returning polynomial machine can be normalized without any
acceptance assumption. All residue is charged via its transition-space bound. -/
def normalize_run (ks : List K) (cover : ∀ k, k∈ks)
    (input : K) (main : Λ) (M : Λ → Statement K Λ)
    (B : ℕ) (hB : ∀ l, pushes (M l)≤B)
    (s : Bits) (out : Configuration K Λ) (T : ℕ)
    (run : EvalsToInTime (TM2.step M) (initial input main s) (some out) T)
    (halted : out.l=none) :
    TM2OutputsInTime (machine ks input main M) s (some [out.var.2])
      (T+ks.length*(s.length+T*B+1)+2) := by
  have body := call_run wiring Label.body Label.write (fun _ => []) M (program ks M)
    (fun _ => rfl) run
  rw [initial_embed,return_embed ks out halted] at body
  have space := run_bound M B hB _ out T s.length run (initial_bound input main s)
  have tail := return_run ks M input main cover out.var out.stk (s.length+T*B) space
  have combined := EvalsToInTime.trans (TM2.step (program ks M)) _ _ _ _ _ body tail
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using combined

def pushBound (M : Λ → Statement K Λ) : ℕ := Finset.univ.sup (fun l => pushes (M l))

theorem pushes_le (M : Λ → Statement K Λ) (l : Λ) : pushes (M l)≤pushBound M :=
  by exact Finset.le_sup (f := fun j => pushes (M j)) (Finset.mem_univ l)

noncomputable def normalizedPolynomial (ks : List K) (M : Λ → Statement K Λ)
    (p : Polynomial ℕ) : Polynomial ℕ :=
  p+Polynomial.C ks.length*(Polynomial.X+p*Polynomial.C (pushBound M)+1)+2

theorem normalizedPolynomial_eval (ks : List K) (M : Λ → Statement K Λ)
    (p : Polynomial ℕ) (n : ℕ) :
    (normalizedPolynomial ks M p).eval n=p.eval n+ks.length*(n+p.eval n*pushBound M+1)+2 := by
  simp [normalizedPolynomial]

/-- Construct the standard verifier object once the semantic executor has
been proved on every raw pair, including rejection. -/
noncomputable def standardVerifier (ks : List K) (cover : ∀ k, k∈ks)
    (input : K) (main : Λ) (M : Λ → Statement K Λ) (V : Bits → Bits → Bool)
    (p : Polynomial ℕ)
    (executes : ∀ x y, ∃ out : Configuration K Λ,
      Nonempty (EvalsToInTime (TM2.step M) (initial input main (pairWire (x,y)))
        (some out) (p.eval (pairWire (x,y)).length)) ∧ out.l=none ∧ out.var.2=V x y) :
    StandardVerifier V where
  machine := {
    tm := machine ks input main M
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := normalizedPolynomial ks M p
    outputsFun := by
      rintro ⟨x,y⟩
      change TM2OutputsInTime (machine ks input main M) (List.map id (pairWire (x,y)))
        (some (List.map id [V x y])) ((normalizedPolynomial ks M p).eval (pairWire (x,y)).length)
      simp only [List.map_id_fun]
      let out := Classical.choose (executes x y)
      have spec := Classical.choose_spec (executes x y)
      let run := Classical.choice spec.1
      have halted := spec.2.1
      have hb := spec.2.2
      have h := normalize_run ks cover input main M (pushBound M) (pushes_le M)
        (pairWire (x,y)) out _ run halted
      rw [hb] at h
      simpa only [normalizedPolynomial_eval] using h
  }
  finiteAlphabet k := by change Finite Bool; infer_instance

end UAVProof.TreeBudgetStandardOutputTM2
