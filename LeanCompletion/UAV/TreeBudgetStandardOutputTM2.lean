import LeanCompletion.UAV.TreeBudgetTM2CallOn

/-! A standard-output wrapper. It records the Boolean return value, clears a
fixed covering list of caller stacks, resets the finite state and halts. -/
namespace UAVProof.TreeBudgetStandardOutputTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing
variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]

inductive Label (Λ : Type) (n : ℕ)
  | body (l : Λ)
  | write
  | clear (i : Fin (n+1))
  deriving DecidableEq, Fintype

def wiring : Wiring K (K ⊕ Unit) :=
  ⟨Sum.inl,(fun k => match k with | .inl k => some k | _ => none),
    by intro k; rfl,by intro k i h; cases k <;> simpa using h⟩

def jump {n : ℕ} (l : Label Λ n) : Statement (K ⊕ Unit) (Label Λ n) :=
  .load (fun _ => (none,true)) (.goto (fun _ => l))

def program (ks : List K) (M : Λ → Statement K Λ) :
    Label Λ ks.length → Statement (K ⊕ Unit) (Label Λ ks.length)
  | .body l => compile wiring .body .write (M l)
  | .write => .push (.inr ()) Prod.snd (jump (.clear 0))
  | .clear i => if hi : i.val<ks.length then
      .pop (.inl ks[i.val]) (fun _ b => (b,true))
        (.branch (fun s => s.1.isNone)
          (jump (.clear ⟨i.val+1,by omega⟩)) (jump (.clear i)))
      else .load (fun _ => (none,true)) .halt

def machine (ks : List K) (input : K) (main : Λ) (M : Λ → Statement K Λ) : FinTM2 where
  K := K ⊕ Unit
  k₀ := .inl input
  k₁ := .inr ()
  Γ _ := Bool
  Λ := Label Λ ks.length
  main := .body main
  σ := State
  initialState := (none,true)
  m := program ks M

def store (s : K → Bits) (out : Bits) : K ⊕ Unit → Bits
  | .inl k => s k
  | .inr _ => out

def cfg (ks : List K) (i : Fin (ks.length+1)) (s : K → Bits) (out : Bits) :
    Configuration (K ⊕ Unit) (Label Λ ks.length) :=
  ⟨some (.clear i),(none,true),store s out⟩

def cleaned (ks : List K) (s : K → Bits) : K → Bits :=
  fun k => if k∈ks then [] else s k

theorem cleaned_nil (s : K → Bits) : cleaned [] s=s := by funext k; simp [cleaned]
theorem cleaned_cons (k : K) (ks : List K) (s : K → Bits) :
    cleaned (k::ks) s=cleaned ks (Function.update s k []) := by
  funext j
  by_cases hj : j=k <;> by_cases hk : j∈ks <;> simp_all [cleaned,Function.update_apply]

theorem store_update (s : K → Bits) (out v : Bits) (k : K) :
    Function.update (store s out) (.inl k) v=store (Function.update s k v) out := by
  funext j; cases j <;> simp [store,Function.update_apply]

end UAVProof.TreeBudgetStandardOutputTM2
