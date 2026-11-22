import LeanCompletion.UAV.TreeBudgetRowCheckRuns

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2

set_option maxHeartbeats 8000000
set_option maxRecDepth 50000

theorem compare_saved_val (l₁ l₂ l₃ yes no : PC) (i j : Fin 24)
    (c₁ : instructions l₁=.copy (operandPort i 31 (by decide)) false l₂)
    (c₂ : instructions l₂=.copy (operandPort j 32 (by decide)) false l₃)
    (c₃ : instructions l₃=.le cw yes no)
    (s : K → Bits) (hs : s (reg 24)=[]) (h₁ : s (reg 31)=[]) (h₂ : s (reg 32)=[])
    (h₃ : s (reg 33)=[]) (h₄ : s (reg 34)=[]) :
    (compare_saved l₁ l₂ l₃ yes no i j c₁ c₂ c₃ s hs h₁ h₂ h₃ h₄).val=
      3*((s (source i)).length+(s (source j)).length)+9 := by
  change (2*(s (source i)).length+3)+(2*(s (source j)).length+3)+
    ((s (source i)).length+(s (source j)).length+3)=_
  omega

theorem weighted_saved_val (l₁ l₂ l₃ next : PC) (i j : Fin 24) (a : Fin 3)
    (c₁ : instructions l₁=.copy (operandPort i 26 (by decide)) false l₂)
    (c₂ : instructions l₂=.copy (operandPort j 27 (by decide)) false l₃)
    (c₃ : instructions l₃=.weighted (mw a) next)
    (s : K → Bits) (hs : s (reg 24)=[]) (h₁ : s (reg 26)=[]) (h₂ : s (reg 27)=[])
    (h₃ : s (reg 28)=[]) (h₄ : s (reg 29)=[]) :
    (weighted_saved l₁ l₂ l₃ next i j a c₁ c₂ c₃ s hs h₁ h₂ h₃ h₄).val=
      2*(s (source i)).length+2*(s (source j)).length+
        16*((s (source i)).length+(s (source j)).length+(s (acc a)).length+1)^2+9 := by
  change (2*(s (source i)).length+3)+(2*(s (source j)).length+3)+
    (16*((s (source i)).length+(s (source j)).length+(s (acc a)).length+1)^2+3)=_
  omega

theorem prepare_run_val (P H u ap an root tp tn ctx suffix : Bits) :
    (prepare_run P H u ap an root tp tn ctx suffix).val=
      2*(P.length+H.length+u.length+ap.length+an.length+tp.length+tn.length)+21 := by
  dsimp [prepare_run]
  omega

end UAVProof.A4RowCheck
