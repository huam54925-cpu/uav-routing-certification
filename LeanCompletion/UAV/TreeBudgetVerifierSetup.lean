import LeanCompletion.UAV.TreeBudgetVerifierTM2

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev pSource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ik A4FeeTailMachine.parents)
abbrev hSource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ik (.inl TreeBudgetRootFlowTM2.demands))
abbrev rSource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ik (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot)))
abbrev mSource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ik (.inl (.inl (.inr (.inr 0)))))
abbrev bodySource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ck A4CertRecords.savedBody)
abbrev marksSource : A4FeeScaling.K := A4FeeScaling.old (A4PairedParser.ck A4CertRecords.savedCount)

def rowInputs (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) : A4RowsCheck.Data :=
  { rowSaved := A4RowCheck.store (s pSource) (s hSource) []
      (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A)
      (s rSource) AT.toNat.bits (-AT).toNat.bits [] []
    body := s bodySource
    markers := s marksSource
    routes := s mSource }

def columnInputs (s : A4FeeScaling.K → Bits) : A4ColumnCheck.Input :=
  ⟨s bodySource,[],s rSource,s hSource,[]⟩

def prepPC (j : ℕ) : PC := match j with
  | 0 => .parents | 1 => .demands | 2 => .root | 3 => .routes
  | 4 => .body | 5 => .markers | 6 => .positive | 7 => .negative
  | 8 => .budgetPositive | 9 => .budgetNegative | 10 => .columnBody
  | 11 => .columnRoot | 12 => .columnTargets | _ => .done

def prepRows (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : ℕ) : A4RowsCheck.Data :=
  { rowSaved := A4RowCheck.store
      (if 1≤j then s pSource else []) (if 2≤j then s hSource else []) []
      (if 7≤j then TreeBudgetSignedTableTM2.positive A else [])
      (if 8≤j then TreeBudgetSignedTableTM2.negative A else [])
      (if 3≤j then s rSource else [])
      (if 9≤j then AT.toNat.bits else []) (if 10≤j then (-AT).toNat.bits else []) [] []
    body := if 5≤j then s bodySource else []
    markers := if 6≤j then s marksSource else []
    routes := if 4≤j then s mSource else [] }

def prepColumns (s : A4FeeScaling.K → Bits) (j : ℕ) : A4ColumnCheck.Input :=
  ⟨if 11≤j then s bodySource else [],[],if 12≤j then s rSource else [],
    if 13≤j then s hSource else [],[]⟩

def prepBank (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : ℕ) : K → Bits :=
  store s (A4RowsCheck.store (prepRows s A AT j))
    (A4ColumnCheck.start (prepColumns s j)).stk
    (TreeBudgetSignedTableTM2.stopped (A.flatMap encodeInt)
      (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A) []).stk
    (TreeBudgetSignedTableTM2.store (encodeInt AT) [] [] []
      (if j<9 then encodeNat AT.toNat else [])
      (if j<10 then encodeNat (-AT).toNat else []) [])

def ready (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) : Cfg :=
  ⟨some (.rows A4RowsCheck.machine.main),(none,true),prepBank s A AT 13⟩

theorem ready_rows (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) :
    (fun k => prepBank s A AT 13 (rk k))=A4RowsCheck.store (rowInputs s A AT) := rfl

theorem ready_columns (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) :
    (fun k => prepBank s A AT 13 (ck k))=(A4ColumnCheck.start (columnInputs s)).stk := rfl

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,scratch,$d,by decide,by decide,by decide⟩ : Ports K))

def prepPort (j : Fin 13) : Ports K := match j.val with
  | 0 => port(inst A4FeeTailMachine.parents,rowReg 0)
  | 1 => port(inst (.inl TreeBudgetRootFlowTM2.demands),rowReg 1)
  | 2 => port(inst (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot)),rowReg 5)
  | 3 => port(inst (.inl (.inl (.inr (.inr 0)))),rk (A4RowsCheck.ax .routes))
  | 4 => port(cert A4CertRecords.savedBody,rk (A4RowsCheck.ax .body))
  | 5 => port(cert A4CertRecords.savedCount,rk (A4RowsCheck.ax .markers))
  | 6 => port(fk 4,rowReg 3)
  | 7 => port(fk 5,rowReg 4)
  | 8 => port(bk 4,rowReg 6)
  | 9 => port(bk 5,rowReg 7)
  | 10 => port(cert A4CertRecords.savedBody,ck (A4ColumnCheck.wr .body))
  | 11 => port(inst (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot)),ck (A4ColumnCheck.wr .root))
  | _ => port(inst (.inl TreeBudgetRootFlowTM2.demands),ck (A4ColumnCheck.wr .targets))

def valueAt (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : Fin 13) : Bits :=
  match j.val with
  | 0 => s pSource | 1 => s hSource | 2 => s rSource | 3 => s mSource
  | 4 => s bodySource | 5 => s marksSource
  | 6 => TreeBudgetSignedTableTM2.positive A | 7 => TreeBudgetSignedTableTM2.negative A
  | 8 => AT.toNat.bits | 9 => (-AT).toNat.bits
  | 10 => s bodySource | 11 => s rSource | _ => s hSource

theorem prep_port_scratch (j : Fin 13) : (prepPort j).scratch=scratch := by fin_cases j <;> rfl

theorem prep_source (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : Fin 13) :
    prepBank s A AT j.val (prepPort j).src=
      (if j.val=8 ∨ j.val=9 then word (valueAt s A AT j) else valueAt s A AT j) := by
  fin_cases j <;> rfl

theorem prep_dest (s : A4FeeScaling.K → Bits) (A : List ℤ) (AT : ℤ) (j : Fin 13) :
    prepBank s A AT j.val (prepPort j).dst=[] := by fin_cases j <;> rfl

end UAVProof.A4Verifier
