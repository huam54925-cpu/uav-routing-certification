import LeanCompletion.UAV.TreeBudgetRegisterRuns
import LeanCompletion.UAV.TreeBudgetFeeScalingSpec

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000

inductive R
  | nums | dens | bnum | bden | pre | suf | a | b
  | prefixRev | numRev | denRev | signRev | sign | fees | budget | scratch
  deriving DecidableEq, Fintype

abbrev K := A4PairedParser.K ⊕ (Fin 6 ⊕ R)
abbrev old (k : A4PairedParser.K) : K := .inl k
abbrev mr (i : Fin 6) : K := .inr (.inl i)
abbrev wr (r : R) : K := .inr (.inr r)

inductive PC
  | copyNums | copyDens | copyBNum | copyBDen | seed
  | fTest | fSign | fA | fB | fSaveA | fSaveB | fSaveP | fLoadP | fLoadB
  | fMul | fClearP | fKeepP | fClearProduct | fClearA | fClearB
  | bSign | bA | bLoadA | bLoadP | bMul | bEmit | bClearA | bClearP | bU
  | rTest | rP | rB | rA | rSign | rLoadP | rLoadU | rFactor
  | rLoadA | rLoadFactor | rClearFactor | rFee | rEmit
  | rLoadB | rLoadUAgain | rSuffix | rClearU | rKeepU | rClearProduct
  | rClearA | rClearB | rClearP | cleanup | done
  deriving DecidableEq, Fintype

def mw : Wiring (Fin 6) K :=
  ⟨mr,(fun k => match k with | .inr (.inl i) => some i | _ => none),
    by intro i; rfl, by intro k i h; rcases k with k | j | r <;> simpa using h⟩

abbrev inputField (f : A4FeeTailMachine.FeeField) : K :=
  old (A4PairedParser.ik (.inr (.result f)))

local macro "port(" s:term "," d:term ")" : term =>
  `((⟨$s,wr .scratch,$d,by decide,by decide,by decide⟩ : Ports K))

def instr : PC → TreeBudgetRegisterTM2.Instr K PC
  | .copyNums => .copy port(inputField .nums,wr .nums) false .copyDens
  | .copyDens => .copy port(inputField .dens,wr .dens) false .copyBNum
  | .copyBNum => .copy port(inputField .bnum,wr .bnum) false .copyBDen
  | .copyBDen => .copy port(inputField .bden,wr .bden) false .seed
  | .seed => .push (wr .pre) true .fTest
  | .fTest => .test (wr .dens) .bSign .fSign
  | .fSign => .bit (wr .nums) (wr .signRev) .fA
  | .fA => .read port(wr .nums,wr .a) .fB
  | .fB => .read port(wr .dens,wr .b) .fSaveA
  | .fSaveA => .copy port(wr .a,wr .numRev) true .fSaveB
  | .fSaveB => .copy port(wr .b,wr .denRev) true .fSaveP
  | .fSaveP => .copy port(wr .pre,wr .prefixRev) true .fLoadP
  | .fLoadP => .copy port(wr .pre,mr 0) false .fLoadB
  | .fLoadB => .copy port(wr .b,mr 1) false .fMul
  | .fMul => .mul mw .fClearP
  | .fClearP => .clear port(wr .pre,mr 5) .fKeepP
  | .fKeepP => .copy port(mr 2,wr .pre) false .fClearProduct
  | .fClearProduct => .clear port(mr 2,mr 5) .fClearA
  | .fClearA => .clear port(wr .a,mr 5) .fClearB
  | .fClearB => .clear port(wr .b,mr 5) .fTest
  | .bSign => .bit (wr .bnum) (wr .sign) .bA
  | .bA => .read port(wr .bnum,wr .a) .bLoadA
  | .bLoadA => .copy port(wr .a,mr 0) false .bLoadP
  | .bLoadP => .copy port(wr .pre,mr 1) false .bMul
  | .bMul => .mul mw .bEmit
  | .bEmit => .emit port(mr 2,wr .budget) (wr .sign) .bClearA
  | .bClearA => .clear port(wr .a,mr 5) .bClearP
  | .bClearP => .clear port(wr .pre,mr 5) .bU
  | .bU => .read port(wr .bden,wr .suf) .rTest
  | .rTest => .test (wr .prefixRev) .cleanup .rP
  | .rP => .read port(wr .prefixRev,wr .pre) .rB
  | .rB => .read port(wr .denRev,wr .b) .rA
  | .rA => .read port(wr .numRev,wr .a) .rSign
  | .rSign => .bit (wr .signRev) (wr .sign) .rLoadP
  | .rLoadP => .copy port(wr .pre,mr 0) false .rLoadU
  | .rLoadU => .copy port(wr .suf,mr 1) false .rFactor
  | .rFactor => .mul mw .rLoadA
  | .rLoadA => .copy port(wr .a,mr 0) false .rLoadFactor
  | .rLoadFactor => .copy port(mr 2,mr 1) false .rClearFactor
  | .rClearFactor => .clear port(mr 2,mr 5) .rFee
  | .rFee => .mul mw .rEmit
  | .rEmit => .emit port(mr 2,wr .fees) (wr .sign) .rLoadB
  | .rLoadB => .copy port(wr .b,mr 0) false .rLoadUAgain
  | .rLoadUAgain => .copy port(wr .suf,mr 1) false .rSuffix
  | .rSuffix => .mul mw .rClearU
  | .rClearU => .clear port(wr .suf,mr 5) .rKeepU
  | .rKeepU => .copy port(mr 2,wr .suf) false .rClearProduct
  | .rClearProduct => .clear port(mr 2,mr 5) .rClearA
  | .rClearA => .clear port(wr .a,mr 5) .rClearB
  | .rClearB => .clear port(wr .b,mr 5) .rClearP
  | .rClearP => .clear port(wr .pre,mr 5) .rTest
  | .cleanup => .clear port(wr .suf,mr 5) .done
  | .done => .halt

structure Data where
  saved : A4PairedParser.K → Bits
  work : R → Bits := fun _ => []
  mult : Fin 6 → Bits := fun _ => []

def store (d : Data) : K → Bits
  | .inl k => d.saved k | .inr (.inl k) => d.mult k | .inr (.inr k) => d.work k

def put (d : Data) (k : K) (v : Bits) : Data := match k with
  | .inl k => {d with saved:=Function.update d.saved k v}
  | .inr (.inl k) => {d with mult:=Function.update d.mult k v}
  | .inr (.inr k) => {d with work:=Function.update d.work k v}

theorem store_put (d : Data) (k : K) (v : Bits) : store (put d k v)=Function.update (store d) k v := by
  funext j
  rcases k with k | k | k <;> rcases j with j | j | j <;>
    simp [store,put,Function.update_apply]

abbrev Cfg := TreeBudgetRegisterTM2.Cfg K PC
def cfg (l : PC) (d : Data) : Cfg := TreeBudgetRegisterTM2.cfg l (store d)
abbrev Run := TreeBudgetRegisterTM2.Run instr
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) :=
  TreeBudgetRegisterTM2.seq instr h g

def forwardState (saved : A4PairedParser.K → Bits) (bn bd : Bits)
    (es : List Row) (p : Bits) (hist : List Item) : Data :=
  {saved:=saved, work:=fun r => match r with
    | .nums => (es.map Prod.fst).flatMap encodeInt
    | .dens => (es.map Prod.snd).flatMap encodeNat
    | .bnum => bn | .bden => bd | .pre => p
    | .prefixRev => hist.flatMap (fun e => word e.pre)
    | .numRev => hist.flatMap (fun e => word e.a.natAbs.bits)
    | .denRev => hist.flatMap (fun e => word e.b.bits)
    | .signRev => hist.map (fun e => decide (e.a<0))
    | _ => []}

def backwardState (saved : A4PairedParser.K → Bits) (budget : Bits)
    (hist : List Item) (u : Bits) (out : Bits) : Data :=
  {saved:=saved, work:=fun r => match r with
    | .budget => budget | .fees => out | .suf => u
    | .prefixRev => hist.flatMap (fun e => word e.pre)
    | .numRev => hist.flatMap (fun e => word e.a.natAbs.bits)
    | .denRev => hist.flatMap (fun e => word e.b.bits)
    | .signRev => hist.map (fun e => decide (e.a<0))
    | _ => []}

end UAVProof.A4FeeScaling
