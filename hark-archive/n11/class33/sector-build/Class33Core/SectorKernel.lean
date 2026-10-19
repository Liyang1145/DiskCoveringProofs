import Class33Core.SwitchKernel
/- Class33 core-Lean transcription of the WIP sector direct leaf (pre-validation, NOT credit):
   MetricSectorRationalCellCertificate.{qRawCell,qCell,BoundsValid,triangleCell,penaltyCell,sectorDirectUpperQ},
   MetricSectorRationalNodes.signedWidthUpperQ, with RI/sinCell/squareCell/sinLoNLag/sinHiNLag from SwitchKernel.
   Plus a pre-order token checker for RationalBoxSubdivision.Certificate (split i t / accept). -/
namespace Class33Core.SectorKernel
open Class33Core.SwitchKernel
def sub (A B : RI) : RI := ⟨A.lo - B.hi, A.hi - B.lo⟩
structure Box where
  a0 : Rat
  a1 : Rat
  u0 : Rat
  u1 : Rat
  v0 : Rat
  v1 : Rat
  deriving DecidableEq
structure Co where
  C : Rat
  mu : Rat
  dL : Rat
  dR : Rat
  bL : Rat
  bR : Rat
structure KB where
  cl : Rat
  ch : Rat
  hl : Rat
  hh : Rat
inductive Tok where
  | S (d : Nat) (t : Rat)
  | L (cl ch hl hh : Rat)
  | P
def qRaw (B : Box) : RI :=
  add (squareCell (sub ⟨B.u0, B.u1⟩ ⟨B.v0, B.v1⟩))
    (mul (mul (ofRat 4) (mul ⟨B.u0, B.u1⟩ ⟨B.v0, B.v1⟩)) (squareCell (sinCell (mul (ofRat (1/2)) ⟨B.a0, B.a1⟩))))
def qLo (B : Box) : Rat := max 0 (qRaw B).lo
def qHi (B : Box) : Rat := min 4 (qRaw B).hi
def validK (B : Box) (K : KB) : Bool :=
  decide (0 ≤ B.a0 ∧ B.a0 ≤ B.a1 ∧ 0 ≤ B.u0 ∧ B.u0 ≤ B.u1 ∧ B.u1 ≤ 1 ∧ 0 ≤ B.v0 ∧ B.v0 ≤ B.v1 ∧ B.v1 ≤ 1 ∧
    0 ≤ K.cl ∧ 0 ≤ K.ch ∧ K.cl ^ 2 ≤ qLo B ∧ qHi B ≤ K.ch ^ 2 ∧ 0 ≤ K.hl ∧ K.hl ≤ 1 ∧ 0 ≤ K.hh ∧ K.hh ≤ 1 ∧
    sinHiNLag K.hl ≤ (19/100 : Rat) * K.cl ∧ (19/100 : Rat) * K.ch ≤ sinLoNLag K.hh)
def pen (c : Rat) (I : RI) : RI := mul (ofRat (-c)) I
def triangleCell (B : Box) : RI :=
  mul (mul (ofRat ((19/50 : Rat)^2/2)) (mul ⟨B.u0, B.u1⟩ ⟨B.v0, B.v1⟩)) (sinCell ⟨B.a0, B.a1⟩)
def signedWidthUpperQ (C : Rat) (K : KB) : Rat := C * (if 0 ≤ C then 2 * K.hh else 2 * K.hl)
def sectorDirectUpperQ (c : Co) (B : Box) (K : KB) : Rat :=
  (triangleCell B).hi + (2 * K.hh - sinLoNLag (2 * K.hh)) / 2 + signedWidthUpperQ c.C K +
    (pen c.mu ⟨B.a0, B.a1⟩).hi + (pen c.dL (squareCell ⟨B.u0, B.u1⟩)).hi + (pen c.dR (squareCell ⟨B.v0, B.v1⟩)).hi +
    (pen c.bL ⟨B.u0, B.u1⟩).hi + (pen c.bR ⟨B.v0, B.v1⟩).hi
def leafOK (c : Co) (M : Rat) (B : Box) (K : KB) : Bool :=
  validK B K && decide (sectorDirectUpperQ c B K ≤ M)
def splitBox (B : Box) (d : Nat) (t : Rat) : Option (Box × Box) :=
  match d with
  | 0 => if B.a0 ≤ t ∧ t ≤ B.a1 then some ({ B with a1 := t }, { B with a0 := t }) else none
  | 1 => if B.u0 ≤ t ∧ t ≤ B.u1 then some ({ B with u1 := t }, { B with u0 := t }) else none
  | 2 => if B.v0 ≤ t ∧ t ≤ B.v1 then some ({ B with v1 := t }, { B with v0 := t }) else none
  | _ => none
/-- pre-order checker; `exp` = boxes of stub nodes `P` (checked by the parts). -/
def chk (c : Co) (M : Rat) : Nat → Box → List Tok → List Box → Option (List Tok × List Box)
  | 0, _, _, _ => none
  | _+1, _, [], _ => none
  | _+1, B, Tok.L cl ch hl hh :: r, e => if leafOK c M B ⟨cl, ch, hl, hh⟩ then some (r, e) else none
  | _+1, B, Tok.P :: r, e => match e with
      | [] => none
      | b :: e' => if B = b then some (r, e') else none
  | n+1, B, Tok.S d t :: r, e =>
      match splitBox B d t with
      | none => none
      | some (BL, BR) =>
        match chk c M n BL r e with
        | none => none
        | some (r', e') => chk c M n BR r' e'
def chkAll (c : Co) (M : Rat) (B : Box) (toks : List Tok) (e : List Box) : Bool :=
  match chk c M (toks.length + 1) B toks e with
  | some ([], []) => true
  | _ => false
end Class33Core.SectorKernel
