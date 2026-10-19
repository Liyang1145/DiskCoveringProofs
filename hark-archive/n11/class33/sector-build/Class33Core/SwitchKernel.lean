/- Class33 core-Lean transcription of the WIP switch direct leaf (pre-validation, NOT credit):
   SharedMomentFactorIntervalCertificate.switchDirectUpperQ, RatInterval.{ofRat,add,mul},
   RationalTrigCellBounds.{sinCell,squareCell,midpoint,halfWidth}, IntervalsHighLag.sin{Lo,Hi}NLag,
   IntervalsHigh.sinTQ (Finset.range sum as List.range fold), CompactQuadraticMomentMaximum.maximumQ.
   `|q|` as `if q < 0 then -q else q`; core Rat min/max. -/
namespace Class33Core.SwitchKernel
structure RI where
  lo : Rat
  hi : Rat
def qabs (q : Rat) : Rat := if q < 0 then -q else q
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n
def ofRat (q : Rat) : RI := ⟨q, q⟩
def add (A B : RI) : RI := ⟨A.lo + B.lo, A.hi + B.hi⟩
def mul (A B : RI) : RI :=
  ⟨min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)),
   max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))⟩
def sinTQ (m : Nat) (q : Rat) : Rat :=
  (List.range m).foldl (fun s k => s + (-1 : Rat) ^ k * q ^ (2 * k + 1) / ((fact (2 * k + 1) : Nat) : Rat)) 0
def sinLoNLag (q : Rat) : Rat := sinTQ 14 q - qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def sinHiNLag (q : Rat) : Rat := sinTQ 14 q + qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def midpoint (I : RI) : Rat := (I.lo + I.hi) / 2
def halfWidth (I : RI) : Rat := (I.hi - I.lo) / 2
def sinCell (I : RI) : RI :=
  ⟨max (-1) (sinLoNLag (midpoint I) - halfWidth I), min 1 (sinHiNLag (midpoint I) + halfWidth I)⟩
def squareCell (I : RI) : RI :=
  if 0 ≤ I.lo then ⟨I.lo^2, I.hi^2⟩
  else if I.hi ≤ 0 then ⟨I.hi^2, I.lo^2⟩
  else ⟨0, max (I.lo^2) (I.hi^2)⟩
def maximumQ (A B : Rat) : Rat :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B^2/(4*A) else max 0 (A+B)
def switchQuadraticCell (q d2 : Rat) (B : RI) : RI :=
  add (add (mul (ofRat ((19/50 : Rat)^2/2)) (sinCell (mul (ofRat 2) B))) (mul (ofRat q) (squareCell (sinCell B)))) (ofRat d2)
def switchLinearCell (b d1 : Rat) (B : RI) : RI := add (mul (ofRat b) (sinCell B)) (ofRat d1)
def switchDirectUpperQ (p q b d2 d1 : Rat) (B : RI) : Rat :=
  (mul (ofRat p) B).hi + maximumQ (switchQuadraticCell q d2 B).hi (switchLinearCell b d1 B).hi
structure Coeff where
  p : Rat
  q : Rat
  b : Rat
  d2 : Rat
  d1 : Rat
def leafOK (c : Coeff) (M lo hi : Rat) : Bool := decide (switchDirectUpperQ c.p c.q c.b c.d2 c.d1 ⟨lo, hi⟩ ≤ M)
def allLeavesOK (c : Coeff) (M : Rat) (l : List (Rat × Rat)) : Bool := l.all (fun x => leafOK c M x.1 x.2)
/-- consecutive leaves share endpoints (chunked tiling; chunk endpoints checked separately). -/
def chainB : List (Rat × Rat) → Bool
  | [] => true
  | [_] => true
  | x :: y :: r => decide (x.2 = y.1) && decide (x.1 < x.2) && chainB (y :: r)
end Class33Core.SwitchKernel
