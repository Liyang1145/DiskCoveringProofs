/-
Core-Lean (no Mathlib) kernel replay of the exact-rational premises of the team WIP's
`N11Formalization.Paid16CellCertificate.Valid` (wip/lean, n11-wip-0001).

`ValidQ` restates every field of the WIP `Valid` as a Prop over core `Rat`, transcribed from
Paid16CellCertificate.lean, CosineLinePacket.lean, ConvexMinorantCore.lean, DBMMinorantDual.lean,
DBMAngleProvider.lean, FlashCosineLeaf318.lean (Lq LQ Dq DQ), Interval/Trig.lean (piLo piHi),
FlashCosineLeaf284Bridge.lean (iOf jOf T), IntervalsHigh(.Lag).lean (sinTQ cosTQ, Lagrange
remainders), RoundedPaid16.lean (weight numerators / 10^12, mix).
Value-level conventions: `qabs` = Mathlib `|.|`; `∑ f : Fin m` = `List.range m` fold;
`Fin 36` index k ↦ pair (iOf k, jOf k) via the explicit table `pairI`/`pairJ`;
the node's DBM matrix `db` and `terminal` flag are carried as data (bound to
DBMSourceTreeData.lean by the Python transcription check, NOT by this kernel).
This pre-validates the finite premises only; the real-analytic soundness
(`Paid16CellCertificate.common_chart_radius`, Mathlib) is the WIP's, and NOTHING here is paid.
-/
namespace DCPN11Core.EnergyReplay

def qabs (q : Rat) : Rat := if q < 0 then -q else q
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n
def sumRange (m : Nat) (f : Nat → Rat) : Rat := (List.range m).foldl (fun s k => s + f k) 0
def sinTQ (m : Nat) (q : Rat) : Rat :=
  sumRange m (fun k => (-1 : Rat) ^ k * q ^ (2 * k + 1) / ((fact (2 * k + 1) : Nat) : Rat))
def cosTQ (m : Nat) (q : Rat) : Rat :=
  sumRange m (fun k => (-1 : Rat) ^ k * q ^ (2 * k) / ((fact (2 * k) : Nat) : Rat))
def sinLoNLag (q : Rat) : Rat := sinTQ 14 q - qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def sinHiNLag (q : Rat) : Rat := sinTQ 14 q + qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def cosHiNLag (q : Rat) : Rat := cosTQ 14 q + qabs q ^ 28 / ((fact 28 : Nat) : Rat)

def piLo : Rat := 314159265358979323846 / 10 ^ 20
def piHi : Rat := 314159265358979323847 / 10 ^ 20
def Lq : Rat := 2 * (1150475603510479590494077 / 2951479051793528258560000)
def LQ : Rat := 2 * (449404532622434011541355675101 / 1152921504606846976000000000000)
def Dq : Rat := 9 * Lq - 2 * piHi
def DQ : Rat := 9 * LQ - 2 * piLo
def T : Rat := 1899919265599193545242591 / 5000000000000000000000000

def endpointLo (a b x : Rat) : Rat := x * (if 0 ≤ x then a else b)
def piLower (x : Rat) : Rat := endpointLo piLo piHi x
def piUpper (x : Rat) : Rat := -piLower (-x)
def IncArc (a b : Rat) (m : Int) : Prop :=
  piUpper (2*(m : Rat)-1/2) ≤ a ∧ b ≤ piLower (2*(m : Rat)+1/2)
def DecArc (a b : Rat) (m : Int) : Prop :=
  piUpper (2*(m : Rat)+1/2) ≤ a ∧ b ≤ piLower (2*(m : Rat)+3/2)
instance (a b : Rat) (m : Int) : Decidable (IncArc a b m) := by unfold IncArc; infer_instance
instance (a b : Rat) (m : Int) : Decidable (DecArc a b m) := by unfold DecArc; infer_instance

inductive Rule
  | tangent | decreasing | left | right
  deriving DecidableEq

structure Line where
  a : Rat
  b : Rat
  s : Rat
  c : Rat
  t : Rat
  e : Rat
  shift : Int
  rule : Rule

def LineValid (p : Line) : Prop :=
  p.a ≤ p.b ∧ match p.rule with
  | .tangent =>
    IncArc p.a p.b p.shift ∧ p.a ≤ p.t ∧ p.t ≤ p.b ∧ 0 ≤ p.e ∧
      p.s-p.e ≤ sinLoNLag p.t ∧ sinHiNLag p.t ≤ p.s+p.e ∧
      p.c ≤ 1-cosHiNLag p.t-p.s*p.t-p.e*(p.b-p.a)
  | .decreasing =>
    DecArc p.a p.b p.shift ∧ p.c ≤ 1-cosHiNLag p.a-p.s*p.a ∧
      p.c ≤ 1-cosHiNLag p.b-p.s*p.b
  | .left =>
    IncArc p.a p.b p.shift ∧ p.s ≤ sinLoNLag p.a ∧ p.c ≤ 1-cosHiNLag p.a-p.s*p.a
  | .right =>
    IncArc p.a p.b p.shift ∧ sinHiNLag p.b ≤ p.s ∧ p.c ≤ 1-cosHiNLag p.b-p.s*p.b
instance (p : Line) : Decidable (LineValid p) := by
  unfold LineValid
  cases p.rule <;> infer_instance

/-- iOf/jOf of FlashCosineLeaf284Bridge, k = 0..35 (lexicographic pairs i<j of Fin 9). -/
def pairI : List Nat := [0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,4,4,4,4,5,5,5,6,6,7]
def pairJ : List Nat := [1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,3,4,5,6,7,8,4,5,6,7,8,5,6,7,8,6,7,8,7,8,8]
def iOf (k : Nat) : Nat := pairI.getD k 0
def jOf (k : Nat) : Nat := pairJ.getD k 0

/-- A node of DBMSourceTree: integer matrix `db` (scale 4096) and terminal flag. -/
structure Node where
  db : List (List Int)
  terminal : Bool
def Node.dbQ (n : Node) (i j : Nat) : Rat := ((n.db.getD i []).getD j 0 : Rat) / 4096
def slo (n : Node) (k : Nat) : Rat := max (-(n.dbQ (jOf k) (iOf k))) 0
def shi (n : Node) (k : Nat) : Rat := n.dbQ (iOf k) (jOf k)

structure Packet where
  nodeID : Nat
  beta : List Rat
  line : List Line
  rowFrom : List Nat
  rowTo : List Nat
  lam : List Rat
  rmin : Rat

def dLine : Line := ⟨0,0,0,0,0,0,0,.tangent⟩
def Packet.L (p : Packet) (k : Nat) : Line := p.line.getD k dLine
def Packet.b (p : Packet) (f : Nat) : Rat := p.beta.getD f 0
def Packet.lm (p : Packet) (a : Nat) : Rat := p.lam.getD a 0
def Packet.rf (p : Packet) (a : Nat) : Nat := p.rowFrom.getD a 0
def Packet.rt (p : Packet) (a : Nat) : Nat := p.rowTo.getD a 0

/-- RoundedPaid16.weight f k = numerator f k / 10^12, `numer` is the 16×36 table. -/
def weightQ (numer : List (List Int)) (f k : Nat) : Rat := ((numer.getD f []).getD k 0 : Rat) / 1000000000000
def W (numer : List (List Int)) (p : Packet) (k : Nat) : Rat :=
  sumRange 16 (fun f => p.b f * weightQ numer f k)
def rowA (i j q : Nat) : Rat := (if q < j then 1 else 0) - (if q < i then 1 else 0)
def gQ (numer : List (List Int)) (p : Packet) (q : Nat) : Rat :=
  sumRange 36 (fun k => if iOf k ≤ q ∧ q < jOf k then W numer p k * (p.L k).s else 0)
def rho (p : Packet) (q : Nat) : Rat := sumRange 7 (fun a => p.lm a * rowA (p.rf a) (p.rt a) q)
def lamB (n : Node) (p : Packet) : Rat := sumRange 7 (fun a => p.lm a * n.dbQ (p.rf a) (p.rt a))
def cl (numer : List (List Int)) (p : Packet) : Rat :=
  sumRange 36 (fun k => W numer p k * (p.L k).s * ((iOf k : Rat) - (jOf k : Rat)))
def cv (numer : List (List Int)) (p : Packet) : Rat := sumRange 36 (fun k => W numer p k * (p.L k).c)
def lower (numer : List (List Int)) (n : Node) (p : Packet) : Rat :=
  cv numer p + endpointLo Lq LQ (cl numer p) - lamB n p + p.rmin

/-- Field-for-field restatement of `Paid16CellCertificate.Valid` (Fin 16/36/7/9 as `< m`). -/
structure ValidQ (numer : List (List Int)) (n : Node) (p : Packet) : Prop where
  shape : p.beta.length = 16 ∧ p.line.length = 36 ∧ p.lam.length = 7 ∧
    p.rowFrom.length = 7 ∧ p.rowTo.length = 7 ∧ (∀ a, a < 7 → p.rf a < 10 ∧ p.rt a < 10)
  beta_nonneg : ∀ f, f < 16 → 0 ≤ p.b f
  beta_sum : sumRange 16 p.b = 1
  lines : ∀ k, k < 36 → LineValid (p.L k)
  endpoints : ∀ k, k < 36 →
    (p.L k).a ≤ ((iOf k : Rat) - (jOf k : Rat)) * LQ + Dq * slo n k ∧
    ((iOf k : Rat) - (jOf k : Rat)) * Lq + DQ * shi n k ≤ (p.L k).b
  lam_nonneg : ∀ a, a < 7 → 0 ≤ p.lm a
  reduced : ∀ q, q < 9 → p.rmin ≤ endpointLo Dq DQ (gQ numer p q) + rho p q
  numeric : T ^ 2 < lower numer n p
  terminal : n.terminal = true

def allLt (n : Nat) (P : Nat → Prop) [DecidablePred P] : Bool := (List.range n).all (fun k => decide (P k))
theorem allLt_sound {n : Nat} {P : Nat → Prop} [DecidablePred P] (h : allLt n P = true) :
    ∀ k, k < n → P k := by
  intro k hk
  have h2 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using h2

/-- Boolean evaluator; `validB_sound` turns a kernel evaluation into `ValidQ`. -/
def validB (numer : List (List Int)) (n : Node) (p : Packet) : Bool :=
  (decide (p.beta.length = 16) && decide (p.line.length = 36) && decide (p.lam.length = 7) &&
    decide (p.rowFrom.length = 7) && decide (p.rowTo.length = 7) &&
    allLt 7 (fun a => p.rf a < 10 ∧ p.rt a < 10)) &&
  allLt 16 (fun f => 0 ≤ p.b f) && decide (sumRange 16 p.b = 1) &&
  allLt 36 (fun k => LineValid (p.L k)) &&
  allLt 36 (fun k =>
    (p.L k).a ≤ ((iOf k : Rat) - (jOf k : Rat)) * LQ + Dq * slo n k ∧
    ((iOf k : Rat) - (jOf k : Rat)) * Lq + DQ * shi n k ≤ (p.L k).b) &&
  allLt 7 (fun a => 0 ≤ p.lm a) &&
  allLt 9 (fun q => p.rmin ≤ endpointLo Dq DQ (gQ numer p q) + rho p q) &&
  decide (T ^ 2 < lower numer n p) && n.terminal

theorem validB_sound {numer : List (List Int)} {n : Node} {p : Packet}
    (h : validB numer n p = true) : ValidQ numer n p := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, allLt_sound h6⟩, allLt_sound h7, h8, allLt_sound h9,
    allLt_sound h10, allLt_sound h11, allLt_sound h12, h13, h14⟩

end DCPN11Core.EnergyReplay
