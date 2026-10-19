/-
Core-Lean (no Mathlib) replay of the exact-rational side conditions of the team WIP's
`N11Formalization.C450GroupedPacketKernel.Valid` (snapshot n11-wip-0001, root f6e3419a…).

`ValidQ` below restates the 29 fields of the WIP `Valid` verbatim as propositions over `Rat`
(the WIP `Valid` is itself a Prop over `ℚ` only). Auxiliary functions are transcribed from
Interval/Core.lean, C450QuadraticBounds.lean, C450GroupedGeometry.lean, C450GroupedAmplitude.lean,
C450GroupedAnalytic.lean, IntervalsHigh(.lean/Lag.lean), Interval/Trig.lean (piLo):
  * `qabs q = if q < 0 then -q else q`   (value-equal to Mathlib `|q| = max q (-q)`),
  * `min`/`max` core `Rat` instances    (value-equal to Mathlib lattice min/max on ℚ),
  * finite sums `∑ k ∈ range m` as a `List.range` fold, `Nat.factorial` as `fact`.
This does NOT prove the real-analytic `CellBound`/`SegmentNormalized`; it only certifies, in
the Lean kernel, that the rational premises the WIP soundness lemma `cell_of_packet` consumes
hold for the emitted data, plus the structural tiling the WIP assembly relies on.
-/
namespace DCPN11Core.C450Replay

structure RI where
  lo : Rat
  hi : Rat

structure TenSeg where
  eLo : Rat
  eHi : Rat
  a0 : Rat
  a1 : Rat
  a2 : Rat
  a3 : Rat
  b0 : Rat
  b1 : Rat
  b2 : Rat
  b3 : Rat

structure Packet where
  lo : Rat
  hi : Rat
  qLo : Rat
  qHi : Rat
  ellLo : Rat
  ellHi : Rat
  vLo : Rat
  vHi : Rat
  zLo : Rat
  zHi : Rat
  qt : Rat
  qb : Rat
  p0 : Rat
  p1 : Rat

def qabs (q : Rat) : Rat := if q < 0 then -q else q
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

namespace RI
def ofRat (q : Rat) : RI := ⟨q, q⟩
def add (A B : RI) : RI := ⟨A.lo + B.lo, A.hi + B.hi⟩
def mul (A B : RI) : RI :=
  ⟨min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)),
   max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))⟩
def Contains (I J : RI) : Prop := I.lo ≤ J.lo ∧ J.hi ≤ I.hi
end RI

def piLo : Rat := 314159265358979323846 / 10 ^ 20
def sumRange (m : Nat) (f : Nat → Rat) : Rat := (List.range m).foldl (fun acc k => acc + f k) 0
def sinTQ (m : Nat) (q : Rat) : Rat :=
  sumRange m (fun k => (-1 : Rat) ^ k * q ^ (2 * k + 1) / ((fact (2 * k + 1) : Nat) : Rat))
def cosTQ (m : Nat) (q : Rat) : Rat :=
  sumRange m (fun k => (-1 : Rat) ^ k * q ^ (2 * k) / ((fact (2 * k) : Nat) : Rat))
def sinLoNLag (q : Rat) : Rat := sinTQ 14 q - qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def sinHiNLag (q : Rat) : Rat := sinTQ 14 q + qabs q ^ 29 / ((fact 29 : Nat) : Rat)
def cosHiNLag (q : Rat) : Rat := cosTQ 14 q + qabs q ^ 28 / ((fact 28 : Nat) : Rat)

def quadQ (B C x : Rat) : Rat := x^2 + 2*B*x + C
def minimumQ (lo hi B C : Rat) : Rat :=
  (min hi (max lo (-B)))^2 + 2*B*(min hi (max lo (-B))) + C
def clipUnit (I : RI) : RI := ⟨max (-1) I.lo, min 1 I.hi⟩
def p2Q (x : Rat) : Rat := 2*x^2 - 1
def p3Q (x : Rat) : Rat := 4*x^3 - 3*x
def lower2Q (lo hi : Rat) : Rat := p2Q (min hi (max lo 0))
def upper2Q (lo hi : Rat) : Rat := max (p2Q lo) (p2Q hi)
def lower3Q (lo hi : Rat) : Rat :=
  if lo ≤ 1/2 ∧ 1/2 ≤ hi then -1 else min (p3Q lo) (p3Q hi)
def upper3Q (lo hi : Rat) : Rat :=
  if lo ≤ -1/2 ∧ -1/2 ≤ hi then 1 else max (p3Q lo) (p3Q hi)
def range2Q (I : RI) : RI := ⟨lower2Q I.lo I.hi, upper2Q I.lo I.hi⟩
def range3Q (I : RI) : RI := ⟨lower3Q I.lo I.hi, upper3Q I.lo I.hi⟩
def squareThird (I : RI) : RI := ⟨(4*I.lo^2-1)/3, (4*I.hi^2-1)/3⟩
def amplitudeInterval (a1 a2 a3 : Rat) (Z V : RI) : RI :=
  (((RI.ofRat a1).mul V).add ((RI.ofRat a2).mul (Z.mul (range2Q V)))).add
    ((RI.ofRat a3).mul ((squareThird Z).mul (range3Q V)))
def sineProductUpper (p t : Rat) : Rat := p * (if 0 ≤ p then sinHiNLag t else sinLoNLag t)
def arcUpper (a p t : Rat) : Rat := a*t + sineProductUpper p t

def Packet.Q (p : Packet) : RI := ⟨p.qLo, p.qHi⟩
def Packet.Z (p : Packet) : RI := ⟨p.zLo, p.zHi⟩
def Packet.V (p : Packet) : RI := ⟨p.vLo, p.vHi⟩
def Packet.L (p : Packet) : RI := ⟨p.ellLo, p.ellHi⟩
def Packet.CB (p : Packet) : RI :=
  ⟨min 1 (p.ellLo/(2*(19/50:Rat))), min 1 (p.ellHi/(2*(19/50:Rat)))⟩
def offsetInterval (s : TenSeg) : RI := ⟨s.eLo, s.eHi⟩
def rawDirection (s : TenSeg) (p : Packet) : RI :=
  ((p.L.mul p.Q).add (offsetInterval s)).mul ⟨p.hi⁻¹, p.lo⁻¹⟩
def cap (s : TenSeg) : Rat := piLo*(s.a0+s.b0)/10
def packetUpper (s : TenSeg) (p : Packet) : Rat := arcUpper s.a0 p.p0 p.qt + arcUpper s.b0 p.p1 p.qb

/-- Field-for-field restatement of the WIP `C450GroupedPacketKernel.Valid`. -/
structure ValidQ (s : TenSeg) (p : Packet) : Prop where
  e_nonneg : 0 ≤ s.eLo
  e_upper : s.eHi ≤ 7/50
  lower : 31/50 ≤ p.lo
  ordered : p.lo ≤ p.hi
  upper : p.hi ≤ 69/50
  q_lower : -1 ≤ p.qLo
  q_upper : p.qHi ≤ 1
  ell_lower : s.eHi ≤ p.ellLo
  ell_ordered : p.ellLo ≤ p.ellHi
  ell_numeric0 : quadQ (p.ellLo*p.qHi) (p.ellLo^2) s.eLo ≤ p.lo^2
  ell_numeric1 : quadQ (p.ellLo*p.qHi) (p.ellLo^2) s.eHi ≤ p.lo^2
  ell_numeric_upper : p.hi^2 ≤ minimumQ s.eLo s.eHi (p.ellHi*p.qLo) (p.ellHi^2)
  z_numeric_lower : 0 ≤ minimumQ p.lo p.hi (-p.zLo) (1-(19/50:Rat)^2)
  z_numeric0 : quadQ (-p.zHi) (1-(19/50:Rat)^2) p.lo ≤ 0
  z_numeric1 : quadQ (-p.zHi) (1-(19/50:Rat)^2) p.hi ≤ 0
  v_contains : RI.Contains p.V (clipUnit (rawDirection s p))
  v_lower : -1 ≤ p.vLo
  v_upper : p.vHi ≤ 1
  z_nonneg : 0 ≤ p.zLo
  cb_nonneg : 0 ≤ p.CB.lo
  qt_nonneg : 0 ≤ p.qt
  qb_nonneg : 0 ≤ p.qb
  t_cos : cosHiNLag p.qt ≤ p.zLo
  b_cos : cosHiNLag p.qb ≤ p.CB.lo
  amplitude0 : (amplitudeInterval s.a1 s.a2 s.a3 p.Z p.V).hi ≤ p.p0
  amplitude1 : (amplitudeInterval s.b1 s.b2 s.b3 p.CB p.Q).hi ≤ p.p1
  scalar0 : qabs p.p0 ≤ s.a0
  scalar1 : qabs p.p1 ≤ s.b0
  total_pos : 0 < s.a0+s.b0
  numeric : packetUpper s p < cap s

def validB (s : TenSeg) (p : Packet) : Bool :=
  decide (0 ≤ s.eLo) && decide (s.eHi ≤ 7/50) && decide (31/50 ≤ p.lo) && decide (p.lo ≤ p.hi) &&
  decide (p.hi ≤ 69/50) && decide (-1 ≤ p.qLo) && decide (p.qHi ≤ 1) && decide (s.eHi ≤ p.ellLo) &&
  decide (p.ellLo ≤ p.ellHi) &&
  decide (quadQ (p.ellLo*p.qHi) (p.ellLo^2) s.eLo ≤ p.lo^2) &&
  decide (quadQ (p.ellLo*p.qHi) (p.ellLo^2) s.eHi ≤ p.lo^2) &&
  decide (p.hi^2 ≤ minimumQ s.eLo s.eHi (p.ellHi*p.qLo) (p.ellHi^2)) &&
  decide (0 ≤ minimumQ p.lo p.hi (-p.zLo) (1-(19/50:Rat)^2)) &&
  decide (quadQ (-p.zHi) (1-(19/50:Rat)^2) p.lo ≤ 0) &&
  decide (quadQ (-p.zHi) (1-(19/50:Rat)^2) p.hi ≤ 0) &&
  decide (p.V.lo ≤ (clipUnit (rawDirection s p)).lo) &&
  decide ((clipUnit (rawDirection s p)).hi ≤ p.V.hi) &&
  decide (-1 ≤ p.vLo) && decide (p.vHi ≤ 1) && decide (0 ≤ p.zLo) && decide (0 ≤ p.CB.lo) &&
  decide (0 ≤ p.qt) && decide (0 ≤ p.qb) &&
  decide (cosHiNLag p.qt ≤ p.zLo) && decide (cosHiNLag p.qb ≤ p.CB.lo) &&
  decide ((amplitudeInterval s.a1 s.a2 s.a3 p.Z p.V).hi ≤ p.p0) &&
  decide ((amplitudeInterval s.b1 s.b2 s.b3 p.CB p.Q).hi ≤ p.p1) &&
  decide (qabs p.p0 ≤ s.a0) && decide (qabs p.p1 ≤ s.b0) && decide (0 < s.a0+s.b0) &&
  decide (packetUpper s p < cap s)

theorem validB_sound {s : TenSeg} {p : Packet} (h : validB s p = true) : ValidQ s p := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,
    h14⟩,h15⟩,h16⟩,h17⟩,h18⟩,h19⟩,h20⟩,h21⟩,h22⟩,h23⟩,h24⟩,h25⟩,h26⟩,h27⟩,h28⟩,h29⟩,h30⟩,h31⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,⟨h16,h17⟩,h18,h19,h20,h21,h22,h23,h24,
    h25,h26,h27,h28,h29,h30,h31⟩

/-- A grouped cell: its direction interval `Qcell` and its packets in radial order. -/
structure Cell where
  q : RI
  packets : List Packet

/-- Radial chain: consecutive packets share endpoints, starting at `a` and ending at `b`. -/
def chainB : Rat → Rat → List Packet → Bool
  | a, b, [] => decide (a = b)
  | a, b, p :: ps => decide (p.lo = a) && chainB p.hi b ps

/-- Direction cells tile `[a,b]` in order. -/
def tileB : Rat → Rat → List RI → Bool
  | a, b, [] => decide (a = b)
  | a, b, q :: qs => decide (q.lo = a) && decide (q.lo ≤ q.hi) && tileB q.hi b qs

def cellB (s : TenSeg) (c : Cell) : Bool :=
  !c.packets.isEmpty && chainB (31/50) (69/50) c.packets &&
  c.packets.all (fun p => decide (p.qLo = c.q.lo) && decide (p.qHi = c.q.hi) && validB s p)

/-- `nn0`/`nn1`/`eHi_le` of the WIP `C450SourceKData`. -/
def segHeadB (s : TenSeg) : Bool :=
  decide (qabs s.a1 + qabs s.a2 + qabs s.a3 ≤ s.a0) &&
  decide (qabs s.b1 + qabs s.b2 + qabs s.b3 ≤ s.b0) && decide (s.eHi ≤ 7/50)

def TenSeg.beq (s t : TenSeg) : Bool :=
  decide (s.eLo = t.eLo) && decide (s.eHi = t.eHi) && decide (s.a0 = t.a0) && decide (s.a1 = t.a1) &&
  decide (s.a2 = t.a2) && decide (s.a3 = t.a3) && decide (s.b0 = t.b0) && decide (s.b1 = t.b1) &&
  decide (s.b2 = t.b2) && decide (s.b3 = t.b3)

theorem cellB_packet {s : TenSeg} {c : Cell} (h : cellB s c = true) :
    ∀ p ∈ c.packets, ValidQ s p ∧ p.qLo = c.q.lo ∧ p.qHi = c.q.hi := by
  intro p hp
  simp only [cellB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, _⟩, hall⟩ := h
  obtain ⟨⟨h1, h2⟩, h3⟩ := hall p hp
  exact ⟨validB_sound h3, h1, h2⟩

end DCPN11Core.C450Replay
