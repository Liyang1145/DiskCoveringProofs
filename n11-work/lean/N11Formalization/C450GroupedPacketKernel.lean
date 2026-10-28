import N11Formalization.C450GroupedAmplitude

/-! Genuine grouped packet: only exact rational checks enter Valid.
The real geometry, amplitude, scalar eligibility, widths and ORIGINAL
capacity follow for every actual centre on the closed packet domain.
No actual source family or closed cover is supplied here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedPacketKernel
open scoped Interval
open MeasureTheory
open C450OuterGeometry C450QuadraticBounds C450GroupedGeometry C450GroupedAnalytic
open C450GroupedAmplitude

structure Packet where
  lo : ℚ
  hi : ℚ
  qLo : ℚ
  qHi : ℚ
  ellLo : ℚ
  ellHi : ℚ
  vLo : ℚ
  vHi : ℚ
  zLo : ℚ
  zHi : ℚ
  qt : ℚ
  qb : ℚ
  p0 : ℚ
  p1 : ℚ
  deriving DecidableEq, Repr

def Packet.R (p : Packet) : RatInterval := ⟨p.lo,p.hi⟩
def Packet.Q (p : Packet) : RatInterval := ⟨p.qLo,p.qHi⟩
def Packet.L (p : Packet) : RatInterval := ⟨p.ellLo,p.ellHi⟩
def Packet.V (p : Packet) : RatInterval := ⟨p.vLo,p.vHi⟩
def Packet.Z (p : Packet) : RatInterval := ⟨p.zLo,p.zHi⟩
def Packet.CB (p : Packet) : RatInterval :=
  ⟨min 1 (p.ellLo/(2*(19/50:ℚ))),min 1 (p.ellHi/(2*(19/50:ℚ)))⟩
def offsetInterval (s : TenSeg) : RatInterval := ⟨s.eLo,s.eHi⟩
def rawDirection (s : TenSeg) (p : Packet) : RatInterval :=
  ((p.L.mul p.Q).add (offsetInterval s)).mul ⟨p.hi⁻¹,p.lo⁻¹⟩
def quadQ (B C x : ℚ) : ℚ := x^2+2*B*x+C
def cap (s : TenSeg) : ℚ := RatInterval.piLo*(s.a0+s.b0)/10
def packetUpper (s : TenSeg) (p : Packet) : ℚ :=
  arcUpper s.a0 p.p0 p.qt+arcUpper s.b0 p.p1 p.qb

theorem quadQ_cast (B C x : ℚ) :
    (quadQ B C x:ℝ) = quad (B:ℝ) (C:ℝ) (x:ℝ) := by simp [quadQ,quad]

structure Valid (s : TenSeg) (p : Packet) : Prop where
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
  z_numeric_lower : 0 ≤ minimumQ p.lo p.hi (-p.zLo) (1-(19/50:ℚ)^2)
  z_numeric0 : quadQ (-p.zHi) (1-(19/50:ℚ)^2) p.lo ≤ 0
  z_numeric1 : quadQ (-p.zHi) (1-(19/50:ℚ)^2) p.hi ≤ 0
  v_contains : RatInterval.Contains p.V (clipUnit (rawDirection s p))
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
  scalar0 : |p.p0| ≤ s.a0
  scalar1 : |p.p1| ≤ s.b0
  total_pos : 0 < s.a0+s.b0
  numeric : packetUpper s p < cap s

theorem actual_geometry (s : TenSeg) (p : Packet) (hp : Valid s p)
    (c : Point) (e : ℝ)
    (hr : RatInterval.Mem p.R ‖c‖)
    (he : RatInterval.Mem (offsetInterval s) e)
    (hq : RatInterval.Mem p.Q (c450Cq c e)) :
    RatInterval.Mem p.L (ell c e) ∧
    RatInterval.Mem p.Z (Real.cos (outerT c)) ∧
    RatInterval.Mem p.V (outerV c) ∧
    RatInterval.Mem p.CB (Real.cos (c450B c e)) := by
  have hrLo : (31:ℝ)/50 ≤ (p.lo:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.lower
  have hrHi : (p.hi:ℝ) ≤ (69:ℝ)/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.upper
  have he0 : (0:ℝ) ≤ (s.eLo:ℝ) := by exact_mod_cast hp.e_nonneg
  have he7 : (s.eHi:ℝ) ≤ (7:ℝ)/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.e_upper
  have hEL : (s.eHi:ℝ) ≤ (p.ellLo:ℝ) := by exact_mod_cast hp.ell_lower
  have hLU : (p.ellLo:ℝ) ≤ (p.ellHi:ℝ) := by exact_mod_cast hp.ell_ordered
  have hnumL0 : quad ((p.ellLo:ℝ)*(p.qHi:ℝ)) ((p.ellLo:ℝ)^2) (s.eLo:ℝ) ≤
      (p.lo:ℝ)^2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.ell_numeric0
    simpa only [quadQ_cast,Rat.cast_mul,Rat.cast_pow] using hh
  have hnumL1 : quad ((p.ellLo:ℝ)*(p.qHi:ℝ)) ((p.ellLo:ℝ)^2) (s.eHi:ℝ) ≤
      (p.lo:ℝ)^2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.ell_numeric1
    simpa only [quadQ_cast,Rat.cast_mul,Rat.cast_pow] using hh
  have hnumU : (p.hi:ℝ)^2 ≤
      minimum (s.eLo:ℝ) (s.eHi:ℝ) ((p.ellHi:ℝ)*(p.qLo:ℝ)) ((p.ellHi:ℝ)^2) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.ell_numeric_upper
    simpa only [minimum_cast,Rat.cast_mul,Rat.cast_pow] using hh
  have hL : RatInterval.Mem p.L (ell c e) :=
    ell_bounds he0 he.1 he.2 he7 hrLo hr.1 hr.2 hq.1 hq.2 hEL hLU hnumL0 hnumL1 hnumU
  have hzL : 0 ≤ minimum (p.lo:ℝ) (p.hi:ℝ) (-(p.zLo:ℝ)) (1-(19/50:ℝ)^2) := by
    have hh := (Rat.cast_nonneg (K := ℝ)).mpr hp.z_numeric_lower
    simpa only [minimum_cast,Rat.cast_neg,Rat.cast_sub,Rat.cast_one,
      Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hh
  have hz0 : quad (-(p.zHi:ℝ)) (1-(19/50:ℝ)^2) (p.lo:ℝ) ≤ 0 := by
    have hh := (Rat.cast_nonpos (K := ℝ)).mpr hp.z_numeric0
    simpa only [quadQ_cast,Rat.cast_neg,Rat.cast_sub,Rat.cast_one,
      Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hh
  have hz1 : quad (-(p.zHi:ℝ)) (1-(19/50:ℝ)^2) (p.hi:ℝ) ≤ 0 := by
    have hh := (Rat.cast_nonpos (K := ℝ)).mpr hp.z_numeric1
    simpa only [quadQ_cast,Rat.cast_neg,Rat.cast_sub,Rat.cast_one,
      Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hh
  have hZ : RatInterval.Mem p.Z (zOf ‖c‖) := z_bounds hrLo hr.1 hr.2 hzL hz0 hz1
  have hzg := C450FirstRadialKernel.z_mem (hrLo.trans hr.1) (hr.2.trans hrHi)
  have hcost : Real.cos (outerT c) = zOf ‖c‖ := Real.cos_arccos hzg.1 hzg.2
  have hZcos : RatInterval.Mem p.Z (Real.cos (outerT c)) := by rw [hcost]; exact hZ
  have hden : p.R.hi < 0 ∨ 0 < p.R.lo := by
    right
    change 0 < p.lo
    linarith [hp.lower]
  have hpos : 0 < ell c e := by
    have hh := ell_lower_global (he0.trans he.1) (he.2.trans he7) (hrLo.trans hr.1)
    linarith
  have hv := direction_interval p.L p.Q (offsetInterval s) p.R hden hpos hL hq he hr
  change RatInterval.Mem (rawDirection s p) (outerV c) at hv
  have hV := RatInterval.mem_of_contains hp.v_contains
    (clipped_direction (rawDirection s p) (hrLo.trans hr.1) hv)
  have hcb := cosine_beta_bounds hL.1 hL.2
  change min 1 ((p.ellLo:ℝ)/(2*(19/50:ℝ))) ≤ Real.cos (c450B c e) ∧
    Real.cos (c450B c e) ≤ min 1 ((p.ellHi:ℝ)/(2*(19/50:ℝ))) at hcb
  have hCB : RatInterval.Mem p.CB (Real.cos (c450B c e)) := by
    change ((min 1 (p.ellLo/(2*(19/50:ℚ))):ℚ):ℝ) ≤ Real.cos (c450B c e) ∧
      Real.cos (c450B c e) ≤ ((min 1 (p.ellHi/(2*(19/50:ℚ))):ℚ):ℝ)
    simpa only [Rat.cast_min,Rat.cast_one,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hcb
  exact ⟨hL,hZcos,hV,hCB⟩

theorem cap_lt_actual (s : TenSeg) (hpos : 0 < s.a0+s.b0) :
    (cap s:ℝ) < Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10 := by
  have hs : (0:ℝ) < (s.a0:ℝ)+(s.b0:ℝ) := by exact_mod_cast hpos
  have hh := div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right RatInterval.piLo_lt_pi hs) (by norm_num : (0:ℝ) < 10)
  simpa [cap] using hh

/-- All nonnumeric amplitude/geometry/width/scalar obligations are paid by
the kernel. Valid stays explicit until actual exact packet checks pass. -/
theorem packet_bound (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0)
    (p : Packet) (hp : Valid s p) (c : Point) (e : ℝ)
    (hr : RatInterval.Mem p.R ‖c‖)
    (he : RatInterval.Mem (offsetInterval s) e)
    (hq : RatInterval.Mem p.Q (c450Cq c e)) :
    c450Outer (s.W0 h0) c+c450Inner (s.W1 h1) c e <
      Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10 := by
  obtain ⟨hL,hZ,hV,hCB⟩ := actual_geometry s p hp c e hr he hq
  have hrLo : (31:ℝ)/50 ≤ (p.lo:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.lower
  have hrHi : (p.hi:ℝ) ≤ (69:ℝ)/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.upper
  have hc0 := hrLo.trans hr.1
  have hc1 := hr.2.trans hrHi
  have ha0 := actual_amplitude_le (s.W0 h0) s.a1 s.a2 s.a3 p.p0 p.Z p.V
    rfl rfl rfl hp.z_nonneg hp.v_lower hp.v_upper hZ hV hp.amplitude0
  have ha1 := actual_amplitude_le (s.W1 h1) s.b1 s.b2 s.b3 p.p1 p.CB p.Q
    rfl rfl rfl hp.cb_nonneg hp.q_lower hp.q_upper hCB hq hp.amplitude1
  have hp0 : |(p.p0:ℝ)| ≤ (s.W0 h0).a0 := by
    change |(p.p0:ℝ)| ≤ (s.a0:ℝ)
    exact_mod_cast hp.scalar0
  have hp1 : |(p.p1:ℝ)| ≤ (s.W1 h1).a0 := by
    change |(p.p1:ℝ)| ≤ (s.b0:ℝ)
    exact_mod_cast hp.scalar1
  have hcost := Real.cos_arccos (C450FirstRadialKernel.z_mem hc0 hc1).1
    (C450FirstRadialKernel.z_mem hc0 hc1).2
  have hz : (p.zLo:ℝ) ≤ zOf ‖c‖ := by
    have hh := RatInterval.mem_lo_le hZ
    change (p.zLo:ℝ) ≤ Real.cos (Real.arccos (zOf ‖c‖)) at hh
    rwa [hcost] at hh
  have ht := outer_width_le p.qt hc0 hc1 hp.qt_nonneg hz
    ((Rat.cast_le (K := ℝ)).mpr hp.t_cos)
  have hb := inner_width_le c e p.qb hp.qb_nonneg (RatInterval.mem_lo_le hCB)
    ((Rat.cast_le (K := ℝ)).mpr hp.b_cos)
  have hpair := actual_pair_bound (s.W0 h0) (s.W1 h1) c e
    (p.p0:ℝ) (p.p1:ℝ) (p.qt:ℝ) (p.qb:ℝ)
    (by linarith : 1-19/50 ≤ ‖c‖) (by linarith : ‖c‖ ≤ 1+19/50)
    ha0 ha1 hp0 hp1 ht hb
  have harc : arc (s.W0 h0).a0 (p.p0:ℝ) (p.qt:ℝ)+
      arc (s.W1 h1).a0 (p.p1:ℝ) (p.qb:ℝ) ≤ (packetUpper s p:ℝ) := by
    simpa only [packetUpper,Rat.cast_add,TenSeg.W0,TenSeg.W1] using
      add_le_add (arc_upper s.a0 p.p0 p.qt) (arc_upper s.b0 p.p1 p.qb)
  have hnum := (Rat.cast_lt (K := ℝ)).mpr hp.numeric
  exact (hpair.trans harc).trans_lt (hnum.trans (cap_lt_actual s hp.total_pos))

/-- Actual canonical circle integrals, including empty and tangent arcs.
This interpretation is asserted ONLY on the legal domain obtained from
Valid and actual closed norm/offset/direction membership. -/
theorem packet_integrals (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0)
    (p : Packet) (hp : Valid s p) (c : Point) (e : ℝ)
    (hr : RatInterval.Mem p.R ‖c‖)
    (he : RatInterval.Mem (offsetInterval s) e)
    (hq : RatInterval.Mem p.Q (c450Cq c e)) :
    (∫ θ in (0)..(2*Real.pi),
      if dist (angPt θ) c ≤ (19/50:ℝ) then (s.W0 h0).toFun θ else 0) +
    (∫ θ in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt θ) c ≤ (19/50:ℝ)
        then (s.W1 h1).toFun θ else 0) <
      (2*Real.pi*(s.a0:ℝ)+2*Real.pi*(s.b0:ℝ))/10 := by
  have hrLo : (31:ℝ)/50 ≤ (p.lo:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.lower
  have hrHi : (p.hi:ℝ) ≤ (69:ℝ)/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.upper
  have heLo : (0:ℝ) ≤ (s.eLo:ℝ) := by exact_mod_cast hp.e_nonneg
  have heHi : (s.eHi:ℝ) ≤ (7:ℝ)/50 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hp.e_upper
  have hc0 := hrLo.trans hr.1
  have hc1 := hr.2.trans hrHi
  have hpair := pair_canonical (s.W0 h0) (s.W1 h1)
    (heLo.trans he.1) (he.2.trans heHi)
    (by linarith : 1-19/50 ≤ ‖c‖) (by linarith : ‖c‖ ≤ 1+19/50)
  change _+_ = 2*c450Outer (s.W0 h0) c+2*c450Inner (s.W1 h1) c e at hpair
  unfold hubPt
  rw [hpair]
  have hh := mul_lt_mul_of_pos_left (packet_bound s h0 h1 p hp c e hr he hq)
    (by norm_num : (0:ℝ) < 2)
  have hrhs : 2*(Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10) =
      (2*Real.pi*(s.a0:ℝ)+2*Real.pi*(s.b0:ℝ))/10 := by ring
  rw [hrhs] at hh
  simpa only [mul_add] using hh

end N11Formalization.C450GroupedPacketKernel
#check @N11Formalization.C450GroupedPacketKernel.actual_geometry
#check @N11Formalization.C450GroupedPacketKernel.packet_bound
#print axioms N11Formalization.C450GroupedPacketKernel.actual_geometry
#print axioms N11Formalization.C450GroupedPacketKernel.cap_lt_actual
#print axioms N11Formalization.C450GroupedPacketKernel.packet_bound
#check @N11Formalization.C450GroupedPacketKernel.packet_integrals
#print axioms N11Formalization.C450GroupedPacketKernel.packet_integrals
