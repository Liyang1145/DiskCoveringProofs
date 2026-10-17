import N11Formalization.C450AngularMajorant
import N11Formalization.C450FirstRadialKernel

/-! Rational coefficients and SIGNED offsets; exact closed radial packet
soundness. Parameter and packet validity stay explicit until instantiated. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450RadialPacketKernel
open C450AngularMajorant C450RadialMajorant

structure Params where
  A : ℚ
  B : ℚ
  M : ℚ
  F : ℚ

def cap (p : Params) : ℚ := RatInterval.piLo*(p.A+p.B)/10
def finish (p : Params) : ℚ := 2*(19/50:ℚ)+p.F
def betaCos (p : Params) (r : ℚ) : ℚ := (r-p.F)/(2*(19/50:ℚ))
def model (p : Params) (r : ℝ) : ℝ :=
  angularModel (p.A:ℝ) (p.M:ℝ) (p.F:ℝ) r
abbrev Packet := C450FirstRadialKernel.Packet

structure ValidParams (p : Params) : Prop where
  A_nonneg : 0 ≤ p.A
  M_nonneg : 0 ≤ p.M
  total_pos : 0 < p.A+p.B
  finish_lower : 31/50 ≤ finish p
  far_numeric : p.A*Tglobal < cap p

structure Valid (p : Params) (q : Packet) : Prop where
  lower : 31/50 ≤ q.lo
  ordered : q.lo ≤ q.hi
  upper : q.hi ≤ 69/50
  turn : q.hi^2 ≤ 1-(19/50:ℚ)^2
  qt_nonneg : 0 ≤ q.qt
  qb_nonneg : 0 ≤ q.qb
  t_cos : cosHiNLag q.qt ≤ C450FirstRadialKernel.zQ q.hi
  beta_cos : cosHiNLag q.qb ≤ betaCos p q.lo
  beta_domain : -1 ≤ betaCos p q.lo ∧ betaCos p q.lo ≤ 1
  numeric : p.A*q.qt+p.M*q.qb < cap p

theorem betaCos_cast (p : Params) (r : ℚ) :
    (betaCos p r:ℝ) = ((r:ℝ)-(p.F:ℝ))/(2*(19/50:ℝ)) := by
  simp [betaCos]

theorem packet_bound (p : Params) (hp : ValidParams p)
    (q : Packet) (hq : Valid p q) (r : ℝ)
    (hr : r ∈ Set.Icc (q.lo:ℝ) (q.hi:ℝ)) : model p r < (cap p:ℝ) := by
  have hlo : (31:ℝ)/50 ≤ (q.lo:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hq.lower
    norm_num at hh
    exact hh
  have hhi : (q.hi:ℝ) ≤ (69:ℝ)/50 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hq.upper
    norm_num at hh
    exact hh
  have hpos : 0 < r := by linarith [hr.1]
  have hhipos : 0 < (q.hi:ℝ) := by linarith [hr.1,hr.2]
  have hturn : (q.hi:ℝ)^2 ≤ 1-(19/50:ℝ)^2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hq.turn
    simpa only [Rat.cast_pow,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using hh
  have hprod : r*(q.hi:ℝ) ≤ 1-(19/50:ℝ)^2 :=
    (mul_le_mul_of_nonneg_right hr.2 hhipos.le).trans (by simpa only [pow_two] using hturn)
  have hmono : zOf (q.hi:ℝ) ≤ zOf r :=
    z_antitone_on hpos hhipos hr.2 hprod
  have hz := C450FirstRadialKernel.z_mem (hlo.trans hr.1) (hr.2.trans hhi)
  have hcost : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have htc : ((cosHiNLag q.qt:ℚ):ℝ) ≤ zOf (q.hi:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hq.t_cos
    rwa [C450FirstRadialKernel.zQ_cast] at hh
  have ht : Real.arccos (zOf r) ≤ (q.qt:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hq.qt_nonneg)
      (Real.arccos_le_pi _) hcost (htc.trans hmono)
  have hbetaDomain : (betaCos p q.lo:ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · exact_mod_cast hq.beta_domain.1
    · exact_mod_cast hq.beta_domain.2
  have hcosb : Real.cos (Real.arccos (betaCos p q.lo:ℝ)) = (betaCos p q.lo:ℝ) :=
    Real.cos_arccos hbetaDomain.1 hbetaDomain.2
  have hbc : ((cosHiNLag q.qb:ℚ):ℝ) ≤ (betaCos p q.lo:ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr hq.beta_cos
  have hb0 : Real.arccos (betaCos p q.lo:ℝ) ≤ (q.qb:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hq.qb_nonneg)
      (Real.arccos_le_pi _) hcosb hbc
  have hbm : betaUpper r (p.F:ℝ) ≤ Real.arccos (betaCos p q.lo:ℝ) := by
    unfold betaUpper
    rw [betaCos_cast]
    apply Real.arccos_le_arccos
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sub_le_sub_right hr.1 _
  have hA : (0:ℝ) ≤ (p.A:ℝ) := (Rat.cast_nonneg (K := ℝ)).mpr hp.A_nonneg
  have hM : (0:ℝ) ≤ (p.M:ℝ) := (Rat.cast_nonneg (K := ℝ)).mpr hp.M_nonneg
  have hmodel : model p r ≤ (p.A:ℝ)*(q.qt:ℝ)+(p.M:ℝ)*(q.qb:ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left ht hA)
      (mul_le_mul_of_nonneg_left (hbm.trans hb0) hM)
  have hnum : (p.A:ℝ)*(q.qt:ℝ)+(p.M:ℝ)*(q.qb:ℝ) < (cap p:ℝ) := by exact_mod_cast hq.numeric
  exact hmodel.trans_lt hnum

theorem cap_lt_actual (p : Params) (hp : ValidParams p) :
    (cap p:ℝ) < Real.pi*((p.A:ℝ)+(p.B:ℝ))/10 := by
  have hsum : (0:ℝ) < (p.A:ℝ)+(p.B:ℝ) := by exact_mod_cast hp.total_pos
  have hh := mul_lt_mul_of_pos_right RatInterval.piLo_lt_pi hsum
  have hd := div_lt_div_of_pos_right hh (by norm_num : (0:ℝ) < 10)
  simpa [cap] using hd

theorem far_bound (p : Params) (hp : ValidParams p) (r : ℝ)
    (hr : r ∈ Set.Icc (finish p:ℝ) ((69:ℝ)/50)) : model p r < (cap p:ℝ) := by
  have hfinish : (31:ℝ)/50 ≤ (finish p:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.finish_lower
    norm_num at hh
    exact hh
  have hz := C450FirstRadialKernel.z_mem (hfinish.trans hr.1) hr.2
  have hc : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have ht := t_le_global (by linarith [hr.1] : 0 < r) (Real.arccos_le_pi _) hc
  have hb : betaUpper r (p.F:ℝ) = 0 := by
    unfold betaUpper
    apply Real.arccos_of_one_le
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*(19/50))]
    have hh : (finish p:ℝ) = 2*(19/50:ℝ)+(p.F:ℝ) := by simp [finish]
    linarith [hr.1]
  have hA : (0:ℝ) ≤ (p.A:ℝ) := (Rat.cast_nonneg (K := ℝ)).mpr hp.A_nonneg
  have hm := mul_le_mul_of_nonneg_left ht hA
  have hnr : (p.A:ℝ)*(Tglobal:ℝ) < (cap p:ℝ) := by exact_mod_cast hp.far_numeric
  unfold model angularModel
  rw [hb,mul_zero,add_zero]
  exact hm.trans_lt hnr

theorem closed_of_near (p : Params) (hp : ValidParams p)
    (hn : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish p:ℝ), model p r < (cap p:ℝ)) :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model p r < (cap p:ℝ) :=
  C450FirstRadialKernel.interval_join hn (fun r hr => far_bound p hp r hr)
end N11Formalization.C450RadialPacketKernel
#check @N11Formalization.C450RadialPacketKernel.packet_bound
#check @N11Formalization.C450RadialPacketKernel.closed_of_near
#print axioms N11Formalization.C450RadialPacketKernel.packet_bound
#print axioms N11Formalization.C450RadialPacketKernel.cap_lt_actual
#print axioms N11Formalization.C450RadialPacketKernel.closed_of_near
