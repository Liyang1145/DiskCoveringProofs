import N11Formalization.C450AngularMajorant
import N11Formalization.C450FirstRadialKernel

/-! Three actual second-segment models. Concrete packets are paid separately. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SecondRadialKernel
open C450AngularMajorant C450RadialMajorant

inductive Branch where
  | neg | mid | pos
  deriving DecidableEq

def R : ℚ := 19/50
def E : ℚ := 71/10000
def A : ℚ := 641363/250000
def B : ℚ := 42283/62500
def H : ℚ := -48331/1000000
def tail : ℚ := B+|(431:ℚ)/500000|+|(77:ℚ)/1000000|
def F : Branch → ℚ
  | .neg => E^2
  | .mid => E/2+E^2
  | .pos => E+E^2
def M : Branch → ℚ
  | .neg => tail-H
  | .mid => tail
  | .pos => tail+(2/5)*H
def cap : ℚ := RatInterval.piLo*(A+B)/10
def finish (k : Branch) : ℚ := 2*R+F k
def betaCos (k : Branch) (r : ℚ) : ℚ := (r-F k)/(2*R)
def model (k : Branch) (r : ℝ) : ℝ :=
  angularModel (A:ℝ) (M k:ℝ) (F k:ℝ) r
abbrev Packet := C450FirstRadialKernel.Packet

structure Valid (k : Branch) (p : Packet) : Prop where
  lower : 31/50 ≤ p.lo
  ordered : p.lo ≤ p.hi
  upper : p.hi ≤ 69/50
  turn : p.hi^2 ≤ 1-R^2
  qt_nonneg : 0 ≤ p.qt
  qb_nonneg : 0 ≤ p.qb
  t_cos : cosHiNLag p.qt ≤ C450FirstRadialKernel.zQ p.hi
  beta_cos : cosHiNLag p.qb ≤ betaCos k p.lo
  beta_domain : -1 ≤ betaCos k p.lo ∧ betaCos k p.lo ≤ 1
  numeric : A*p.qt+M k*p.qb < cap

theorem betaCos_cast (k : Branch) (r : ℚ) :
    (betaCos k r:ℝ) = ((r:ℝ)-(F k:ℝ))/(2*(19/50:ℝ)) := by
  simp [betaCos,R]

theorem M_nonneg (k : Branch) : (0:ℝ) ≤ (M k:ℝ) := by
  cases k <;> norm_num [M,tail,B,H]

theorem packet_bound (k : Branch) (p : Packet) (hp : Valid k p) (r : ℝ)
    (hr : r ∈ Set.Icc (p.lo:ℝ) (p.hi:ℝ)) : model k r < (cap:ℝ) := by
  have hlo : (31:ℝ)/50 ≤ (p.lo:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.lower
    norm_num at hh
    exact hh
  have hhi : (p.hi:ℝ) ≤ (69:ℝ)/50 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.upper
    norm_num at hh
    exact hh
  have hpos : 0 < r := by linarith [hr.1]
  have hhipos : 0 < (p.hi:ℝ) := by linarith [hr.1,hr.2]
  have hturn : (p.hi:ℝ)^2 ≤ 1-(19/50:ℝ)^2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.turn
    simpa only [Rat.cast_pow,Rat.cast_sub,Rat.cast_one,R,Rat.cast_div,Rat.cast_ofNat] using hh
  have hprod : r*(p.hi:ℝ) ≤ 1-(19/50:ℝ)^2 :=
    (mul_le_mul_of_nonneg_right hr.2 hhipos.le).trans (by simpa only [pow_two] using hturn)
  have hmono : zOf (p.hi:ℝ) ≤ zOf r :=
    z_antitone_on hpos hhipos hr.2 hprod
  have hz := C450FirstRadialKernel.z_mem (hlo.trans hr.1) (hr.2.trans hhi)
  have hcost : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have htc : ((cosHiNLag p.qt:ℚ):ℝ) ≤ zOf (p.hi:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.t_cos
    rwa [C450FirstRadialKernel.zQ_cast] at hh
  have ht : Real.arccos (zOf r) ≤ (p.qt:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hp.qt_nonneg)
      (Real.arccos_le_pi _) hcost (htc.trans hmono)
  have hbetaDomain : (betaCos k p.lo:ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · exact_mod_cast hp.beta_domain.1
    · exact_mod_cast hp.beta_domain.2
  have hcosb : Real.cos (Real.arccos (betaCos k p.lo:ℝ)) = (betaCos k p.lo:ℝ) :=
    Real.cos_arccos hbetaDomain.1 hbetaDomain.2
  have hbc : ((cosHiNLag p.qb:ℚ):ℝ) ≤ (betaCos k p.lo:ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr hp.beta_cos
  have hb0 : Real.arccos (betaCos k p.lo:ℝ) ≤ (p.qb:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hp.qb_nonneg)
      (Real.arccos_le_pi _) hcosb hbc
  have hbm : betaUpper r (F k:ℝ) ≤ Real.arccos (betaCos k p.lo:ℝ) := by
    unfold betaUpper
    rw [betaCos_cast]
    apply Real.arccos_le_arccos
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sub_le_sub_right hr.1 _
  have hA : (0:ℝ) ≤ (A:ℝ) := by norm_num [A]
  have hmodel : model k r ≤ (A:ℝ)*(p.qt:ℝ)+(M k:ℝ)*(p.qb:ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left ht hA)
      (mul_le_mul_of_nonneg_left (hbm.trans hb0) (M_nonneg k))
  have hnum : (A:ℝ)*(p.qt:ℝ)+(M k:ℝ)*(p.qb:ℝ) < (cap:ℝ) := by exact_mod_cast hp.numeric
  exact hmodel.trans_lt hnum

theorem cap_lt_actual : (cap:ℝ) < Real.pi*((A:ℝ)+(B:ℝ))/10 := by
  have hh := mul_lt_mul_of_pos_right RatInterval.piLo_lt_pi
    (by norm_num [A,B] : (0:ℝ) < (A:ℝ)+(B:ℝ))
  have hd := div_lt_div_of_pos_right hh (by norm_num : (0:ℝ) < 10)
  simpa [cap] using hd

theorem far_bound (k : Branch) (r : ℝ)
    (hr : r ∈ Set.Icc (finish k:ℝ) ((69:ℝ)/50)) : model k r < (cap:ℝ) := by
  have hfinish : (31:ℝ)/50 ≤ (finish k:ℝ) := by
    cases k <;> norm_num [finish,F,E,R]
  have hz := C450FirstRadialKernel.z_mem (hfinish.trans hr.1) hr.2
  have hc : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have ht := t_le_global (by linarith [hr.1] : 0 < r) (Real.arccos_le_pi _) hc
  have hb : betaUpper r (F k:ℝ) = 0 := by
    unfold betaUpper
    apply Real.arccos_of_one_le
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*(19/50))]
    have hh : (finish k:ℝ) = 2*(19/50:ℝ)+(F k:ℝ) := by simp [finish,R]
    linarith [hr.1]
  have hA : (0:ℝ) ≤ (A:ℝ) := by norm_num [A]
  have hm := mul_le_mul_of_nonneg_left ht hA
  have hnum : A*Tglobal < cap := by decide +kernel
  have hnr : (A:ℝ)*(Tglobal:ℝ) < (cap:ℝ) := by exact_mod_cast hnum
  unfold model angularModel
  rw [hb,mul_zero,add_zero]
  exact hm.trans_lt hnr
end N11Formalization.C450SecondRadialKernel
#check @N11Formalization.C450SecondRadialKernel.packet_bound
#check @N11Formalization.C450SecondRadialKernel.far_bound
#print axioms N11Formalization.C450SecondRadialKernel.packet_bound
#print axioms N11Formalization.C450SecondRadialKernel.far_bound
