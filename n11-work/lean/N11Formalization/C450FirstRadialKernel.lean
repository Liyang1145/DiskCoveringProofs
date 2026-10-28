import N11Formalization.C450RadialMajorant

/-! First actual source segment: finite rational radial packets -> continuum.
Validity and closed radial coverage remain explicit until concrete payment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialKernel
open C450RadialMajorant

def R : ℚ := 19/50
def E : ℚ := 1/250
def A : ℚ := 641363/250000
def B : ℚ := 338103/500000
def M : ℚ := B+|(-17317:ℚ)/1000000|+|(31:ℚ)/100000|+|(-27:ℚ)/1000000|
def cap : ℚ := RatInterval.piLo*(A+B)/10
def zQ (r : ℚ) : ℚ := (1+r^2-R^2)/(2*r)
def betaCos (r : ℚ) : ℚ := (r-E)/(2*R)
def model (r : ℝ) : ℝ := (A:ℝ)*Real.arccos (zOf r)+(M:ℝ)*betaUpper r (E:ℝ)

structure Packet where
  lo : ℚ
  hi : ℚ
  qt : ℚ
  qb : ℚ

structure Valid (p : Packet) : Prop where
  lower : 31/50 ≤ p.lo
  ordered : p.lo ≤ p.hi
  upper : p.hi ≤ 191/250
  turn : p.hi^2 ≤ 1-R^2
  qt_nonneg : 0 ≤ p.qt
  qb_nonneg : 0 ≤ p.qb
  t_cos : cosHiNLag p.qt ≤ zQ p.hi
  beta_cos : cosHiNLag p.qb ≤ betaCos p.lo
  beta_domain : -1 ≤ betaCos p.lo ∧ betaCos p.lo ≤ 1
  numeric : A*p.qt+M*p.qb < cap

theorem zQ_cast (r : ℚ) : (zQ r:ℝ) = zOf (r:ℝ) := by
  simp [zQ,zOf,R]
theorem betaCos_cast (r : ℚ) :
    (betaCos r:ℝ) = ((r:ℝ)-(E:ℝ))/(2*(19/50:ℝ)) := by
  simp [betaCos,R]

theorem z_mem {r : ℝ} (h0 : (31:ℝ)/50 ≤ r) (h1 : r ≤ (69:ℝ)/50) :
    zOf r ∈ Set.Icc (-1) 1 := by
  have hp : 0 < r := by linarith
  refine ⟨?_,?_⟩
  · linarith [z_ge_global hp]
  · unfold zOf
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*r)]
    have hm := mul_nonneg (by linarith : 0 ≤ r-31/50)
      (by linarith : 0 ≤ 69/50-r)
    nlinarith

theorem packet_bound (p : Packet) (hp : Valid p) (r : ℝ)
    (hr : r ∈ Set.Icc (p.lo:ℝ) (p.hi:ℝ)) : model r < (cap:ℝ) := by
  have hlo : (31:ℝ)/50 ≤ (p.lo:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.lower
    norm_num at hh
    exact hh
  have hhi : (p.hi:ℝ) ≤ (191:ℝ)/250 := by
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
  have hz := z_mem (hlo.trans hr.1) (by linarith [hr.2])
  have hcost : Real.cos (Real.arccos (zOf r)) = zOf r := Real.cos_arccos hz.1 hz.2
  have htc : ((cosHiNLag p.qt:ℚ):ℝ) ≤ zOf (p.hi:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.t_cos
    rwa [zQ_cast] at hh
  have ht : Real.arccos (zOf r) ≤ (p.qt:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hp.qt_nonneg)
      (Real.arccos_le_pi _) hcost (htc.trans hmono)
  have hbetaDomain : (betaCos p.lo:ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · exact_mod_cast hp.beta_domain.1
    · exact_mod_cast hp.beta_domain.2
  have hcosb : Real.cos (Real.arccos (betaCos p.lo:ℝ)) = (betaCos p.lo:ℝ) :=
    Real.cos_arccos hbetaDomain.1 hbetaDomain.2
  have hbc : ((cosHiNLag p.qb:ℚ):ℝ) ≤ (betaCos p.lo:ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr hp.beta_cos
  have hb0 : Real.arccos (betaCos p.lo:ℝ) ≤ (p.qb:ℝ) :=
    le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hp.qb_nonneg)
      (Real.arccos_le_pi _) hcosb hbc
  have hbm : betaUpper r (E:ℝ) ≤ Real.arccos (betaCos p.lo:ℝ) := by
    unfold betaUpper
    rw [betaCos_cast]
    apply Real.arccos_le_arccos
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sub_le_sub_right hr.1 _
  have hA : (0:ℝ) ≤ (A:ℝ) := by norm_num [A]
  have hM : (0:ℝ) ≤ (M:ℝ) := by norm_num [M,B]
  have hmodel : model r ≤ (A:ℝ)*(p.qt:ℝ)+(M:ℝ)*(p.qb:ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left ht hA)
      (mul_le_mul_of_nonneg_left (hbm.trans hb0) hM)
  have hnum : (A:ℝ)*(p.qt:ℝ)+(M:ℝ)*(p.qb:ℝ) < (cap:ℝ) := by exact_mod_cast hp.numeric
  exact hmodel.trans_lt hnum

theorem cap_lt_actual : (cap:ℝ) < Real.pi*((A:ℝ)+(B:ℝ))/10 := by
  have hh := mul_lt_mul_of_pos_right RatInterval.piLo_lt_pi
    (by norm_num [A,B] : (0:ℝ) < (A:ℝ)+(B:ℝ))
  have hd := div_lt_div_of_pos_right hh (by norm_num : (0:ℝ) < 10)
  simpa [cap] using hd

/-- Closed adjacent intervals, including their shared endpoint. -/
theorem interval_join {P : ℝ → Prop} {lo mid hi : ℝ}
    (hl : ∀ r ∈ Set.Icc lo mid, P r) (hr : ∀ r ∈ Set.Icc mid hi, P r) :
    ∀ r ∈ Set.Icc lo hi, P r := by
  intro r h
  by_cases hm : r ≤ mid
  · exact hl r ⟨h.1,hm⟩
  · exact hr r ⟨(lt_of_not_ge hm).le,h.2⟩
end N11Formalization.C450FirstRadialKernel
#check @N11Formalization.C450FirstRadialKernel.packet_bound
#print axioms N11Formalization.C450FirstRadialKernel.packet_bound
