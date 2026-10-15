import N11Formalization.C450AngularCellMajorant
import N11Formalization.C450RadialPacketKernel

/-! Actual outer/inner direction transport and outer halfwidth sine bounds.
No optimizer, selected angle or source symmetry hypothesis is supplied. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450OuterGeometry
open C450AngularMajorant

def outerT (c : Point) : ℝ := Real.arccos (zOf ‖c‖)
def outerV (c : Point) : ℝ := c 0/‖c‖

theorem inner_cq_le_outer_v {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Cq c e ≤ outerV c := by
  have hr : 0 < ‖c‖ := by linarith
  have hell := ell_pos_canonical he0 he7 hc0
  have hd : |‖c‖-‖c-(!₂[e,0]:Point)‖| ≤ e := by
    have hh := abs_norm_sub_norm_le c (c-(!₂[e,0]:Point))
    rw [sub_sub_cancel] at hh
    rwa [norm_pair_zero he0] at hh
  have hcoord := abs_coord_le_norm c
  have hp : c 0*(‖c‖-‖c-(!₂[e,0]:Point)‖) ≤ ‖c‖*e := by
    calc
      _ ≤ |c 0*(‖c‖-‖c-(!₂[e,0]:Point)‖)| := le_abs_self _
      _ = |c 0| * |‖c‖-‖c-(!₂[e,0]:Point)‖| := abs_mul _ _
      _ ≤ ‖c‖*e := mul_le_mul hcoord hd (abs_nonneg _) (norm_nonneg c)
  unfold c450Cq outerV
  rw [div_le_div_iff₀ hell hr]
  nlinarith only [hp]

theorem outer_v_bounds {c : Point} (hc0 : 1-19/50 ≤ ‖c‖) :
    -1 ≤ outerV c ∧ outerV c ≤ 1 :=
  C450SourceQuantity.direction_bounds hc0

theorem outer_t_bounds {c : Point}
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50) :
    0 ≤ outerT c ∧ outerT c ≤ 2/5 := by
  have hr : 0 < ‖c‖ := by linarith
  have hz := C450FirstRadialKernel.z_mem
    (by linarith : (31:ℝ)/50 ≤ ‖c‖) (by linarith : ‖c‖ ≤ (69:ℝ)/50)
  have hcos := Real.cos_arccos hz.1 hz.2
  have ht := t_le_global hr (Real.arccos_le_pi _) hcos
  exact ⟨Real.arccos_nonneg _,ht.trans (by norm_num [Tglobal])⟩

theorem sin97 {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 2/5) :
    (97/100:ℝ)*t ≤ Real.sin t := by
  have hb := Real.sin_bound (x := t) (by rw [abs_of_nonneg ht0]; linarith)
  rw [abs_of_nonneg ht0] at hb
  have h2 : t^2 ≤ (4/25:ℝ) := by nlinarith
  have h4 : t^4 ≤ (16/625:ℝ) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (4/25:ℝ)-t^2)
      (by positivity : 0 ≤ (4/25:ℝ)+t^2)]
  have h3 : t^3 ≤ (4/25:ℝ)*t := by
    nlinarith [mul_le_mul_of_nonneg_left h2 ht0]
  have h5 : t^5 ≤ (16/625:ℝ)*t := by
    nlinarith [mul_le_mul_of_nonneg_left h4 ht0]
  linarith [(abs_le.mp hb).1]

theorem sin2_lower {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 2/5) :
    (4/5:ℝ)*(2*t) ≤ Real.sin (2*t) :=
  sin_lower (by linarith) (by linarith)

theorem sin3_lower {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 2/5) :
    (3/4:ℝ)*(3*t) ≤ Real.sin (3*t) := by
  have h97 := sin97 ht0 ht4
  have hs0 : 0 ≤ Real.sin t := by linarith
  have hs : Real.sin t ≤ t := by
    have hh := Real.abs_sin_le_abs (x := t)
    rw [abs_of_nonneg ht0] at hh
    exact (le_abs_self _).trans hh
  have hs2 : (Real.sin t)^2 ≤ (4/25:ℝ) := by nlinarith
  have hs3 : (Real.sin t)^3 ≤ (4/25:ℝ)*t := by
    nlinarith [mul_nonneg hs0 (by linarith : 0 ≤ (4/25:ℝ)-(Real.sin t)^2)]
  rw [Real.sin_three_mul]
  nlinarith only [h97,hs3,ht0]

theorem sin_scaled_nonneg {t k : ℝ}
    (ht0 : 0 ≤ t) (ht4 : t ≤ 2/5) (hk0 : 0 ≤ k) (hk3 : k ≤ 3) :
    0 ≤ Real.sin (k*t) := by
  apply Real.sin_nonneg_of_mem_Icc
  constructor
  · exact mul_nonneg hk0 ht0
  · have hm : k*t ≤ (3:ℝ)*(2/5) :=
      mul_le_mul hk3 ht4 ht0 (by norm_num)
    linarith [Real.pi_gt_three]

theorem sin_scaled_upper {t k : ℝ} (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) :
    Real.sin (k*t) ≤ k*t := by
  have hh := Real.abs_sin_le_abs (x := k*t)
  rw [abs_of_nonneg (mul_nonneg hk0 ht0)] at hh
  exact (le_abs_self _).trans hh

def P2 (v : ℝ) : ℝ := 2*v^2-1
def P3 (v : ℝ) : ℝ := 4*v^3-3*v
theorem P2_le {q v : ℝ} (hq0 : 0 ≤ q) (hqv : q ≤ v) : P2 q ≤ P2 v := by
  unfold P2
  nlinarith
theorem P3_le {q v : ℝ} (hqHalf : (1:ℝ)/2 ≤ q) (hqv : q ≤ v) : P3 q ≤ P3 v := by
  have hvHalf : (1:ℝ)/2 ≤ v := hqHalf.trans hqv
  have hq2 : (1:ℝ)/4 ≤ q^2 := by nlinarith
  have hv2 : (1:ℝ)/4 ≤ v^2 := by nlinarith
  have hqv2 : (1:ℝ)/4 ≤ q*v := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ q-1/2) (by linarith : 0 ≤ v-1/2)]
  have hf : 0 ≤ 4*(v^2+v*q+q^2)-3 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hqv) hf
  unfold P3
  nlinarith only [hp]
end N11Formalization.C450OuterGeometry
#check @N11Formalization.C450OuterGeometry.inner_cq_le_outer_v
#check @N11Formalization.C450OuterGeometry.outer_t_bounds
#print axioms N11Formalization.C450OuterGeometry.inner_cq_le_outer_v
#print axioms N11Formalization.C450OuterGeometry.sin97
#print axioms N11Formalization.C450OuterGeometry.sin3_lower
#print axioms N11Formalization.C450OuterGeometry.P3_le
