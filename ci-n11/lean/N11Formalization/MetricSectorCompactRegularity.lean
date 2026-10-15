import N11Formalization.MetricAreaEnvelopeRegularity

/-! Full compact skew-sector regularity, including coincident endpoints.
The chord is represented as the norm of a vector, so no positive quadratic
or differentiability hypothesis is needed at q=0. Both radii vary freely
in [0,1]. These estimates justify complete multidimensional box errors. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorCompactRegularity

open DSHTopologyInterior ActualCircleSegmentAlgebra ActualSectorAreaEnvelope
open MetricAreaEnvelopeRegularity ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualMetricAngleAtoms ActualSectorMetricDomain ActualSharedFactorArea
open ActualOwnershipSwitchWidths

def chordVector (a u v : ℝ) : Point := u • circleMap 0-v • circleMap a
def chordLength (a u v : ℝ) : ℝ := Real.sqrt (u^2+v^2-2*u*v*Real.cos a)
def sectorWidth (a u v : ℝ) : ℝ := 2*Real.arcsin ((19/50 : ℝ)*chordLength a u v/2)
def sectorFactor (a u v : ℝ) : ℝ :=
  (19/50 : ℝ)^2*u*v*Real.sin a/2+segmentTerm (sectorWidth a u v)

theorem chord_vector_sq (a u v : ℝ) :
    ‖chordVector a u v‖^2 = u^2+v^2-2*u*v*Real.cos a := by
  unfold chordVector
  rw [norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,circleMap_norm,mul_one,sq_abs,
    real_inner_smul_left,real_inner_smul_right,inner_circleMap,zero_sub,Real.cos_neg]
  ring

theorem chordLength_eq_norm (a u v : ℝ) : chordLength a u v = ‖chordVector a u v‖ := by
  unfold chordLength
  rw [← chord_vector_sq,Real.sqrt_sq (norm_nonneg _)]

theorem circle_chord_lipschitz (a b : ℝ) : ‖circleMap a-circleMap b‖ ≤ |a-b| := by
  have hn := norm_sub_sq_real (circleMap a) (circleMap b)
  rw [circleMap_norm,circleMap_norm,inner_circleMap] at hn
  have hc := Real.cos_two_mul ((a-b)/2)
  rw [show 2*((a-b)/2)=a-b by ring] at hc
  have htr := Real.sin_sq_add_cos_sq ((a-b)/2)
  have hs := Real.sin_sq_le_sq (x := (a-b)/2)
  nlinarith [norm_nonneg (circleMap a-circleMap b),abs_nonneg (a-b),sq_abs (a-b)]

theorem chordLength_box {a u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : chordLength a u v ∈ Set.Icc (0 : ℝ) 2 := by
  rw [chordLength_eq_norm]
  have hn := norm_sub_le (u • circleMap 0) (v • circleMap a)
  simp only [norm_smul,Real.norm_eq_abs,circleMap_norm,mul_one,
    abs_of_nonneg hu.1,abs_of_nonneg hv.1] at hn
  exact ⟨norm_nonneg _,by change ‖u • circleMap 0-v • circleMap a‖ ≤ 2; linarith [hu.2,hv.2]⟩

theorem chordLength_difference {a b u u' v v' : ℝ}
    (hv' : v' ∈ Set.Icc (0 : ℝ) 1) :
    |chordLength a u v-chordLength b u' v'| ≤ |u-u'|+|v-v'|+|a-b| := by
  rw [chordLength_eq_norm,chordLength_eq_norm]
  have he : chordVector a u v-chordVector b u' v' =
      (u-u') • circleMap 0-(v-v') • circleMap a-v' • (circleMap a-circleMap b) := by
    unfold chordVector
    module
  have hn := norm_sub_le ((u-u') • circleMap 0-(v-v') • circleMap a)
    (v' • (circleMap a-circleMap b))
  have hm := norm_sub_le ((u-u') • circleMap 0) ((v-v') • circleMap a)
  have hc := mul_le_mul_of_nonneg_left (circle_chord_lipschitz a b) hv'.1
  have hb := mul_le_mul_of_nonneg_right hv'.2 (abs_nonneg (a-b))
  simp only [norm_smul,Real.norm_eq_abs,circleMap_norm,mul_one,abs_of_nonneg hv'.1] at hn hm
  have hnorm := abs_norm_sub_norm_le (chordVector a u v) (chordVector b u' v')
  rw [he] at hnorm
  linarith only [hnorm,hn,hm,hc,hb]

theorem sectorWidth_difference {a b u u' v v' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hu' : u' ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hv' : v' ∈ Set.Icc (0 : ℝ) 1) :
    |sectorWidth a u v-sectorWidth b u' v'| ≤
      (19/25 : ℝ)*(|a-b|+|u-u'|+|v-v'|) := by
  have hq := chordLength_box (a := a) hu hv
  have hq' := chordLength_box (a := b) hu' hv'
  have hx : (19/50 : ℝ)*chordLength a u v/2 ∈ Set.Icc (0 : ℝ) (19/50) := by
    constructor <;> linarith [hq.1,hq.2]
  have hy : (19/50 : ℝ)*chordLength b u' v'/2 ∈ Set.Icc (0 : ℝ) (19/50) := by
    constructor <;> linarith [hq'.1,hq'.2]
  have ha := arcsin_box_difference hx hy
  have hd := chordLength_difference (a := a) (b := b) (u := u) (u' := u') (v := v) hv'
  have he : (19/50 : ℝ)*chordLength a u v/2-(19/50 : ℝ)*chordLength b u' v'/2 =
      (19/100 : ℝ)*(chordLength a u v-chordLength b u' v') := by ring
  rw [he,abs_mul] at ha
  norm_num at ha
  have hw : sectorWidth a u v-sectorWidth b u' v' =
      2*(Real.arcsin ((19/50 : ℝ)*chordLength a u v/2)-
        Real.arcsin ((19/50 : ℝ)*chordLength b u' v'/2)) := by unfold sectorWidth; ring
  rw [hw,abs_mul]
  norm_num
  nlinarith only [ha,hd]

theorem radius_product_difference {u u' v v' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv' : v' ∈ Set.Icc (0 : ℝ) 1) :
    |u*v-u'*v'| ≤ |u-u'|+|v-v'| := by
  have he : u*v-u'*v' = u*(v-v')+v'*(u-u') := by ring
  rw [he]
  have ht := abs_add_le (u*(v-v')) (v'*(u-u'))
  rw [abs_mul,abs_mul,abs_of_nonneg hu.1,abs_of_nonneg hv'.1] at ht
  have h1 := mul_le_mul_of_nonneg_right hu.2 (abs_nonneg (v-v'))
  have h2 := mul_le_mul_of_nonneg_right hv'.2 (abs_nonneg (u-u'))
  linarith only [ht,h1,h2]

theorem sectorFactor_difference {a b u u' v v' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hu' : u' ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hv' : v' ∈ Set.Icc (0 : ℝ) 1) :
    |sectorFactor a u v-sectorFactor b u' v'| ≤ |a-b|+|u-u'|+|v-v'| := by
  have hp := radius_product_difference (u' := u') (v := v) hu hv'
  have hw := sectorWidth_difference (a := a) (b := b) hu hu' hv hv'
  have hg := segmentTerm_difference (sectorWidth a u v) (sectorWidth b u' v')
  have hs := Real.abs_sin_sub_sin_le a b
  have hprod : (0 : ℝ) ≤ u*v ∧ u*v ≤ 1 :=
    ⟨mul_nonneg hu.1 hv.1,by
      have hh := mul_le_mul_of_nonneg_right hu.2 hv.1
      simp only [one_mul] at hh
      exact hh.trans hv.2⟩
  have ht : |u*v*Real.sin a-u'*v'*Real.sin b| ≤
      |u*v*(Real.sin a-Real.sin b)|+|(u*v-u'*v')*Real.sin b| := by
    have he : u*v*Real.sin a-u'*v'*Real.sin b =
        u*v*(Real.sin a-Real.sin b)+(u*v-u'*v')*Real.sin b := by ring
    rw [he]
    exact abs_add_le _ _
  simp only [abs_mul,abs_of_nonneg hu.1,abs_of_nonneg hv.1] at ht
  have h1 := mul_le_mul_of_nonneg_right hprod.2 (abs_nonneg (Real.sin a-Real.sin b))
  have h2 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one b) (abs_nonneg (u*v-u'*v'))
  have he : sectorFactor a u v-sectorFactor b u' v' =
      (19/50 : ℝ)*(19/100)*(u*v*Real.sin a-u'*v'*Real.sin b)+
        (segmentTerm (sectorWidth a u v)-segmentTerm (sectorWidth b u' v')) := by
    unfold sectorFactor
    ring
  have hh := abs_add_le ((19/50 : ℝ)*(19/100)*(u*v*Real.sin a-u'*v'*Real.sin b))
    (segmentTerm (sectorWidth a u v)-segmentTerm (sectorWidth b u' v'))
  rw [abs_mul,abs_mul] at hh
  norm_num at hh
  rw [he]
  nlinarith only [hp,hw,hg,hs,ht,h1,h2,hh,abs_nonneg (a-b),abs_nonneg (u-u'),abs_nonneg (v-v')]

theorem actual_sector_compact_factors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i=sectorWidth (sectorAngle v i) (leftNormalized v i) (rightNormalized v i) ∧
      sectorArea v i=sectorFactor (sectorAngle v i) (leftNormalized v i) (rightNormalized v i) := by
  have hw := actual_factor_width_formula h hr v i
  have hw' : switchGap v i=sectorWidth (sectorAngle v i) (leftNormalized v i) (rightNormalized v i) := hw
  exact ⟨hw',by unfold sectorArea sectorFactor; rw [hw']⟩

end N11Formalization.MetricSectorCompactRegularity
#check @N11Formalization.MetricSectorCompactRegularity.sectorWidth_difference
#check @N11Formalization.MetricSectorCompactRegularity.sectorFactor_difference
#check @N11Formalization.MetricSectorCompactRegularity.actual_sector_compact_factors
#print axioms N11Formalization.MetricSectorCompactRegularity.chordLength_difference
#print axioms N11Formalization.MetricSectorCompactRegularity.sectorWidth_difference
#print axioms N11Formalization.MetricSectorCompactRegularity.sectorFactor_difference
#print axioms N11Formalization.MetricSectorCompactRegularity.actual_sector_compact_factors
