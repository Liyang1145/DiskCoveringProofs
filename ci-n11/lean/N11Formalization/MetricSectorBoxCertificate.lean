import N11Formalization.MetricSectorCompactRegularity
import N11Formalization.CompactBoxGridCertificate

/-! Signed sector objectives on the entire closed three-dimensional box.
The factor and width bounds include the coincident-endpoint locus. The
anisotropic certificate requires only finite node inequalities, and the
actual sector geometry enters through proved angle and endpoint bounds. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorBoxCertificate

open MetricSectorCompactRegularity CompactBoxGridCertificate
open DSHTopologyInterior ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualMetricAngleAtoms ActualSectorMetricDomain ActualSharedFactorArea
open ActualOwnershipSwitchWidths

def sectorObjective (C mu dL dR bL bR a u v : ℝ) : ℝ :=
  sectorFactor a u v+C*sectorWidth a u v-mu*a-dL*u^2-dR*v^2-bL*u-bR*v

def angleLipschitz (C mu : ℝ) : ℝ := 1+(19/25 : ℝ)*|C|+|mu|
def radiusLipschitz (C d b : ℝ) : ℝ := 1+(19/25 : ℝ)*|C|+2*|d|+|b|

theorem squared_radius_difference {u w : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |u^2-w^2| ≤ 2*|u-w| := by
  rw [show u^2-w^2=(u-w)*(u+w) by ring,abs_mul,
    abs_of_nonneg (add_nonneg hu.1 hw.1)]
  have hs : u+w ≤ 2 := by linarith [hu.2,hw.2]
  nlinarith only [mul_le_mul_of_nonneg_left hs (abs_nonneg (u-w))]

theorem radial_penalty_difference (d b : ℝ) {u w : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |d*(u^2-w^2)+b*(u-w)| ≤ (2*|d|+|b|)*|u-w| := by
  have ht := abs_add_le (d*(u^2-w^2)) (b*(u-w))
  simp only [abs_mul] at ht
  have hs := mul_le_mul_of_nonneg_left (squared_radius_difference hu hw) (abs_nonneg d)
  nlinarith only [ht,hs]

theorem sectorObjective_difference (C mu dL dR bL bR a a' : ℝ)
    {u u' v v' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hu' : u' ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hv' : v' ∈ Set.Icc (0 : ℝ) 1) :
    |sectorObjective C mu dL dR bL bR a u v-
      sectorObjective C mu dL dR bL bR a' u' v'| ≤
      angleLipschitz C mu*|a-a'|+radiusLipschitz C dL bL*|u-u'|+
        radiusLipschitz C dR bR*|v-v'| := by
  have hf := sectorFactor_difference (a := a) (b := a') hu hu' hv hv'
  have hw := mul_le_mul_of_nonneg_left
    (sectorWidth_difference (a := a) (b := a') hu hu' hv hv') (abs_nonneg C)
  have hl := radial_penalty_difference dL bL hu hu'
  have hr := radial_penalty_difference dR bR hv hv'
  let A := sectorFactor a u v-sectorFactor a' u' v'
  let B := C*(sectorWidth a u v-sectorWidth a' u' v')
  let D := -mu*(a-a')
  let E := -(dL*(u^2-u'^2)+bL*(u-u'))
  let F := -(dR*(v^2-v'^2)+bR*(v-v'))
  have h1 := abs_add_le A B
  have h2 := abs_add_le (A+B) D
  have h3 := abs_add_le (A+B+D) E
  have h4 := abs_add_le (A+B+D+E) F
  have he : sectorObjective C mu dL dR bL bR a u v-
      sectorObjective C mu dL dR bL bR a' u' v'=A+B+D+E+F := by
    dsimp [A,B,D,E,F,sectorObjective]
    ring
  dsimp [A,B,D,E,F] at h1 h2 h3 h4
  simp only [abs_mul,abs_neg] at h1 h2 h3 h4
  rw [he]
  dsimp [A,B,D,E,F,angleLipschitz,radiusLipschitz]
  nlinarith only [h1,h2,h3,h4,hf,hw,hl,hr]

def sectorBoxSides (U : ℝ) : Fin 3 → ℝ := ![U,1,1]
def sectorLipschitz (C mu dL dR bL bR : ℝ) : Fin 3 → ℝ :=
  ![angleLipschitz C mu,radiusLipschitz C dL bL,radiusLipschitz C dR bR]
def sectorBoxObjective (C mu dL dR bL bR : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  sectorObjective C mu dL dR bL bR (x 0) (x 1) (x 2)
def sectorGridError (C mu dL dR bL bR U : ℝ) (N : Fin 3 → ℕ) : ℝ :=
  ∑ j : Fin 3, sectorLipschitz C mu dL dR bL bR j*sectorBoxSides U j/(N j : ℝ)

theorem sectorGridError_eq (C mu dL dR bL bR U : ℝ) (N : Fin 3 → ℕ) :
    sectorGridError C mu dL dR bL bR U N =
      angleLipschitz C mu*U/(N 0 : ℝ)+radiusLipschitz C dL bL/(N 1 : ℝ)+
        radiusLipschitz C dR bR/(N 2 : ℝ) := by
  simp [sectorGridError,Fin.sum_univ_three,sectorBoxSides,sectorLipschitz]

theorem sectorObjective_box_difference (C mu dL dR bL bR U : ℝ)
    {x y : Fin 3 → ℝ} (hx : x ∈ Box (sectorBoxSides U))
    (hy : y ∈ Box (sectorBoxSides U)) :
    |sectorBoxObjective C mu dL dR bL bR x-sectorBoxObjective C mu dL dR bL bR y| ≤
      ∑ j : Fin 3, sectorLipschitz C mu dL dR bL bR j*|x j-y j| := by
  have hu : x 1 ∈ Set.Icc (0 : ℝ) 1 := by simpa [sectorBoxSides] using hx 1
  have hu' : y 1 ∈ Set.Icc (0 : ℝ) 1 := by simpa [sectorBoxSides] using hy 1
  have hv : x 2 ∈ Set.Icc (0 : ℝ) 1 := by simpa [sectorBoxSides] using hx 2
  have hv' : y 2 ∈ Set.Icc (0 : ℝ) 1 := by simpa [sectorBoxSides] using hy 2
  simpa [sectorBoxObjective,sectorLipschitz,Fin.sum_univ_three] using
    sectorObjective_difference C mu dL dR bL bR (x 0) (y 0) hu hu' hv hv'

theorem sectorObjective_box_upper_of_grid (C mu dL dR bL bR : ℝ)
    {U M : ℝ} (hU : 0 ≤ U) (N : Fin 3 → ℕ) (hN : ∀ j, 0 < N j)
    (hnodes : ∀ k : ∀ j, Fin (N j+1),
      sectorBoxObjective C mu dL dR bL bR (gridVector (sectorBoxSides U) N k) ≤ M) :
    ∀ x ∈ Box (sectorBoxSides U), sectorBoxObjective C mu dL dR bL bR x ≤
      M+sectorGridError C mu dL dR bL bR U N := by
  have hsides : ∀ j, 0 ≤ sectorBoxSides U j := by
    intro j
    fin_cases j <;> simp [sectorBoxSides,hU]
  have hL : ∀ j, 0 ≤ sectorLipschitz C mu dL dR bL bR j := by
    intro j
    fin_cases j <;> simp [sectorLipschitz,angleLipschitz,radiusLipschitz] <;> positivity
  exact weighted_box_upper_of_grid (sectorBoxSides U) (sectorLipschitz C mu dL dR bL bR)
    N hsides hL hN (sectorBoxObjective C mu dL dR bL bR) M
    (fun x hx y hy => sectorObjective_box_difference C mu dL dR bL bR U hx hy) hnodes

theorem sectorObjective_closed_upper_of_grid (C mu dL dR bL bR : ℝ)
    {U M a u v : ℝ} (hU : 0 ≤ U) (N : Fin 3 → ℕ) (hN : ∀ j, 0 < N j)
    (hnodes : ∀ k : ∀ j, Fin (N j+1),
      sectorBoxObjective C mu dL dR bL bR (gridVector (sectorBoxSides U) N k) ≤ M)
    (ha : a ∈ Set.Icc (0 : ℝ) U) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    sectorObjective C mu dL dR bL bR a u v ≤ M+sectorGridError C mu dL dR bL bR U N := by
  have hx : (![a,u,v] : Fin 3 → ℝ) ∈ Box (sectorBoxSides U) := by
    intro j
    fin_cases j
    · simpa [sectorBoxSides] using ha
    · simpa [sectorBoxSides] using hu
    · simpa [sectorBoxSides] using hv
  simpa [sectorBoxObjective] using
    sectorObjective_box_upper_of_grid C mu dL dR bL bR hU N hN hnodes ![a,u,v] hx

theorem actual_sector_box_upper_of_grid {c : Fin 11 → Point} {r U M : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9)
    (hU : Real.pi ≤ U) (C mu dL dR bL bR : ℝ)
    (N : Fin 3 → ℕ) (hN : ∀ j, 0 < N j)
    (hnodes : ∀ k : ∀ j, Fin (N j+1),
      sectorBoxObjective C mu dL dR bL bR (gridVector (sectorBoxSides U) N k) ≤ M) :
    sectorArea v i+C*switchGap v i-mu*sectorAngle v i-
      dL*(leftNormalized v i)^2-dR*(rightNormalized v i)^2-
        bL*leftNormalized v i-bR*rightNormalized v i ≤
      M+sectorGridError C mu dL dR bL bR U N := by
  have hd := actual_normalized_endpoint_domain h hr v i
  have ha := actual_sector_angle_bounds v i
  have hf := actual_sector_compact_factors h hr v i
  rw [hf.1,hf.2]
  exact sectorObjective_closed_upper_of_grid C mu dL dR bL bR
    (Real.pi_pos.le.trans hU) N hN hnodes ⟨ha.1,ha.2.trans hU⟩
    ⟨hd.1.le,hd.2.1⟩ ⟨hd.2.2.1.le,hd.2.2.2⟩

end N11Formalization.MetricSectorBoxCertificate
#check @N11Formalization.MetricSectorBoxCertificate.sectorObjective_difference
#check @N11Formalization.MetricSectorBoxCertificate.sectorObjective_box_upper_of_grid
#check @N11Formalization.MetricSectorBoxCertificate.actual_sector_box_upper_of_grid
#print axioms N11Formalization.MetricSectorBoxCertificate.sectorObjective_difference
#print axioms N11Formalization.MetricSectorBoxCertificate.sectorObjective_box_upper_of_grid
#print axioms N11Formalization.MetricSectorBoxCertificate.actual_sector_box_upper_of_grid
