import N11Formalization.ActualFaceCircumradiusAtoms
import N11Formalization.ActualSectorMetricDomain
import N11Formalization.ActualSwitchSineAtoms

/-! The actual three-family shared-factor area model.

Every variable is defined from the original representative, selected
nearest faces and NineTies. The source-style face/switch/sector area
identity is produced, not supplied as a certificate premise. Site-angle
equations and seven class exclusion certificates remain unpaid.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedFactorArea
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualBoundaryNineTies
open ActualMetricAngleAtoms ActualFaceCircumradiusAtoms ActualSectorMetricDomain
open ActualOwnedSectorDecomposition ActualSwitchAtomAggregate ActualBoundarySwitchMetric
open ActualBoundarySwitchAngles ActualOwnershipSwitchWidths ActualCircleSegmentAlgebra
open ActualBoundaryCyclicOrder ActualRingLinkBoundaryData FlashTiling

def faceArea {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (A : R.Index) : ℝ :=
  2*(19/50 : ℝ)^2*faceSquaredNormalized R A*Real.sin (faceAngle R A 0)*
    Real.sin (faceAngle R A 1)*Real.sin (faceAngle R A 2)

def switchSquared {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) : ℝ :=
  ((switchData h hr v i).radius/(19/50))^2

def switchArea {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) : ℝ :=
  (19/50 : ℝ)^2*switchSquared h hr v i*
    Real.sin (2*SwitchData.angle (switchData h hr v i))/2

def sectorArea {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i)/2 +
    segmentTerm (switchGap v i)

theorem actual_switch_squared_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 ≤ switchSquared h hr v i ∧ switchSquared h hr v i ≤ 1 := by
  have hb := (switchData h hr v i).normalized_radius
  unfold switchSquared
  exact ⟨sq_nonneg _,by nlinarith [hb.1,hb.2]⟩

theorem actual_squared_radius_copies {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    leftNormalized v i^2=switchSquared h hr v i ∧
      rightNormalized v i^2=switchSquared h hr v (nextRing i) := by
  have hc := actual_sector_radius_copies h hr v i
  unfold leftNormalized rightNormalized switchSquared
  rw [hc.1,hc.2]
  exact ⟨rfl,rfl⟩

theorem actual_switch_area_atom {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchArea h hr v i =
      (switchData h hr v i).chord*(switchData h hr v i).offset := by
  have hu : (19/50 : ℝ)^2*switchSquared h hr v i=(switchData h hr v i).radius^2 := by
    unfold switchSquared
    ring
  unfold switchArea
  rw [hu]
  exact SwitchData.exact_area_atom (switchData h hr v i)

theorem actual_sector_area_atom {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorArea v i =
      orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))/2 +
        segmentTerm (switchGap v i) := by
  rw [actual_sector_area_angle h hr v i]
  unfold sectorArea leftNormalized rightNormalized leftRadius rightRadius
  ring

theorem actual_sector_source_formula {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorArea v i =
      (19/50 : ℝ)^2*leftNormalized v i*rightNormalized v i*Real.sin (sectorAngle v i)/2 +
        segmentTerm (2*Real.arcsin ((19/50 : ℝ)*Real.sqrt (chordQuadratic v i)/2)) := by
  unfold sectorArea
  rw [actual_factor_width_formula h hr v i]

/-- Exact source-style area equality, with all three atom families
defined by the actual geometry. No metric/area model is assumed. -/
theorem actual_shared_factor_area {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) :
    Real.pi = (∑ A : R.Index, faceArea R A) +
      (∑ i : Fin 9, switchArea h hr v i) + ∑ i : Fin 9, sectorArea v i := by
  have hf : (∑ A : R.Index,
      orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)))/2 =
      ∑ A : R.Index, faceArea R A := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro A hA
    exact actual_face_factor_area R A
  have hs : (∑ i : Fin 9,
      (switchData h hr v i).chord*(switchData h hr v i).offset) =
      ∑ i : Fin 9, switchArea h hr v i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (actual_switch_area_atom h hr v i).symm
  have hc : (∑ i : Fin 9,
      orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i)))/2 +
      (∑ i : Fin 9, segmentTerm (switchGap v i)) = ∑ i : Fin 9, sectorArea v i := by
    rw [Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (actual_sector_area_atom h hr v i).symm
  have ht := actual_disk_atom_decomposition h hr R v
  rw [hf,hs] at ht
  linarith

end N11Formalization.ActualSharedFactorArea
#check @N11Formalization.ActualSharedFactorArea.actual_squared_radius_copies
#check @N11Formalization.ActualSharedFactorArea.actual_sector_source_formula
#check @N11Formalization.ActualSharedFactorArea.actual_shared_factor_area
#print axioms N11Formalization.ActualSharedFactorArea.actual_squared_radius_copies
#print axioms N11Formalization.ActualSharedFactorArea.actual_shared_factor_area
