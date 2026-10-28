import N11Formalization.ActualSharedMomentMaskedDual

/-! Shared first/second moments with nonnegative Delaunay multipliers,
without choosing an ear. This is the genuine no-ear path, including Q0:
the common width multiplier remains signed, and arbitrary nonnegative
Delaunay multipliers are retained. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentUnmaskedDual
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualSharedMomentData ActualSharedMomentDual
open ActualEdgeMetricModel ActualEdgeFlagSums ActualRefinementDoubleCounting
open ActualMetricAngleAtoms ActualRingLinkBoundaryData
open ActualBoundarySwitchAngles ActualSwitchAtomAggregate
open ActualSectorMetricDomain ActualOwnershipSwitchWidths
open ActualFaceCircumradiusAtoms

def dualConstant {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (kap : Finset (Fin 11) → ℝ) : ℝ :=
  stationConstant D.mu + Real.pi * (∑ e ∈ edges R, kap e) - 2*Real.pi*D.width

theorem dualConstant_eq_masked_zero {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (D : Coefficients R) (kap : Finset (Fin 11) → ℝ) :
    dualConstant D kap = ActualSharedMomentMaskedDual.dualConstant D kap 0 := by
  simp only [dualConstant,ActualSharedMomentMaskedDual.dualConstant,mul_zero,sub_zero]

theorem actual_unmasked_moment_area_bound {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℝ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e) :
    Real.pi ≤ dualConstant D kap +
      (∑ A : R.Index, ActualSharedMomentMaskedDual.faceFactor D kap A
        (faceAngle R A) (faceNormalized R A)) +
      (∑ k : Fin 9, ActualSharedMomentMaskedDual.switchFactor D kap k
        (SwitchData.angle (switchData h hr v k)) (switchNormalized h hr v k)) +
      (∑ k : Fin 9, sectorFactor D k (sectorAngle v k)
        (leftNormalized v k) (rightNormalized v k)) := by
  classical
  have hb := actual_moment_factor_sum h hr R v D hm
  have hk := ActualSharedMomentMaskedDual.actual_delaunay_multiplier_balance h hr R v kap
  have hn : 0 ≤ ∑ e ∈ edges R, kap e * edgeAngle h hr R v e :=
    Finset.sum_nonneg (fun e he => mul_nonneg (hkap e he)
      (actual_edge_angle_area_domain h hr R v he).1)
  unfold dualConstant ActualSharedMomentMaskedDual.faceFactor
    ActualSharedMomentMaskedDual.switchFactor
  simp only [Finset.sum_sub_distrib]
  linarith only [hb,hk,hn]

theorem exclude_of_full_domain_unmasked_moment_certificate
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℝ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e)
    (faceMax : R.Index → ℝ) (switchMax sectorMax : Fin 9 → ℝ)
    (hf : ∀ (A : R.Index) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ActualSharedMomentMaskedDual.faceFactor D kap A a y ≤ faceMax A)
    (hs : ∀ (k : Fin 9) (b : ℝ), b ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ActualSharedMomentMaskedDual.switchFactor D kap k b y ≤ switchMax k)
    (ht : ∀ (k : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
        sectorFactor D k a u w ≤ sectorMax k)
    (hstrict : dualConstant D kap + (∑ A : R.Index, faceMax A) +
      (∑ k : Fin 9, switchMax k) + (∑ k : Fin 9, sectorMax k) < Real.pi) : False := by
  have hsum := actual_unmasked_moment_area_bound h hr R v D hm kap hkap
  have hface := Finset.sum_le_sum (s := Finset.univ) (fun A _ => hf A (faceAngle R A)
    (fun s => ⟨(actual_face_angle_strict R A s).1.le,(actual_face_angle_strict R A s).2.le⟩)
    (actual_face_angle_sum h R A) (faceNormalized R A)
    ⟨(actual_face_normalized_domain h hr R A).1.le,
      (actual_face_normalized_domain h hr R A).2⟩)
  have hswitch := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hs k
    (SwitchData.angle (switchData h hr v k))
    ⟨(SwitchData.angle_bounds (switchData h hr v k)).1.le,
      (SwitchData.angle_bounds (switchData h hr v k)).2.le⟩
    (switchNormalized h hr v k)
    ⟨(actual_switch_normalized_domain h hr v k).1.le,
      (actual_switch_normalized_domain h hr v k).2⟩)
  have hsector := Finset.sum_le_sum (s := Finset.univ) (fun k _ => ht k (sectorAngle v k)
    (actual_sector_angle_bounds v k) (leftNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).1.le,
      (actual_normalized_endpoint_domain h hr v k).2.1⟩ (rightNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).2.2.1.le,
      (actual_normalized_endpoint_domain h hr v k).2.2.2⟩)
  linarith only [hsum,hface,hswitch,hsector,hstrict]

end N11Formalization.ActualSharedMomentUnmaskedDual
#check @N11Formalization.ActualSharedMomentUnmaskedDual.actual_unmasked_moment_area_bound
#check @N11Formalization.ActualSharedMomentUnmaskedDual.exclude_of_full_domain_unmasked_moment_certificate
#print axioms N11Formalization.ActualSharedMomentUnmaskedDual.dualConstant_eq_masked_zero
#print axioms N11Formalization.ActualSharedMomentUnmaskedDual.actual_unmasked_moment_area_bound
#print axioms N11Formalization.ActualSharedMomentUnmaskedDual.exclude_of_full_domain_unmasked_moment_certificate
