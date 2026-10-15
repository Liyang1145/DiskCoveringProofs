import N11Formalization.ActualSharedMomentDual
import N11Formalization.ActualEarOwnedWidth
import N11Formalization.MetricSectorBoxCertificate

/-! Actual nonnegative Delaunay and selected-ear multipliers for the
signed shared-moment factor dual. Full closed factor domains remain
certificate inputs; every geometric identity and capacity is produced. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentMaskedDual
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualSharedMomentData ActualSharedMomentDual
open ActualEdgeMetricModel ActualEdgeFlagSums ActualRefinementDoubleCounting
open ActualEarOwnedWidth ActualQ1CoreFans ActualMetricAngleAtoms
open ActualRingLinkBoundaryData ActualBoundarySwitchAngles ActualSwitchAtomAggregate
open ActualSectorMetricDomain ActualOwnershipSwitchWidths
open ActualFaceCircumradiusAtoms

def faceFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (kap : Finset (Fin 11) → ℝ)
    (A : R.Index) (a : Fin 3 → ℝ) (y : ℝ) : ℝ :=
  ActualSharedMomentDual.faceFactor D A a y-∑ s : Fin 3, kap (flagEdge R A s)*a s

def switchFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (kap : Finset (Fin 11) → ℝ) (k : Fin 9) (b y : ℝ) : ℝ :=
  ActualSharedMomentDual.switchFactor D k b y-kap (cycleEdge k)*b

def sectorFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (ear : Fin 9) (eta : ℝ) (k : Fin 9) (a u v : ℝ) : ℝ :=
  ActualSharedMomentDual.sectorFactor D k a u v+
    (if k ∈ outsideGaps ear then eta else 0)*MetricSectorCompactRegularity.sectorWidth a u v

def dualConstant {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (kap : Finset (Fin 11) → ℝ) (eta : ℝ) : ℝ :=
  stationConstant D.mu+Real.pi*(∑ e ∈ edges R, kap e)-2*Real.pi*D.width-
    (2*Real.pi-2*Real.arcsin (19/25))*eta

theorem actual_delaunay_multiplier_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (kap : Finset (Fin 11) → ℝ) :
    (∑ e ∈ edges R, kap e*edgeAngle h hr R v e) =
      Real.pi*(∑ e ∈ edges R, kap e)-
      (∑ A : R.Index, ∑ s : Fin 3, kap (flagEdge R A s)*faceAngle R A s)-
      (∑ k : Fin 9, kap (cycleEdge k)*SwitchData.angle (switchData h hr v k)) := by
  classical
  have hf := sum_edge_sum R (fun A s => faceAngle R A s*kap (flagEdge R A s))
  simp_rw [edge_sum_common_factor R (faceAngle R) kap] at hf
  have hs := sum_switch_sum h hr R
    (fun k => SwitchData.angle (switchData h hr v k)*kap (cycleEdge k))
  simp_rw [switch_sum_common_factor (fun k => SwitchData.angle (switchData h hr v k)) kap] at hs
  have hf' : (∑ e ∈ edges R, kap e*edgeSum R (faceAngle R) e) =
      ∑ A : R.Index, ∑ s : Fin 3, kap (flagEdge R A s)*faceAngle R A s := by
    simpa only [mul_comm] using hf
  have hs' : (∑ e ∈ edges R, kap e*switchSum
      (fun k => SwitchData.angle (switchData h hr v k)) e) =
      ∑ k : Fin 9, kap (cycleEdge k)*SwitchData.angle (switchData h hr v k) := by
    simpa only [mul_comm] using hs
  simp only [edgeAngle,mul_sub,Finset.sum_sub_distrib]
  rw [hf',hs',← Finset.sum_mul]
  ring

theorem actual_masked_moment_area_bound {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (E : EarData R) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℝ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e)
    (eta : ℝ) (heta : 0 ≤ eta) :
    Real.pi ≤ dualConstant D kap eta+
      (∑ A : R.Index, faceFactor D kap A (faceAngle R A) (faceNormalized R A))+
      (∑ k : Fin 9, switchFactor D kap k (SwitchData.angle (switchData h hr v k))
        (switchNormalized h hr v k))+
      (∑ k : Fin 9, sectorFactor D E.center eta k (sectorAngle v k)
        (leftNormalized v k) (rightNormalized v k)) := by
  classical
  have hb := actual_moment_factor_sum h hr R v D hm
  have hk := actual_delaunay_multiplier_balance h hr R v kap
  have hn : 0 ≤ ∑ e ∈ edges R, kap e*edgeAngle h hr R v e :=
    Finset.sum_nonneg (fun e he => mul_nonneg (hkap e he)
      (actual_edge_angle_area_domain h hr R v he).1)
  have he := actual_ear_outside_width h hr v E.center (EarData.actual_common_point E)
  have ha := Real.arcsin_le_arcsin (show 2*r ≤ (19/25 : ℝ) by linarith)
  have hmask : (2*Real.pi-2*Real.arcsin (19/25))*eta ≤
      eta*(∑ k ∈ outsideGaps E.center, switchGap v k) := by
    have hh := mul_le_mul_of_nonneg_right (show 2*Real.pi-2*Real.arcsin (19/25) ≤
      ∑ k ∈ outsideGaps E.center, switchGap v k by linarith only [he,ha]) heta
    simpa only [mul_comm] using hh
  have hmasksum : (∑ k : Fin 9,
      (if k ∈ outsideGaps E.center then eta else 0)*switchGap v k) =
      eta*(∑ k ∈ outsideGaps E.center, switchGap v k) := by
    simp only [ite_mul,zero_mul,← Finset.sum_filter]
    simp [Finset.mul_sum]
  unfold faceFactor switchFactor sectorFactor dualConstant
  have hw (k : Fin 9) := (MetricSectorCompactRegularity.actual_sector_compact_factors h hr v k).1.symm
  simp_rw [hw]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hmasksum]
  linarith only [hb,hk,hn,hmask]

theorem sector_factor_upper_of_grid {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (ear : Fin 9) (eta : ℝ) (i : Fin 9)
    {U M : ℝ} (hU : Real.pi ≤ U) (N : Fin 3 → ℕ) (hN : ∀ j, 0 < N j)
    (hnodes : ∀ k : ∀ j, Fin (N j+1),
      MetricSectorBoxCertificate.sectorBoxObjective
        (D.width+if i ∈ outsideGaps ear then eta else 0) (D.mu (nextSite i))
        (D.leftSecond i) (D.rightSecond i) (D.leftFirst i) (D.rightFirst i)
        (CompactBoxGridCertificate.gridVector (MetricSectorBoxCertificate.sectorBoxSides U) N k) ≤ M) :
    ∀ a ∈ Set.Icc (0 : ℝ) Real.pi, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ w ∈ Set.Icc (0 : ℝ) 1, sectorFactor D ear eta i a u w ≤
        M+MetricSectorBoxCertificate.sectorGridError
          (D.width+if i ∈ outsideGaps ear then eta else 0) (D.mu (nextSite i))
          (D.leftSecond i) (D.rightSecond i) (D.leftFirst i) (D.rightFirst i) U N := by
  intro a ha u hu w hw
  have hh := MetricSectorBoxCertificate.sectorObjective_closed_upper_of_grid
    (D.width+if i ∈ outsideGaps ear then eta else 0) (D.mu (nextSite i))
    (D.leftSecond i) (D.rightSecond i) (D.leftFirst i) (D.rightFirst i)
    (Real.pi_pos.le.trans hU) N hN hnodes ⟨ha.1,ha.2.trans hU⟩ hu hw
  convert hh using 1
  unfold sectorFactor ActualSharedMomentDual.sectorFactor MetricSectorBoxCertificate.sectorObjective
  ring

theorem exclude_of_full_domain_masked_moment_certificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (E : EarData R) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℝ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e)
    (eta : ℝ) (heta : 0 ≤ eta)
    (faceMax : R.Index → ℝ) (switchMax sectorMax : Fin 9 → ℝ)
    (hf : ∀ (A : R.Index) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, faceFactor D kap A a y ≤ faceMax A)
    (hs : ∀ (k : Fin 9) (b : ℝ), b ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, switchFactor D kap k b y ≤ switchMax k)
    (ht : ∀ (k : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
      sectorFactor D E.center eta k a u w ≤ sectorMax k)
    (hstrict : dualConstant D kap eta+(∑ A : R.Index, faceMax A)+
      (∑ k : Fin 9, switchMax k)+(∑ k : Fin 9, sectorMax k) < Real.pi) : False := by
  have hsum := actual_masked_moment_area_bound h hr R v E D hm kap hkap eta heta
  have hface := Finset.sum_le_sum (s := Finset.univ) (fun A _ => hf A (faceAngle R A)
    (fun s => ⟨(actual_face_angle_strict R A s).1.le,(actual_face_angle_strict R A s).2.le⟩)
    (actual_face_angle_sum h R A) (faceNormalized R A)
    ⟨(actual_face_normalized_domain h hr R A).1.le,(actual_face_normalized_domain h hr R A).2⟩)
  have hswitch := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hs k
    (SwitchData.angle (switchData h hr v k))
    ⟨(SwitchData.angle_bounds (switchData h hr v k)).1.le,
      (SwitchData.angle_bounds (switchData h hr v k)).2.le⟩
    (switchNormalized h hr v k)
    ⟨(actual_switch_normalized_domain h hr v k).1.le,(actual_switch_normalized_domain h hr v k).2⟩)
  have hsector := Finset.sum_le_sum (s := Finset.univ) (fun k _ => ht k (sectorAngle v k)
    (actual_sector_angle_bounds v k) (leftNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).1.le,
      (actual_normalized_endpoint_domain h hr v k).2.1⟩ (rightNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).2.2.1.le,
      (actual_normalized_endpoint_domain h hr v k).2.2.2⟩)
  linarith only [hsum,hface,hswitch,hsector,hstrict]

end N11Formalization.ActualSharedMomentMaskedDual
#check @N11Formalization.ActualSharedMomentMaskedDual.actual_masked_moment_area_bound
#check @N11Formalization.ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate
#print axioms N11Formalization.ActualSharedMomentMaskedDual.actual_delaunay_multiplier_balance
#print axioms N11Formalization.ActualSharedMomentMaskedDual.actual_masked_moment_area_bound
#print axioms N11Formalization.ActualSharedMomentMaskedDual.sector_factor_upper_of_grid
#print axioms N11Formalization.ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate
