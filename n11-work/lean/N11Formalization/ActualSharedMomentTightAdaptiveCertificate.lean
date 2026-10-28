import N11Formalization.ActualSharedMomentAdaptiveCertificate
import N11Formalization.SharedMomentActiveRadiusCertificate

/-! Alternative certified leaf bounds for the actual adaptive dual. Each
face and switch leaf may use the original centered bound, a direct whole-cell
interval bound, or a bound scaled by certified maximizing radii. The entire
original radius domain, triangle boundary, and every subdivision cut remain.
Sector certificates and genuine geometry are supplied by the earlier kernel. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentTightAdaptiveCertificate
open RationalBoxSubdivision SharedMomentFactorLocalCertificate
open SharedMomentFactorIntervalCertificate SharedMomentActiveRadiusCertificate
open SharedMomentFactorGridCertificate ActualSharedMomentRationalCertificate
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualQ1CoreFans ActualRingLinkBoundaryData
open ActualSharedMomentAdaptiveCertificate

def FaceLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 3)) : Prop :=
  FaceOutside B ∨ faceLocalUpperQ p q b B ≤ M ∨
    faceDirectUpperQ p q b B ≤ M ∨ faceActiveUpperQ p q b B ≤ M

theorem face_upper_of_tree (p q b : Fin 3 → ℚ) (M : ℚ)
    (T : RationalBoxSubdivision.Certificate (FaceLeaf p q b M) faceRoot) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y ≤ (M : ℝ) := by
  have H := certificate_sound T
    (fun a => (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y ≤ (M : ℝ)) (by
      intro B hleaf a ha hsum y hy
      rcases hleaf with hout | hlocal | hdirect | hactive
      · exact (face_not_outside ha hsum hout).elim
      · exact face_upper_of_local_certificate p q b B M hlocal a ha y hy
      · exact face_upper_of_direct_certificate p q b B M hdirect a ha y hy
      · exact face_upper_of_active_certificate p q b B M hactive a ha y hy)
  intro a ha hsum y hy
  have hroot : Mem faceRoot a := by
    intro s
    simpa only [faceRoot,RatInterval.mem_iff,Rat.cast_zero] using
      (show (0 : ℝ) ≤ a s ∧ a s ≤ (RatInterval.piHi : ℝ) from
        ⟨(ha s).1,(ha s).2.trans RatInterval.pi_lt_piHi.le⟩)
  exact H a hroot hsum y hy

def SwitchLeaf (p q b d2 d1 M : ℚ) (B : Cell (Fin 1)) : Prop :=
  switchLocalUpperQ p q b d2 d1 B ≤ M ∨
    switchDirectUpperQ p q b d2 d1 B ≤ M ∨ switchActiveUpperQ p q b d2 d1 B ≤ M

theorem switch_upper_of_tree (p q b d2 d1 M : ℚ)
    (T : RationalBoxSubdivision.Certificate (SwitchLeaf p q b d2 d1 M) switchRoot) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  have H := certificate_sound T
    (fun x => ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 (x 0) y ≤ (M : ℝ)) (by
      intro B hleaf x hx y hy
      rcases hleaf with hlocal | hdirect | hactive
      · exact switch_upper_of_local_certificate p q b d2 d1 B M hlocal (x 0) (hx 0) y hy
      · exact switch_upper_of_direct_certificate p q b d2 d1 B M hdirect (x 0) (hx 0) y hy
      · exact switch_upper_of_active_certificate p q b d2 d1 B M hactive (x 0) (hx 0) y hy)
  intro t ht y hy
  have hroot : Mem switchRoot (fun _ => t) := by
    intro i
    simpa only [switchRoot,RatInterval.mem_iff,Rat.cast_zero] using
      (show (0 : ℝ) ≤ t ∧ t ≤ ((RatInterval.piHi/2 : ℚ) : ℝ) from
        ⟨ht.1,ht.2.trans RatInterval.pi_div_two_lt_hi.le⟩)
  exact H (fun _ => t) hroot y hy

/-- The whole domain is covered by finite closed subdivisions. Leaf upper
checks already include their local margins; no uniform global grid is used. -/
theorem exclude_of_adaptive_rational_certificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (E : EarData R) (D : CoeffQ R)
    (hm : MaskBalancedQ R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℚ) (hkap : ∀ e ∈ ActualRefinementDoubleCounting.edges R, 0 ≤ kap e)
    (eta : ℚ) (heta : 0 ≤ eta)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (hface : ∀ A : R.Index, RationalBoxSubdivision.Certificate
      (FaceLeaf (faceP D kap A) (faceQ D A) (faceB D A) (faceMax A)) faceRoot)
    (hswitch : ∀ k : Fin 9, RationalBoxSubdivision.Certificate
      (SwitchLeaf (switchP D kap k) (switchQ D k) (switchB D k)
        (switchD2 D k) (switchD1 D k) (switchMax k)) switchRoot)
    (hsector : ∀ k : Fin 9, RationalBoxSubdivision.Certificate
      (SectorLeaf (sectorC D E.center eta k) (D.mu (nextSite k))
        (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) (sectorMax k)) sectorRoot)
    (hstrict : ActualSharedMomentAdaptiveCertificate.totalUpperQ D kap eta faceMax switchMax sectorMax < RatInterval.piLo) : False := by
  classical
  have htotal : (ActualSharedMomentAdaptiveCertificate.totalUpperQ D kap eta faceMax switchMax sectorMax : ℝ) < Real.pi :=
    (show (ActualSharedMomentAdaptiveCertificate.totalUpperQ D kap eta faceMax switchMax sectorMax : ℝ) < (RatInterval.piLo : ℝ)
      by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hc := dualConstant_upper D kap eta heta
  have hsum : ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta+
      (∑ A : R.Index, (faceMax A : ℝ))+(∑ k : Fin 9, (switchMax k : ℝ))+
        (∑ k : Fin 9, (sectorMax k : ℝ)) < Real.pi := by
    unfold ActualSharedMomentAdaptiveCertificate.totalUpperQ at htotal
    simp only [Rat.cast_add,Rat.cast_sum] at htotal
    linarith only [hc,htotal]
  apply ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate
    h hr R v E D.toReal (maskBalanced_of_rational D hm) (fun e => (kap e : ℝ))
    (fun e he => by exact_mod_cast hkap e he) (eta : ℝ) (by exact_mod_cast heta)
    (fun A => (faceMax A : ℝ)) (fun k => (switchMax k : ℝ)) (fun k => (sectorMax k : ℝ))
    ?_ ?_ ?_ hsum
  · intro A a ha hsum y hy
    rw [face_factor_eq_objective]
    exact face_upper_of_tree (faceP D kap A) (faceQ D A) (faceB D A) (faceMax A)
      (hface A) a ha hsum y hy
  · intro k t ht y hy
    rw [switch_factor_eq_objective]
    exact switch_upper_of_tree (switchP D kap k) (switchQ D k) (switchB D k)
      (switchD2 D k) (switchD1 D k) (switchMax k) (hswitch k) t ht y hy
  · intro k a ha u hu w hw
    have he : ActualSharedMomentMaskedDual.sectorFactor D.toReal E.center (eta : ℝ) k a u w =
        MetricSectorBoxCertificate.sectorObjective (sectorC D E.center eta k)
          (D.mu (nextSite k)) (D.leftSecond k) (D.rightSecond k)
          (D.leftFirst k) (D.rightFirst k) a u w := by
      rw [sectorC_cast]
      unfold ActualSharedMomentMaskedDual.sectorFactor ActualSharedMomentDual.sectorFactor
        MetricSectorBoxCertificate.sectorObjective CoeffQ.toReal
      ring
    rw [he]
    exact sector_upper_of_tree (sectorC D E.center eta k) (D.mu (nextSite k))
      (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) (sectorMax k)
      (hsector k) a ha u hu w hw

/-- No EarData premise: Q0 and any actual refinement can use the common
width and Delaunay multipliers with the same finite tree kernel. -/
theorem exclude_of_unmasked_adaptive_rational_certificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : CoeffQ R)
    (hm : MaskBalancedQ R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℚ) (hkap : ∀ e ∈ ActualRefinementDoubleCounting.edges R, 0 ≤ kap e)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (hface : ∀ A : R.Index, RationalBoxSubdivision.Certificate
      (FaceLeaf (faceP D kap A) (faceQ D A) (faceB D A) (faceMax A)) faceRoot)
    (hswitch : ∀ k : Fin 9, RationalBoxSubdivision.Certificate
      (SwitchLeaf (switchP D kap k) (switchQ D k) (switchB D k)
        (switchD2 D k) (switchD1 D k) (switchMax k)) switchRoot)
    (hsector : ∀ k : Fin 9, RationalBoxSubdivision.Certificate
      (SectorLeaf D.width (D.mu (nextSite k))
        (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) (sectorMax k)) sectorRoot)
    (hstrict : unmaskedTotalUpperQ D kap faceMax switchMax sectorMax < RatInterval.piLo) : False := by
  classical
  have htotal : (unmaskedTotalUpperQ D kap faceMax switchMax sectorMax : ℝ) < Real.pi :=
    (show (unmaskedTotalUpperQ D kap faceMax switchMax sectorMax : ℝ) < (RatInterval.piLo : ℝ)
      by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hc := unmaskedConstant_upper D kap
  have hsum : ActualSharedMomentUnmaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ))+
      (∑ A : R.Index, (faceMax A : ℝ))+(∑ k : Fin 9, (switchMax k : ℝ))+
        (∑ k : Fin 9, (sectorMax k : ℝ)) < Real.pi := by
    unfold unmaskedTotalUpperQ ActualSharedMomentAdaptiveCertificate.totalUpperQ at htotal
    simp only [Rat.cast_add,Rat.cast_sum] at htotal
    linarith only [hc,htotal]
  apply ActualSharedMomentUnmaskedDual.exclude_of_full_domain_unmasked_moment_certificate
    h hr R v D.toReal (maskBalanced_of_rational D hm) (fun e => (kap e : ℝ))
    (fun e he => by exact_mod_cast hkap e he)
    (fun A => (faceMax A : ℝ)) (fun k => (switchMax k : ℝ)) (fun k => (sectorMax k : ℝ))
    ?_ ?_ ?_ hsum
  · intro A a ha hsum y hy
    rw [face_factor_eq_objective]
    exact face_upper_of_tree (faceP D kap A) (faceQ D A) (faceB D A) (faceMax A)
      (hface A) a ha hsum y hy
  · intro k t ht y hy
    rw [switch_factor_eq_objective]
    exact switch_upper_of_tree (switchP D kap k) (switchQ D k) (switchB D k)
      (switchD2 D k) (switchD1 D k) (switchMax k) (hswitch k) t ht y hy
  · intro k a ha u hu w hw
    have he : ActualSharedMomentDual.sectorFactor D.toReal k a u w =
        MetricSectorBoxCertificate.sectorObjective D.width
          (D.mu (nextSite k)) (D.leftSecond k) (D.rightSecond k)
          (D.leftFirst k) (D.rightFirst k) a u w := by
      unfold ActualSharedMomentDual.sectorFactor MetricSectorBoxCertificate.sectorObjective CoeffQ.toReal
      ring
    rw [he]
    exact sector_upper_of_tree D.width (D.mu (nextSite k))
      (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) (sectorMax k)
      (hsector k) a ha u hu w hw

end N11Formalization.ActualSharedMomentTightAdaptiveCertificate
#check @N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#check @N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.face_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.switch_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
