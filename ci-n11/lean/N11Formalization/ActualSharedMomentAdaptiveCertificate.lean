import N11Formalization.SharedMomentFactorLocalCertificate
import N11Formalization.MetricSectorLocalCertificate
import N11Formalization.ActualSharedMomentRationalCertificate
import N11Formalization.ActualSharedMomentUnmaskedDual

/-! Actual masked shared-moment certificates from finite adaptive rational
box subdivisions. Triangle leaves may be removed only by a certified
angle-sum disjointness test. Every other leaf, including cut boundaries,
has a complete local factor upper bound. No concrete class is asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentAdaptiveCertificate

open RationalBoxSubdivision SharedMomentFactorLocalCertificate
open SharedMomentFactorGridCertificate ActualSharedMomentRationalCertificate
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualQ1CoreFans ActualRingLinkBoundaryData

def faceRoot : Cell (Fin 3) := fun _ => ⟨0,RatInterval.piHi⟩
def switchRoot : Cell (Fin 1) := fun _ => ⟨0,RatInterval.piHi/2⟩
def sectorRoot : Cell (Fin 3) := ![⟨0,RatInterval.piHi⟩,⟨0,1⟩,⟨0,1⟩]

/-- Weak rational comparisons suffice because piLo < pi < piHi is strict. -/
def FaceOutside (B : Cell (Fin 3)) : Prop :=
  RatInterval.piHi ≤ (∑ s : Fin 3, (B s).lo) ∨
    (∑ s : Fin 3, (B s).hi) ≤ RatInterval.piLo

theorem face_not_outside {B : Cell (Fin 3)} {a : Fin 3 → ℝ}
    (ha : Mem B a) (hsum : (∑ s : Fin 3, a s)=Real.pi) : ¬ FaceOutside B := by
  have hl : (∑ s : Fin 3, ((B s).lo : ℝ)) ≤ Real.pi := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun s _ => (ha s).1)
  have hh : Real.pi ≤ (∑ s : Fin 3, ((B s).hi : ℝ)) := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun s _ => (ha s).2)
  intro hout
  rcases hout with hlo | hhi
  · have h : (RatInterval.piHi : ℝ) ≤ (∑ s : Fin 3, ((B s).lo : ℝ)) := by
      exact_mod_cast hlo
    exact (not_le_of_gt RatInterval.pi_lt_piHi) (h.trans hl)
  · have h : (∑ s : Fin 3, ((B s).hi : ℝ)) ≤ (RatInterval.piLo : ℝ) := by
      exact_mod_cast hhi
    exact (not_le_of_gt RatInterval.piLo_lt_pi) (hh.trans h)

def FaceLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 3)) : Prop :=
  FaceOutside B ∨ faceLocalUpperQ p q b B ≤ M

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
      rcases hleaf with hout | hupper
      · exact (face_not_outside ha hsum hout).elim
      · exact face_upper_of_local_certificate p q b B M hupper a ha y hy)
  intro a ha hsum y hy
  have hroot : Mem faceRoot a := by
    intro s
    simpa only [faceRoot,RatInterval.mem_iff,Rat.cast_zero] using
      (show (0 : ℝ) ≤ a s ∧ a s ≤ (RatInterval.piHi : ℝ) from
        ⟨(ha s).1,(ha s).2.trans RatInterval.pi_lt_piHi.le⟩)
  exact H a hroot hsum y hy

def SwitchLeaf (p q b d2 d1 M : ℚ) (B : Cell (Fin 1)) : Prop :=
  switchLocalUpperQ p q b d2 d1 B ≤ M

theorem switch_upper_of_tree (p q b d2 d1 M : ℚ)
    (T : RationalBoxSubdivision.Certificate (SwitchLeaf p q b d2 d1 M) switchRoot) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  have H := certificate_sound T
    (fun x => ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 (x 0) y ≤ (M : ℝ)) (by
      intro B hleaf x hx y hy
      exact switch_upper_of_local_certificate p q b d2 d1 B M hleaf (x 0) (hx 0) y hy)
  intro t ht y hy
  have hroot : Mem switchRoot (fun _ => t) := by
    intro i
    simpa only [switchRoot,RatInterval.mem_iff,Rat.cast_zero] using
      (show (0 : ℝ) ≤ t ∧ t ≤ ((RatInterval.piHi/2 : ℚ) : ℝ) from
        ⟨ht.1,ht.2.trans RatInterval.pi_div_two_lt_hi.le⟩)
  exact H (fun _ => t) hroot y hy

def SectorLeaf (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) : Prop :=
  Nonempty (MetricSectorLocalCertificate.Certificate C mu dL dR bL bR M B)

theorem sector_upper_of_tree (C mu dL dR bL bR M : ℚ)
    (T : RationalBoxSubdivision.Certificate (SectorLeaf C mu dL dR bL bR M) sectorRoot) :
    ∀ a ∈ Set.Icc (0 : ℝ) Real.pi, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ w ∈ Set.Icc (0 : ℝ) 1,
      MetricSectorBoxCertificate.sectorObjective C mu dL dR bL bR a u w ≤ (M : ℝ) := by
  intro a ha u hu w hw
  have hx : Mem sectorRoot ![a,u,w] := by
    intro j
    fin_cases j
    · simpa [sectorRoot,RatInterval.mem_iff] using
        (show (0 : ℝ) ≤ a ∧ a ≤ (RatInterval.piHi : ℝ) from
          ⟨ha.1,ha.2.trans RatInterval.pi_lt_piHi.le⟩)
    · simpa [sectorRoot,RatInterval.mem_iff] using hu
    · simpa [sectorRoot,RatInterval.mem_iff] using hw
  exact MetricSectorLocalCertificate.subdivision_upper_of_rational_certificate T ![a,u,w] hx

def totalUpperQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (eta : ℚ)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℚ :=
  constantUpperQ D kap eta+(∑ A : R.Index, faceMax A)+
    (∑ k : Fin 9, switchMax k)+(∑ k : Fin 9, sectorMax k)

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
    (hstrict : totalUpperQ D kap eta faceMax switchMax sectorMax < RatInterval.piLo) : False := by
  classical
  have htotal : (totalUpperQ D kap eta faceMax switchMax sectorMax : ℝ) < Real.pi :=
    (show (totalUpperQ D kap eta faceMax switchMax sectorMax : ℝ) < (RatInterval.piLo : ℝ)
      by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hc := dualConstant_upper D kap eta heta
  have hsum : ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta+
      (∑ A : R.Index, (faceMax A : ℝ))+(∑ k : Fin 9, (switchMax k : ℝ))+
        (∑ k : Fin 9, (sectorMax k : ℝ)) < Real.pi := by
    unfold totalUpperQ at htotal
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

def unmaskedTotalUpperQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℚ :=
  totalUpperQ D kap 0 faceMax switchMax sectorMax

theorem unmaskedConstant_upper {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) :
    ActualSharedMomentUnmaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) ≤
      (constantUpperQ D kap 0 : ℝ) := by
  rw [ActualSharedMomentUnmaskedDual.dualConstant_eq_masked_zero]
  simpa only [Rat.cast_zero] using dualConstant_upper D kap 0 (by norm_num)

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
    unfold unmaskedTotalUpperQ totalUpperQ at htotal
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

end N11Formalization.ActualSharedMomentAdaptiveCertificate
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.unmaskedConstant_upper
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.face_not_outside
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.face_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.switch_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.sector_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_adaptive_rational_certificate
