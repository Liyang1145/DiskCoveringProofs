import N11Formalization.ActualCanonicalMomentTransport
import N11Formalization.SharedMomentFactorPermutation
import N11Formalization.ActualSharedMomentSharpConstant

/-! Canonical full-domain factor bounds consume only canonical rational
coefficient tables. Actual face orders, selected edges, station weights,
cyclic copies and the selected ear are supplied by the proved coordinate
builders. Finite factor certificates produce the intermediate bounds below. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCanonicalSharedMomentConsumer

open ActualCanonicalFaceCoordinates ActualCanonicalMomentTransport
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualOrderedMetricGraphs ActualCanonicalSitePermutation
open ActualSharedMomentRationalCertificate ActualSharedMomentSharpConstant
open SharedMomentFactorGridCertificate SharedMomentFactorPermutation
open ActualBoundaryNineTies ActualQ1CoreFans ActualQ0OrderedTwoFans
open ActualQ1OrderedCoreFans ActualEdgeFlagSums ActualRefinementDoubleCounting
open ActualRefinementEarCount
open ActualSharedMomentData ActualMetricAngleAtoms ActualFaceCircumradiusAtoms
open ActualBoundarySwitchAngles ActualSwitchAtomAggregate ActualSectorMetricDomain
open ActualRingLinkBoundaryData ActualOwnershipSwitchWidths
open MetricAreaRationalCertificate

def sharpAlpha : ℚ := 863314/1000000

theorem sharpAlpha_bracket : EarAsinBracket sharpAlpha := ear_asin_863314

structure CanonicalFactorBounds {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ)
    (ear : Fin 9) (eta : ℚ) (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : Prop where
  face : ∀ (f : F) (a : Fin 3 → ℝ),
    (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (canonicalFaceP D kap f s : ℝ))
        (fun s => (canonicalFaceQ D f s : ℝ)) (fun s => (canonicalFaceB D f s : ℝ)) a y ≤ faceMax f
  switch : ∀ (i : Fin 9) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective (canonicalSwitchP D kap i) (canonicalSwitchQ D i) (canonicalSwitchB D i)
        (canonicalSwitchD2 D i) (canonicalSwitchD1 D i) t y ≤ switchMax i
  sector : ∀ (i : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      MetricSectorBoxCertificate.sectorObjective (canonicalSectorC D ear eta i)
        (D.mu (nextSite i)) (D.leftSecond i) (D.rightSecond i)
        (D.leftFirst i) (D.rightFirst i) a u v ≤ sectorMax i

def canonicalSharpConstantUpperQ {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) : ℚ :=
  piProductUpper (canonicalConstantCoeffQ D kap eta)+2*alpha*eta

def canonicalTotalUpperQ {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℚ :=
  canonicalSharpConstantUpperQ D kap eta alpha+(∑ f : F, faceMax f)+
    (∑ i : Fin 9, switchMax i)+(∑ i : Fin 9, sectorMax i)

structure CanonicalCertificate {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta alpha : ℚ) where
  faceMax : F → ℚ
  switchMax : Fin 9 → ℚ
  sectorMax : Fin 9 → ℚ
  balance : CanonicalMaskBalancedQ D
  edge_nonnegative : ∀ e ∈ faceEdges F, 0 ≤ kap e
  eta_nonnegative : 0 ≤ eta
  bracket : EarAsinBracket alpha
  bounds : CanonicalFactorBounds D kap ear eta faceMax switchMax sectorMax
  strict : canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax < RatInterval.piLo

theorem sharpConstantUpperQ_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) :
    sharpConstantUpperQ (pullback C D) (pullbackKap cut b kap) eta alpha=
      canonicalSharpConstantUpperQ D kap eta alpha := by
  unfold sharpConstantUpperQ canonicalSharpConstantUpperQ
  rw [constantCoeffQ_pullback]

theorem face_factor_upper_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (H : CanonicalFactorBounds D kap ear eta faceMax switchMax sectorMax) :
    ∀ (A : R.Index) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ActualSharedMomentMaskedDual.faceFactor (pullback C D).toReal
        (fun e => (pullbackKap cut b kap e : ℝ)) A a y ≤ faceMax (C.faceEquiv A) := by
  intro A a ha hsum y hy
  rw [face_factor_eq_objective]
  simp only [faceP_pullback,faceQ_pullback,faceB_pullback]
  exact face_upper_of_permuted_coefficients _ _ _ _ (C.slotPerm A)
    (H.face (C.faceEquiv A)) a ha hsum y hy

theorem switch_factor_upper_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (H : CanonicalFactorBounds D kap ear eta faceMax switchMax sectorMax) :
    ∀ (i : Fin 9) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ActualSharedMomentMaskedDual.switchFactor (pullback C D).toReal
        (fun e => (pullbackKap cut b kap e : ℝ)) i t y ≤ switchMax (i-cut) := by
  intro i t ht y hy
  rw [switch_factor_eq_objective]
  simp only [switchP_pullback,switchQ_pullback,switchB_pullback,switchD2_pullback,switchD1_pullback]
  exact H.switch (i-cut) t ht y hy

theorem sector_factor_upper_pullback {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (H : CanonicalFactorBounds D kap (ear-cut) eta faceMax switchMax sectorMax) :
    ∀ (i : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ActualSharedMomentMaskedDual.sectorFactor (pullback C D).toReal ear eta i a u v ≤
        sectorMax (i-cut) := by
  intro i a ha u hu v hv
  have he : ActualSharedMomentMaskedDual.sectorFactor (pullback C D).toReal ear eta i a u v=
      MetricSectorBoxCertificate.sectorObjective (sectorC (pullback C D) ear eta i)
        ((pullback C D).mu (nextSite i)) ((pullback C D).leftSecond i)
        ((pullback C D).rightSecond i) ((pullback C D).leftFirst i)
        ((pullback C D).rightFirst i) a u v := by
    rw [sectorC_cast]
    simp only [ActualSharedMomentMaskedDual.sectorFactor,ActualSharedMomentDual.sectorFactor,
      MetricSectorBoxCertificate.sectorObjective,CoeffQ.toReal]
    ring
  rw [he,sectorC_pullback,sectorOwner_pullback]
  exact H.sector (i-cut) a ha u hu v hv

private theorem actual_zero_eta_area_bound {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : ActualSharedMomentDual.Coefficients R)
    (hm : ActualSharedMomentData.MaskBalanced R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℝ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e) (ear : Fin 9) :
    Real.pi ≤ ActualSharedMomentMaskedDual.dualConstant D kap 0+
      (∑ A : R.Index, ActualSharedMomentMaskedDual.faceFactor D kap A (faceAngle R A) (faceNormalized R A))+
      (∑ i : Fin 9, ActualSharedMomentMaskedDual.switchFactor D kap i
        (SwitchData.angle (switchData h hr v i)) (switchNormalized h hr v i))+
      (∑ i : Fin 9, ActualSharedMomentMaskedDual.sectorFactor D ear 0 i
        (sectorAngle v i) (leftNormalized v i) (rightNormalized v i)) := by
  have hb := ActualSharedMomentDual.actual_moment_factor_sum h hr R v D hm
  have hk := ActualSharedMomentMaskedDual.actual_delaunay_multiplier_balance h hr R v kap
  have hn : 0 ≤ ∑ e ∈ edges R, kap e*ActualEdgeMetricModel.edgeAngle h hr R v e :=
    Finset.sum_nonneg (fun e he => mul_nonneg (hkap e he)
      (ActualEdgeMetricModel.actual_edge_angle_area_domain h hr R v he).1)
  simp only [ActualSharedMomentMaskedDual.dualConstant,ActualSharedMomentMaskedDual.faceFactor,
    ActualSharedMomentMaskedDual.switchFactor,ActualSharedMomentMaskedDual.sectorFactor,
    ite_self,zero_mul,mul_zero,add_zero,sub_zero,Finset.sum_sub_distrib]
  linarith only [hb,hk,hn]

private theorem exclude_with_chart_area {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (v : NineTies c r)
    {F : Finset (Finset (Fin 11))} {cut : Fin 9} {b : Bool}
    (C : Coordinates R F (canonicalPerm cut b)) (D : CanonicalCoeffQ F)
    (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta alpha : ℚ)
    (K : CanonicalCertificate D kap (ear-cut) eta alpha)
    (harea : Real.pi ≤ ActualSharedMomentMaskedDual.dualConstant (pullback C D).toReal
      (fun e => (pullbackKap cut b kap e : ℝ)) eta+
      (∑ A : R.Index, ActualSharedMomentMaskedDual.faceFactor (pullback C D).toReal
        (fun e => (pullbackKap cut b kap e : ℝ)) A (faceAngle R A) (faceNormalized R A))+
      (∑ i : Fin 9, ActualSharedMomentMaskedDual.switchFactor (pullback C D).toReal
        (fun e => (pullbackKap cut b kap e : ℝ)) i
        (SwitchData.angle (switchData h hr v i)) (switchNormalized h hr v i))+
      (∑ i : Fin 9, ActualSharedMomentMaskedDual.sectorFactor (pullback C D).toReal ear eta i
        (sectorAngle v i) (leftNormalized v i) (rightNormalized v i))) : False := by
  have hf := face_factor_upper_pullback C D kap (ear-cut) eta K.faceMax K.switchMax K.sectorMax K.bounds
  have hs := switch_factor_upper_pullback C D kap (ear-cut) eta K.faceMax K.switchMax K.sectorMax K.bounds
  have ht := sector_factor_upper_pullback C D kap ear eta K.faceMax K.switchMax K.sectorMax K.bounds
  have hface := Finset.sum_le_sum (s := Finset.univ) (fun A _ => hf A (faceAngle R A)
    (fun s => ⟨(actual_face_angle_strict R A s).1.le,(actual_face_angle_strict R A s).2.le⟩)
    (actual_face_angle_sum h R A) (faceNormalized R A)
    ⟨(actual_face_normalized_domain h hr R A).1.le,(actual_face_normalized_domain h hr R A).2⟩)
  have hswitch := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hs i
    (SwitchData.angle (switchData h hr v i))
    ⟨(SwitchData.angle_bounds (switchData h hr v i)).1.le,
      (SwitchData.angle_bounds (switchData h hr v i)).2.le⟩
    (switchNormalized h hr v i)
    ⟨(actual_switch_normalized_domain h hr v i).1.le,(actual_switch_normalized_domain h hr v i).2⟩)
  have hsector := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i (sectorAngle v i)
    (actual_sector_angle_bounds v i) (leftNormalized v i)
    ⟨(actual_normalized_endpoint_domain h hr v i).1.le,
      (actual_normalized_endpoint_domain h hr v i).2.1⟩ (rightNormalized v i)
    ⟨(actual_normalized_endpoint_domain h hr v i).2.2.1.le,
      (actual_normalized_endpoint_domain h hr v i).2.2.2⟩)
  have hc := dualConstant_upper_of_bracket (pullback C D) (pullbackKap cut b kap)
    eta alpha K.eta_nonnegative K.bracket
  rw [sharpConstantUpperQ_pullback] at hc
  have hfs : (∑ A : R.Index, (K.faceMax (C.faceEquiv A) : ℝ))=∑ f : F, (K.faceMax f : ℝ) := by
    exact_mod_cast faceSum_pullback C K.faceMax
  have hss : (∑ i : Fin 9, (K.switchMax (i-cut) : ℝ))=∑ i : Fin 9, (K.switchMax i : ℝ) := by
    exact_mod_cast cyclicSum_pullback cut K.switchMax
  have hts : (∑ i : Fin 9, (K.sectorMax (i-cut) : ℝ))=∑ i : Fin 9, (K.sectorMax i : ℝ) := by
    exact_mod_cast cyclicSum_pullback cut K.sectorMax
  rw [hfs] at hface
  rw [hss] at hswitch
  rw [hts] at hsector
  have hstrict : (canonicalSharpConstantUpperQ D kap eta alpha : ℝ)+
      (∑ f : F, (K.faceMax f : ℝ))+(∑ i : Fin 9, (K.switchMax i : ℝ))+
      (∑ i : Fin 9, (K.sectorMax i : ℝ)) < Real.pi := by
    have hh : (canonicalTotalUpperQ D kap eta alpha K.faceMax K.switchMax K.sectorMax : ℝ)<
        (RatInterval.piLo : ℝ) := Rat.cast_lt.mpr K.strict
    have hh' := hh.trans RatInterval.piLo_lt_pi
    simpa only [canonicalTotalUpperQ,Rat.cast_add,Rat.cast_sum] using hh'
  linarith only [harea,hc,hface,hswitch,hsector,hstrict]

theorem exclude_q0_ordered {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (v : NineTies c r)
    (O : OrderedData R) (D : CanonicalCoeffQ (q0Faces O.run_length))
    (kap : Finset (Fin 11) → ℚ) (alpha : ℚ) (K : CanonicalCertificate D kap 0 0 alpha) : False := by
  let C := q0Coordinates h hr O
  have hm := maskBalanced_of_rational (pullback C D) (maskBalanced_pullback C D K.balance)
  have hkap : ∀ e ∈ edges R, (0 : ℝ) ≤ (pullbackKap O.cut (O.fans.colors O.cut) kap e : ℝ) := by
    intro e he
    exact_mod_cast nonnegative_edge_pullback C kap K.edge_nonnegative e he
  have harea := actual_zero_eta_area_bound h hr R v (pullback C D).toReal hm
    (fun e => (pullbackKap O.cut (O.fans.colors O.cut) kap e : ℝ)) hkap O.cut
  exact exclude_with_chart_area h hr R v C D kap O.cut 0 alpha (by simpa only [sub_self] using K)
    (by simpa only [Rat.cast_zero] using harea)

theorem exclude_q1_ordered {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (v : NineTies c r)
    (O : OrderedCoreData R) (D : CanonicalCoeffQ (q1Faces O.cut O.run_length))
    (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) (K : CanonicalCertificate D kap 0 eta alpha) : False := by
  let C := q1Coordinates h hr O
  have hm := maskBalanced_of_rational (pullback C D) (maskBalanced_pullback C D K.balance)
  have hkap : ∀ e ∈ edges R,
      (0 : ℝ) ≤ (pullbackKap O.fans.ear.center (O.fans.colors O.cut) kap e : ℝ) := by
    intro e he
    exact_mod_cast nonnegative_edge_pullback C kap K.edge_nonnegative e he
  have harea := ActualSharedMomentMaskedDual.actual_masked_moment_area_bound h hr R v O.fans.ear
    (pullback C D).toReal hm (fun e => (pullbackKap O.fans.ear.center (O.fans.colors O.cut) kap e : ℝ))
    hkap eta (by exact_mod_cast K.eta_nonnegative)
  exact exclude_with_chart_area h hr R v C D kap O.fans.ear.center eta alpha
    (by simpa only [sub_self] using K) harea

theorem exclude_q0_of_canonical_certificates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (v : NineTies c r)
    (hq : (ringOnlyTriangles R).card=0) (alpha : ℚ)
    (certificates : ∀ m : Fin 9, 0 < m.val →
      ∃ D : CanonicalCoeffQ (q0Faces m), ∃ kap : Finset (Fin 11) → ℚ,
        Nonempty (CanonicalCertificate D kap 0 0 alpha)) : False := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  obtain ⟨D,kap,⟨K⟩⟩ := certificates O.run_length O.positive
  exact exclude_q0_ordered h hr R v O D kap alpha K

theorem exclude_q1_of_canonical_certificates {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (v : NineTies c r)
    (hq : (ringOnlyTriangles R).card=1) (alpha : ℚ)
    (certificates : ∀ k m : Fin 8, 0 < m.val →
      ∃ D : CanonicalCoeffQ (q1Faces k m), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
        Nonempty (CanonicalCertificate D kap 0 eta alpha)) : False := by
  obtain ⟨O⟩ := actual_q1_ordered_core_fans h hr R hq
  obtain ⟨D,kap,eta,⟨K⟩⟩ := certificates O.cut O.run_length O.positive
  exact exclude_q1_ordered h hr R v O D kap eta alpha K

end N11Formalization.ActualCanonicalSharedMomentConsumer
#check @N11Formalization.ActualCanonicalSharedMomentConsumer.CanonicalFactorBounds
#check @N11Formalization.ActualCanonicalSharedMomentConsumer.CanonicalCertificate
#check @N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q0_of_canonical_certificates
#check @N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q1_of_canonical_certificates
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.sharpAlpha_bracket
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.sharpConstantUpperQ_pullback
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.face_factor_upper_pullback
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.switch_factor_upper_pullback
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.sector_factor_upper_pullback
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q0_ordered
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q1_ordered
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q0_of_canonical_certificates
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q1_of_canonical_certificates
