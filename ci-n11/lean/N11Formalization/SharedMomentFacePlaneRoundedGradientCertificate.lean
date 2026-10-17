import N11Formalization.SharedMomentFacePlaneGradientCertificate

/-! Finite outward brackets for maximizing radii. Supplied small rational
endpoints enclose the already proved exact argmax interval; all subsequent
gradient arithmetic uses the small bracket. The only new premise is a
finite rational endpoint comparison, and every original radius is retained. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate
open RationalBoxSubdivision SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneGradientCertificate SharedMomentFactorGridCertificate
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz CompactQuadraticMomentMaximum CompactQuadraticArgmaxRange

def RadiusContains (q b : Fin 3 → ℚ) (B : Cell (Fin 2)) (Y : RatInterval) : Prop :=
  Y.lo ≤ (planeRadiusCell q b B).lo ∧ (planeRadiusCell q b B).hi ≤ Y.hi

theorem radius_mem_of_contains {q b : Fin 3 → ℚ} {B : Cell (Fin 2)}
    {Y : RatInterval} (hY : RadiusContains q b B Y) {y : ℝ}
    (hy : (planeRadiusCell q b B).Mem y) : Y.Mem y := by
  have hl : (Y.lo : ℝ) ≤ ((planeRadiusCell q b B).lo : ℝ) := by exact_mod_cast hY.1
  have hh : ((planeRadiusCell q b B).hi : ℝ) ≤ (Y.hi : ℝ) := by exact_mod_cast hY.2
  exact ⟨hl.trans hy.1,hy.2.trans hh⟩

def roundedGradientErrorQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 2)) (Y : RatInterval) : ℚ :=
  ∑ i : Fin 2, absBoundQ (planeGradientCell p q b B Y i)*halfWidth B i

def roundedGradientUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 2)) (Y : RatInterval) : ℚ :=
  faceDirectUpperQ p q b (planeMidpointCell B)+roundedGradientErrorQ p q b B Y

theorem plane_envelope_le_rounded_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 2)} {Y : RatInterval} (hY : RadiusContains q b B Y)
    {x : Fin 2 → ℝ} (hx : Mem B x)
    (ht : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi) :
    faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) ≤ (roundedGradientUpperQ p q b B Y : ℝ) := by
  have ha := plane_domain_cell_mem hx ht
  have hA := SharedMomentFactorIntervalCertificate.face_quadratic_mem q ha
  have hB := SharedMomentFactorIntervalCertificate.face_linear_mem b ha
  obtain ⟨y,hy,heq,hyLo,hyHi⟩ := maximum_attained_with_rational_enclosure _ _
    (faceQuadraticCell q (planeDomainCell B)).lo (faceQuadraticCell q (planeDomainCell B)).hi
    (faceLinearCell b (planeDomainCell B)).lo (faceLinearCell b (planeDomainCell B)).hi
    hA.1 hA.2 hB.1 hB.2
  have hyY : Y.Mem y := radius_mem_of_contains hY ⟨hyLo,hyHi⟩
  have hvalid : Valid B := fun i => RatInterval.valid_of_mem (hx i)
  have hmid := midpoint_mem hvalid
  have hd := plane_fixed_radius_difference p q b hmid hx hyY
  have herr : (∑ i : Fin 2, (absBoundQ (planeGradientCell p q b B Y i) : ℝ)*
        |x i-(midpoint B i : ℝ)|) ≤ (roundedGradientErrorQ p q b B Y : ℝ) := by
    unfold roundedGradientErrorQ
    push_cast
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (distance_le_halfWidth hx i)
      (by exact_mod_cast absBoundQ_nonneg (planeGradientCell p q b B Y i))
  have hm := faceObjective_le_envelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
    (fun s => (b s : ℝ)) (planeAngles (fun i => (midpoint B i : ℝ))) hy
  have hn := SharedMomentFactorIntervalCertificate.face_envelope_le_direct_upper p q b
    (plane_midpoint_mem B)
  have he : faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y=
      faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) := by
    unfold faceObjective faceEnvelope
    rw [heq]
  have hda := (le_abs_self _).trans hd
  rw [he] at hda
  unfold roundedGradientUpperQ
  push_cast
  linarith only [hda,herr,hm,hn]

theorem plane_upper_of_rounded_certificate (p q b : Fin 3 → ℚ)
    (B : Cell (Fin 2)) (Y : RatInterval) (hY : RadiusContains q b B Y)
    (M : ℚ) (hbound : roundedGradientUpperQ p q b B Y ≤ M) :
    ∀ x, Mem B x → Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  intro x hx ht y hy
  exact ((faceObjective_le_envelope _ _ _ _ hy).trans
    (plane_envelope_le_rounded_upper p q b hY hx ht)).trans (by exact_mod_cast hbound)

def RoundedPlaneLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  GradientPlaneLeaf p q b M B ∨
    ∃ Y : RatInterval, RadiusContains q b B Y ∧ roundedGradientUpperQ p q b B Y ≤ M

theorem rounded_plane_leaf_sound (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2))
    (hl : RoundedPlaneLeaf p q b M B) (x : Fin 2 → ℝ) (hx : Mem B x)
    (ht : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  rcases hl with hl | ⟨Y,hY,hbound⟩
  · exact gradient_plane_leaf_sound p q b M B hl x hx ht y hy
  · exact plane_upper_of_rounded_certificate p q b B Y hY M hbound x hx ht y hy

theorem face_upper_of_rounded_plane_tree (p q b : Fin 3 → ℚ) (M : ℚ)
    (B : Cell (Fin 2))
    (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    (T : RationalBoxSubdivision.Certificate (RoundedPlaneLeaf p q b M) B) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y ≤ (M : ℝ) := by
  have H := certificate_sound T
    (fun x => Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ)) (by
      intro C hl x hx ht y hy
      exact rounded_plane_leaf_sound p q b M C hl x hx ht y hy)
  intro a ha hsum y hy
  let x : Fin 2 → ℝ := ![a 0,a 1]
  have hx : Mem B x := by
    intro i
    have hl : ((B i).lo : ℝ) ≤ 0 := by exact_mod_cast (hroot i).1
    have hh : (RatInterval.piHi : ℝ) ≤ ((B i).hi : ℝ) := by exact_mod_cast (hroot i).2
    fin_cases i
    · exact ⟨hl.trans (ha 0).1,(ha 0).2.trans (RatInterval.pi_lt_piHi.le.trans hh)⟩
    · exact ⟨hl.trans (ha 1).1,(ha 1).2.trans (RatInterval.pi_lt_piHi.le.trans hh)⟩
  have he : planeAngles x=a := by
    funext s
    fin_cases s
    · rfl
    · rfl
    · change Real.pi-a 0-a 1=a 2
      simp only [Fin.sum_univ_three] at hsum
      linarith only [hsum]
  have ht : Real.pi-x 0-x 1=a 2 := by
    simpa [planeAngles] using congrFun he 2
  simpa only [he] using H x hx (ht.symm ▸ ha 2) y hy

end N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.radius_mem_of_contains
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.plane_envelope_le_rounded_upper
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.plane_upper_of_rounded_certificate
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.rounded_plane_leaf_sound
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.face_upper_of_rounded_plane_tree
