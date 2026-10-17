import N11Formalization.SharedMomentFacePlaneDirectCertificate
import N11Formalization.SharedMomentFactorLocalGradientCertificate

/-! Signed derivatives on the exact triangle plane. The third angle is
pi minus the first two; derivative differences keep its cancellations.
The target maximizing radius is fixed along the entire comparison segment,
and all original radii are recovered through the exact quadratic envelope. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFacePlaneGradientCertificate
open RationalBoxSubdivision SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorGridCertificate
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz CompactQuadraticMomentMaximum CompactQuadraticArgmaxRange

def planeGradient (p q b a : Fin 3 → ℝ) (y : ℝ) : Fin 2 → ℝ :=
  ![faceGradient p q b a y 0-faceGradient p q b a y 2,
    faceGradient p q b a y 1-faceGradient p q b a y 2]

def planeGradientCell (p q b : Fin 3 → ℚ) (B : Cell (Fin 2))
    (Y : RatInterval) : Fin 2 → RatInterval :=
  ![(faceGradientCell p q b (planeCell B) Y 0).sub
      (faceGradientCell p q b (planeCell B) Y 2),
    (faceGradientCell p q b (planeCell B) Y 1).sub
      (faceGradientCell p q b (planeCell B) Y 2)]

theorem plane_gradient_mem (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 2)} {a : Fin 3 → ℝ} {Y : RatInterval} {y : ℝ}
    (ha : Mem (planeCell B) a) (hy : Y.Mem y) (i : Fin 2) :
    (planeGradientCell p q b B Y i).Mem
      (planeGradient (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y i) := by
  fin_cases i
  · exact RatInterval.sub_mem (face_gradient_mem p q b ha hy 0)
      (face_gradient_mem p q b ha hy 2)
  · exact RatInterval.sub_mem (face_gradient_mem p q b ha hy 1)
      (face_gradient_mem p q b ha hy 2)

theorem plane_fixed_radius_difference (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 2)} {x x' : Fin 2 → ℝ} {Y : RatInterval} {y : ℝ}
    (hx : Mem B x) (hx' : Mem B x') (hy : Y.Mem y) :
    |faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ))
        (planeAngles x') y-
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ))
        (planeAngles x) y| ≤
      ∑ i : Fin 2, (absBoundQ (planeGradientCell p q b B Y i) : ℝ)*|x' i-x i| := by
  let path (t : ℝ) (s : Fin 3) :=
    planeAngles x s+t*(planeAngles x' s-planeAngles x s)
  let rate (t : ℝ) := ∑ s : Fin 3,
    faceGradient (fun j => (p j : ℝ)) (fun j => (q j : ℝ)) (fun j => (b j : ℝ))
      (path t) y s*(planeAngles x' s-planeAngles x s)
  have hd (t : ℝ) : HasDerivAt
      (fun t => faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (path t) y) (rate t) t := by
    apply face_path_hasDerivAt
    intro s
    simpa only [path,one_mul,id_eq] using!
      ((hasDerivAt_id t).mul_const (planeAngles x' s-planeAngles x s)).const_add
        (planeAngles x s)
  have hr (t : ℝ) : rate t=∑ i : Fin 2,
      planeGradient (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (path t) y i*(x' i-x i) := by
    simp only [rate,Fin.sum_univ_three,Fin.sum_univ_two,planeGradient,planeAngles,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]
    ring
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖rate t‖ ≤ ∑ i : Fin 2, (absBoundQ (planeGradientCell p q b B Y i) : ℝ)*|x' i-x i| := by
    rw [Real.norm_eq_abs,hr]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_of_mem (plane_gradient_mem p q b
        (segment_mem (plane_cell_mem hx) (plane_cell_mem hx') ht) hy i)) (abs_nonneg _)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => (hd t).hasDerivWithinAt) hb
    (convex_Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hp0 : path 0=planeAngles x := by funext s; simp only [path,zero_mul,add_zero]
  have hp1 : path 1=planeAngles x' := by funext s; dsimp [path]; ring
  simpa only [hp0,hp1,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh

def planeRadiusCell (q b : Fin 3 → ℚ) (B : Cell (Fin 2)) : RatInterval :=
  faceRadiusCell q b (planeDomainCell B)

def planeGradientErrorQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 2)) : ℚ :=
  ∑ i : Fin 2, absBoundQ (planeGradientCell p q b B (planeRadiusCell q b B) i)*
    halfWidth B i

def planeGradientUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 2)) : ℚ :=
  faceDirectUpperQ p q b (planeMidpointCell B)+planeGradientErrorQ p q b B

theorem plane_envelope_le_gradient_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 2)} {x : Fin 2 → ℝ} (hx : Mem B x)
    (ht : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi) :
    faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) ≤ (planeGradientUpperQ p q b B : ℝ) := by
  have ha := plane_domain_cell_mem hx ht
  have hA := SharedMomentFactorIntervalCertificate.face_quadratic_mem q ha
  have hB := SharedMomentFactorIntervalCertificate.face_linear_mem b ha
  obtain ⟨y,hy,heq,hyLo,hyHi⟩ := maximum_attained_with_rational_enclosure _ _
    (faceQuadraticCell q (planeDomainCell B)).lo (faceQuadraticCell q (planeDomainCell B)).hi
    (faceLinearCell b (planeDomainCell B)).lo (faceLinearCell b (planeDomainCell B)).hi
    hA.1 hA.2 hB.1 hB.2
  have hyY : (planeRadiusCell q b B).Mem y := ⟨hyLo,hyHi⟩
  have hvalid : Valid B := fun i => RatInterval.valid_of_mem (hx i)
  have hmid := midpoint_mem hvalid
  have hd := plane_fixed_radius_difference p q b hmid hx hyY
  have herr : (∑ i : Fin 2,
      (absBoundQ (planeGradientCell p q b B (planeRadiusCell q b B) i) : ℝ)*
        |x i-(midpoint B i : ℝ)|) ≤ (planeGradientErrorQ p q b B : ℝ) := by
    unfold planeGradientErrorQ
    push_cast
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (distance_le_halfWidth hx i)
      (by exact_mod_cast absBoundQ_nonneg (planeGradientCell p q b B (planeRadiusCell q b B) i))
  have hm := faceObjective_le_envelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
    (fun s => (b s : ℝ)) (planeAngles (fun i => (midpoint B i : ℝ))) hy
  have hn := SharedMomentFactorIntervalCertificate.face_envelope_le_direct_upper p q b (plane_midpoint_mem B)
  have he : faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y=
      faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) := by
    unfold faceObjective faceEnvelope
    rw [heq]
  have hda := (le_abs_self _).trans hd
  rw [he] at hda
  unfold planeGradientUpperQ
  push_cast
  linarith only [hda,herr,hm,hn]

theorem plane_upper_of_gradient_certificate (p q b : Fin 3 → ℚ)
    (B : Cell (Fin 2)) (M : ℚ) (hbound : planeGradientUpperQ p q b B ≤ M) :
    ∀ x, Mem B x → Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  intro x hx ht y hy
  exact ((faceObjective_le_envelope _ _ _ _ hy).trans
    (plane_envelope_le_gradient_upper p q b hx ht)).trans (by exact_mod_cast hbound)

def GradientPlaneLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  DirectPlaneLeaf p q b M B ∨ planeGradientUpperQ p q b B ≤ M

theorem gradient_plane_leaf_sound (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2))
    (hl : GradientPlaneLeaf p q b M B) (x : Fin 2 → ℝ) (hx : Mem B x)
    (ht : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  rcases hl with hl | hg
  · exact direct_plane_leaf_sound p q b M B hl x hx ht y hy
  · exact plane_upper_of_gradient_certificate p q b B M hg x hx ht y hy

theorem face_upper_of_gradient_plane_tree (p q b : Fin 3 → ℚ) (M : ℚ)
    (B : Cell (Fin 2))
    (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    (T : RationalBoxSubdivision.Certificate (GradientPlaneLeaf p q b M) B) :
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
      exact gradient_plane_leaf_sound p q b M C hl x hx ht y hy)
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
    simpa only [planeAngles,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using congrFun he 2
  simpa only [he] using H x hx (ht.symm ▸ ha 2) y hy

end N11Formalization.SharedMomentFacePlaneGradientCertificate
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.plane_gradient_mem
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.plane_fixed_radius_difference
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.plane_envelope_le_gradient_upper
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.plane_upper_of_gradient_certificate
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.gradient_plane_leaf_sound
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.face_upper_of_gradient_plane_tree
