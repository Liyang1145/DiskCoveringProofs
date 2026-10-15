import N11Formalization.SharedMomentFacePlaneCertificate

/-! The signed angle-linear term is enclosed on the actual pi plane before
radius maximization. This keeps p0-p2 and p1-p2 cancellation, while enclosing
pi rationally without replacing its value. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFacePlaneDirectCertificate
open RationalBoxSubdivision SharedMomentFacePlaneCertificate
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate CompactQuadraticMomentMaximum

def planeLinearCell (p : Fin 3 → ℚ) (B : Cell (Fin 2)) : RatInterval :=
  sumThreeInterval ![p 0-p 2,p 1-p 2,p 2]
    ![B 0,B 1,⟨RatInterval.piLo,RatInterval.piHi⟩]

theorem plane_linear_mem (p : Fin 3 → ℚ) {B : Cell (Fin 2)}
    {x : Fin 2 → ℝ} (hx : Mem B x) :
    (planeLinearCell p B).Mem (∑ s : Fin 3, (p s : ℝ)*planeAngles x s) := by
  have H := sum_three_mem ![p 0-p 2,p 1-p 2,p 2]
    ![B 0,B 1,⟨RatInterval.piLo,RatInterval.piHi⟩] ![x 0,x 1,Real.pi] (by
      intro s
      fin_cases s
      · exact hx 0
      · exact hx 1
      · exact ⟨RatInterval.piLo_lt_pi.le,RatInterval.pi_lt_piHi.le⟩)
  have he : (∑ s : Fin 3, ((![p 0-p 2,p 1-p 2,p 2] s : ℚ) : ℝ)*
      (![x 0,x 1,Real.pi] s : ℝ)) =
      ∑ s : Fin 3, (p s : ℝ)*planeAngles x s := by
    simp only [Fin.sum_univ_three,planeAngles,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Rat.cast_sub]
    ring
  simpa only [planeLinearCell,he] using H

def planeDirectUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 2)) : ℚ :=
  (planeLinearCell p B).hi+
    maximumQ (faceQuadraticCell q (planeDomainCell B)).hi
      (faceLinearCell b (planeDomainCell B)).hi

theorem plane_envelope_le_direct_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 2)} {x : Fin 2 → ℝ} (hx : Mem B x)
    (hthird : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi) :
    faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) ≤ (planeDirectUpperQ p q b B : ℝ) := by
  have hA := SharedMomentFactorIntervalCertificate.face_quadratic_mem q
    (plane_domain_cell_mem hx hthird)
  have hB := SharedMomentFactorIntervalCertificate.face_linear_mem b
    (plane_domain_cell_mem hx hthird)
  have hm := (maximum_rational_enclosure hA.1 hA.2 hB.1 hB.2).2
  have hp := (plane_linear_mem p hx).2
  unfold faceEnvelope planeDirectUpperQ
  push_cast
  exact add_le_add hp hm

theorem plane_upper_of_direct_certificate (p q b : Fin 3 → ℚ)
    (B : Cell (Fin 2)) (M : ℚ) (hbound : planeDirectUpperQ p q b B ≤ M) :
    ∀ x, Mem B x → Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  intro x hx ht y hy
  exact ((faceObjective_le_envelope _ _ _ _ hy).trans
    (plane_envelope_le_direct_upper p q b hx ht)).trans (by exact_mod_cast hbound)

def DirectPlaneLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  PlaneLeaf p q b M B ∨ planeDirectUpperQ p q b B ≤ M

theorem direct_plane_leaf_sound (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2))
    (hl : DirectPlaneLeaf p q b M B) (x : Fin 2 → ℝ) (hx : Mem B x)
    (hthird : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  rcases hl with hl | hd
  · exact plane_leaf_sound p q b M B hl x hx hthird y hy
  · exact plane_upper_of_direct_certificate p q b B M hd x hx hthird y hy

theorem face_upper_of_direct_plane_tree (p q b : Fin 3 → ℚ) (M : ℚ)
    (B : Cell (Fin 2))
    (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    (T : RationalBoxSubdivision.Certificate (DirectPlaneLeaf p q b M) B) :
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
      exact direct_plane_leaf_sound p q b M C hl x hx ht y hy)
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

end N11Formalization.SharedMomentFacePlaneDirectCertificate
#check @N11Formalization.SharedMomentFacePlaneDirectCertificate.face_upper_of_direct_plane_tree
#print axioms N11Formalization.SharedMomentFacePlaneDirectCertificate.plane_linear_mem
#print axioms N11Formalization.SharedMomentFacePlaneDirectCertificate.plane_envelope_le_direct_upper
#print axioms N11Formalization.SharedMomentFacePlaneDirectCertificate.plane_upper_of_direct_certificate
#print axioms N11Formalization.SharedMomentFacePlaneDirectCertificate.face_upper_of_direct_plane_tree
