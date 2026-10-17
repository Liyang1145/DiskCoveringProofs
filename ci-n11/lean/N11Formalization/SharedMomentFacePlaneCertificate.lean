import N11Formalization.ActualSharedMomentTightAdaptiveCertificate

/-! Rational two-coordinate certificates for the complete triangle plane.
The third angle is pi minus the two retained coordinates. Its rational
enclosure preserves boundary-crossing cells and the true irrational pi;
only a proved disjointness comparison may remove a leaf. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFacePlaneCertificate
open RationalBoxSubdivision SharedMomentFactorGridCertificate
open SharedMomentFactorLocalCertificate SharedMomentFactorIntervalCertificate
open SharedMomentActiveRadiusCertificate

def planeAngles (x : Fin 2 → ℝ) : Fin 3 → ℝ := ![x 0,x 1,Real.pi-x 0-x 1]

def planeCell (B : Cell (Fin 2)) : Cell (Fin 3) :=
  ![B 0,B 1,⟨RatInterval.piLo-(B 0).hi-(B 1).hi,
    RatInterval.piHi-(B 0).lo-(B 1).lo⟩]

def planeDomainCell (B : Cell (Fin 2)) : Cell (Fin 3) :=
  ![B 0,B 1,⟨max 0 (RatInterval.piLo-(B 0).hi-(B 1).hi),
    min RatInterval.piHi (RatInterval.piHi-(B 0).lo-(B 1).lo)⟩]

def planeMidpointCell (B : Cell (Fin 2)) : Cell (Fin 3) :=
  ![RatInterval.ofRat (midpoint B 0),RatInterval.ofRat (midpoint B 1),
    ⟨RatInterval.piLo-midpoint B 0-midpoint B 1,
      RatInterval.piHi-midpoint B 0-midpoint B 1⟩]

theorem planeAngles_sum (x : Fin 2 → ℝ) : (∑ s : Fin 3, planeAngles x s)=Real.pi := by
  simp only [planeAngles,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring

theorem plane_cell_mem {B : Cell (Fin 2)} {x : Fin 2 → ℝ} (hx : Mem B x) :
    Mem (planeCell B) (planeAngles x) := by
  intro s
  fin_cases s
  · simpa [planeCell,planeAngles] using hx 0
  · simpa [planeCell,planeAngles] using hx 1
  · have hpL := RatInterval.piLo_lt_pi.le
    have hpH := RatInterval.pi_lt_piHi.le
    have h0 := hx 0
    have h1 := hx 1
    simp only [planeCell,planeAngles,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,RatInterval.mem_iff]
    push_cast
    constructor <;> linarith only [hpL,hpH,h0.1,h0.2,h1.1,h1.2]

theorem plane_domain_cell_mem {B : Cell (Fin 2)} {x : Fin 2 → ℝ}
    (hx : Mem B x) (hthird : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi) :
    Mem (planeDomainCell B) (planeAngles x) := by
  have hu := plane_cell_mem hx
  intro s
  fin_cases s
  · simpa [planeDomainCell,planeCell,planeAngles] using hu 0
  · simpa [planeDomainCell,planeCell,planeAngles] using hu 1
  · have h2 := hu 2
    simp only [planeCell,planeAngles,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,RatInterval.mem_iff] at h2
    simp only [planeDomainCell,planeAngles,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,RatInterval.mem_iff]
    push_cast
    push_cast at h2
    exact ⟨max_le hthird.1 h2.1,le_min (hthird.2.trans RatInterval.pi_lt_piHi.le) h2.2⟩

theorem plane_midpoint_mem (B : Cell (Fin 2)) :
    Mem (planeMidpointCell B) (planeAngles (fun i => (midpoint B i : ℝ))) := by
  intro s
  fin_cases s
  · exact RatInterval.ofRat_mem _
  · exact RatInterval.ofRat_mem _
  · simp only [planeMidpointCell,planeAngles,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,RatInterval.mem_iff]
    push_cast
    constructor <;> linarith only [RatInterval.piLo_lt_pi,RatInterval.pi_lt_piHi]

def PlaneOutside (B : Cell (Fin 2)) : Prop := RatInterval.piHi ≤ (B 0).lo+(B 1).lo

theorem plane_not_outside {B : Cell (Fin 2)} {x : Fin 2 → ℝ}
    (hx : Mem B x) (hthird : 0 ≤ Real.pi-x 0-x 1) : ¬ PlaneOutside B := by
  intro h
  have h' : (RatInterval.piHi : ℝ) ≤ ((B 0).lo : ℝ)+((B 1).lo : ℝ) := by
    exact_mod_cast h
  have h0 := (hx 0).1
  have h1 := (hx 1).1
  linarith only [h',h0,h1,hthird,RatInterval.pi_lt_piHi]

def PlaneLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2)) : Prop :=
  PlaneOutside B ∨
    ActualSharedMomentTightAdaptiveCertificate.FaceLeaf p q b M (planeDomainCell B)

theorem plane_leaf_sound (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 2))
    (hl : PlaneLeaf p q b M B) (x : Fin 2 → ℝ) (hx : Mem B x)
    (hthird : Real.pi-x 0-x 1 ∈ Set.Icc (0 : ℝ) Real.pi)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) (planeAngles x) y ≤ (M : ℝ) := by
  rcases hl with hout | hout | hlocal | hdirect | hactive
  · exact (plane_not_outside hx hthird.1 hout).elim
  · exact (ActualSharedMomentAdaptiveCertificate.face_not_outside
      (plane_domain_cell_mem hx hthird) (planeAngles_sum x) hout).elim
  · exact face_upper_of_local_certificate p q b _ M hlocal
      _ (plane_domain_cell_mem hx hthird) y hy
  · exact face_upper_of_direct_certificate p q b _ M hdirect
      _ (plane_domain_cell_mem hx hthird) y hy
  · exact face_upper_of_active_certificate p q b _ M hactive
      _ (plane_domain_cell_mem hx hthird) y hy

theorem face_upper_of_plane_tree (p q b : Fin 3 → ℚ) (M : ℚ)
    (B : Cell (Fin 2))
    (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
    (T : RationalBoxSubdivision.Certificate (PlaneLeaf p q b M) B) :
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
      exact plane_leaf_sound p q b M C hl x hx ht y hy)
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

end N11Formalization.SharedMomentFacePlaneCertificate
#check @N11Formalization.SharedMomentFacePlaneCertificate.face_upper_of_plane_tree
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.plane_cell_mem
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.plane_domain_cell_mem
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.plane_midpoint_mem
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.plane_leaf_sound
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.face_upper_of_plane_tree
