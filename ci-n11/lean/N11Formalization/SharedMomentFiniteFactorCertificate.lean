import N11Formalization.SharedMomentFacePlaneGradientCertificate
import N11Formalization.MetricSectorRationalCellCertificate

/-! Finite factor certificates with flexible rational roots. Each accepted
leaf has a rational check or a finite sqrt/arcsine bracket; no continuous
factor bound is supplied. Root containment and closed splits retain every
angle, radius, tie, zero chord, and subdivision boundary in the true domain. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFiniteFactorCertificate
open RationalBoxSubdivision ActualSharedMomentAdaptiveCertificate
open SharedMomentFactorGridCertificate SharedMomentFactorLocalGradientCertificate
open SharedMomentFacePlaneCertificate SharedMomentFacePlaneGradientCertificate
open MetricSectorRationalCellCertificate

def ContainsCell {I : Type*} (B D : Cell I) : Prop :=
  ∀ i, (B i).lo ≤ (D i).lo ∧ (D i).hi ≤ (B i).hi

theorem mem_of_contains {I : Type*} {B D : Cell I} {x : I → ℝ}
    (h : ContainsCell B D) (hx : Mem D x) : Mem B x := by
  intro i
  have hl : ((B i).lo : ℝ) ≤ ((D i).lo : ℝ) := by exact_mod_cast (h i).1
  have hh : ((D i).hi : ℝ) ≤ ((B i).hi : ℝ) := by exact_mod_cast (h i).2
  exact ⟨hl.trans (hx i).1,(hx i).2.trans hh⟩

def GradientFaceLeaf (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 3)) : Prop :=
  ActualSharedMomentTightAdaptiveCertificate.FaceLeaf p q b M B ∨
    faceGradientUpperQ p q b B ≤ M

theorem gradient_face_leaf_sound (p q b : Fin 3 → ℚ) (M : ℚ) (B : Cell (Fin 3))
    (hl : GradientFaceLeaf p q b M B) (a : Fin 3 → ℝ) (ha : Mem B a)
    (hsum : (∑ s : Fin 3, a s)=Real.pi) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
      (fun s => (b s : ℝ)) a y ≤ (M : ℝ) := by
  rcases hl with hl | hg
  · rcases hl with hout | hlocal | hdirect | hactive
    · exact (face_not_outside ha hsum hout).elim
    · exact SharedMomentFactorLocalCertificate.face_upper_of_local_certificate p q b B M hlocal a ha y hy
    · exact SharedMomentFactorIntervalCertificate.face_upper_of_direct_certificate p q b B M hdirect a ha y hy
    · exact SharedMomentActiveRadiusCertificate.face_upper_of_active_certificate p q b B M hactive a ha y hy
  · exact face_upper_of_gradient_certificate p q b B M hg a ha y hy

inductive FaceCertificate (p q b : Fin 3 → ℚ) (M : ℚ) : Type
  | box (B : Cell (Fin 3)) (hroot : ContainsCell B faceRoot)
      (tree : RationalBoxSubdivision.Certificate (GradientFaceLeaf p q b M) B)
  | plane (B : Cell (Fin 2))
      (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
      (tree : RationalBoxSubdivision.Certificate (GradientPlaneLeaf p q b M) B)

theorem FaceCertificate.sound {p q b : Fin 3 → ℚ} {M : ℚ} (C : FaceCertificate p q b M) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y ≤ (M : ℝ) := by
  cases C with
  | plane B hroot tree => exact face_upper_of_gradient_plane_tree p q b M B hroot tree
  | box B hroot tree =>
    have H := certificate_sound tree
      (fun a => (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
        faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
          (fun s => (b s : ℝ)) a y ≤ (M : ℝ)) (by
        intro B hl a ha hsum y hy
        exact gradient_face_leaf_sound p q b M B hl a ha hsum y hy)
    intro a ha hsum y hy
    have hmem : Mem faceRoot a := by
      intro s
      exact ⟨by simpa only [faceRoot,Rat.cast_zero] using (ha s).1,
        (ha s).2.trans RatInterval.pi_lt_piHi.le⟩
    exact H a (mem_of_contains hroot hmem) hsum y hy

def GradientSwitchLeaf (p q b d2 d1 M : ℚ) (B : Cell (Fin 1)) : Prop :=
  ActualSharedMomentTightAdaptiveCertificate.SwitchLeaf p q b d2 d1 M B ∨
    switchGradientUpperQ p q b d2 d1 B ≤ M

structure SwitchCertificate (p q b d2 d1 M : ℚ) where
  root : Cell (Fin 1)
  contains : ContainsCell root switchRoot
  tree : RationalBoxSubdivision.Certificate (GradientSwitchLeaf p q b d2 d1 M) root

theorem SwitchCertificate.sound {p q b d2 d1 M : ℚ} (C : SwitchCertificate p q b d2 d1 M) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  have H := certificate_sound C.tree
    (fun x => ∀ y ∈ Set.Icc (0 : ℝ) 1, switchObjective p q b d2 d1 (x 0) y ≤ (M : ℝ)) (by
      intro B hl x hx y hy
      rcases hl with hl | hg
      · rcases hl with hlocal | hdirect | hactive
        · exact SharedMomentFactorLocalCertificate.switch_upper_of_local_certificate p q b d2 d1 B M hlocal (x 0) (hx 0) y hy
        · exact SharedMomentFactorIntervalCertificate.switch_upper_of_direct_certificate p q b d2 d1 B M hdirect (x 0) (hx 0) y hy
        · exact SharedMomentActiveRadiusCertificate.switch_upper_of_active_certificate p q b d2 d1 B M hactive (x 0) (hx 0) y hy
      · exact switch_upper_of_gradient_certificate p q b d2 d1 B M hg (x 0) (hx 0) y hy)
  intro t ht y hy
  have hmem : Mem switchRoot (fun _ => t) := by
    intro i
    exact ⟨by simpa only [switchRoot,Rat.cast_zero] using ht.1,
      ht.2.trans RatInterval.pi_div_two_lt_hi.le⟩
  exact H (fun _ => t) (mem_of_contains C.contains hmem) y hy

def DirectSectorLeaf (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) : Prop :=
  SectorLeaf C mu dL dR bL bR M B ∨
    ∃ K : CellBounds, BoundsValid B K ∧ sectorDirectUpperQ C mu dL dR bL bR B K ≤ M

theorem direct_sector_leaf_sound (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3))
    (hl : DirectSectorLeaf C mu dL dR bL bR M B) (x : Fin 3 → ℝ) (hx : Mem B x) :
    MetricSectorBoxCertificate.sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  rcases hl with hglobal | ⟨K,hK,hbound⟩
  · change Nonempty (MetricSectorLocalCertificate.Certificate C mu dL dR bL bR M B) at hglobal
    rcases hglobal with ⟨T⟩
    exact T.sound x hx
  · exact sector_upper_of_direct_certificate C mu dL dR bL bR B K hK M hbound x hx

structure SectorCertificate (C mu dL dR bL bR M : ℚ) where
  root : Cell (Fin 3)
  contains : ContainsCell root sectorRoot
  tree : RationalBoxSubdivision.Certificate (DirectSectorLeaf C mu dL dR bL bR M) root

theorem SectorCertificate.sound {C mu dL dR bL bR M : ℚ} (T : SectorCertificate C mu dL dR bL bR M) :
    ∀ a ∈ Set.Icc (0 : ℝ) Real.pi, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ v ∈ Set.Icc (0 : ℝ) 1,
      MetricSectorBoxCertificate.sectorObjective C mu dL dR bL bR a u v ≤ (M : ℝ) := by
  have H := certificate_sound T.tree
    (fun x => MetricSectorBoxCertificate.sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ)) (by
      intro B hl x hx
      exact direct_sector_leaf_sound C mu dL dR bL bR M B hl x hx)
  intro a ha u hu v hv
  have hx : Mem sectorRoot ![a,u,v] := by
    intro i
    fin_cases i
    · simpa [sectorRoot,RatInterval.mem_iff] using
        (show (0 : ℝ) ≤ a ∧ a ≤ (RatInterval.piHi : ℝ) from
          ⟨ha.1,ha.2.trans RatInterval.pi_lt_piHi.le⟩)
    · simpa [sectorRoot,RatInterval.mem_iff] using hu
    · simpa [sectorRoot,RatInterval.mem_iff] using hv
  exact H ![a,u,v] (mem_of_contains T.contains hx)

end N11Formalization.SharedMomentFiniteFactorCertificate
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.mem_of_contains
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.gradient_face_leaf_sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.FaceCertificate.sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.SwitchCertificate.sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.direct_sector_leaf_sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.SectorCertificate.sound
