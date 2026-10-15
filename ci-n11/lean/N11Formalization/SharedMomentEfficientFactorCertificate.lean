import N11Formalization.SharedMomentFiniteFactorCertificate
import N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate
import N11Formalization.MetricSectorLocalGradientCertificate

/-! Finite factor data with small outward argmax brackets and positive
chord derivative leaves. Every zero-chord cell retains the complete direct
or global fallback. These certificates expose no real-valued premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentEfficientFactorCertificate
open RationalBoxSubdivision SharedMomentFiniteFactorCertificate
open SharedMomentFactorGridCertificate SharedMomentFacePlaneRoundedGradientCertificate
open ActualSharedMomentAdaptiveCertificate

inductive EfficientFaceCertificate (p q b : Fin 3 → ℚ) (M : ℚ) : Type
  | base (certificate : FaceCertificate p q b M)
  | rounded (B : Cell (Fin 2))
      (hroot : ∀ i, (B i).lo ≤ 0 ∧ RatInterval.piHi ≤ (B i).hi)
      (tree : RationalBoxSubdivision.Certificate (RoundedPlaneLeaf p q b M) B)

theorem EfficientFaceCertificate.sound {p q b : Fin 3 → ℚ} {M : ℚ}
    (C : EfficientFaceCertificate p q b M) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ))
        (fun s => (b s : ℝ)) a y ≤ (M : ℝ) := by
  cases C with
  | base certificate => exact certificate.sound
  | rounded B hroot tree => exact face_upper_of_rounded_plane_tree p q b M B hroot tree

def EfficientSectorLeaf (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) : Prop :=
  DirectSectorLeaf C mu dL dR bL bR M B ∨
    Nonempty (MetricSectorLocalGradientCertificate.PositiveCertificate C mu dL dR bL bR M B)

theorem efficient_sector_leaf_sound {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (hl : EfficientSectorLeaf C mu dL dR bL bR M B) :
    ∀ x, Mem B x → MetricSectorBoxCertificate.sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  rcases hl with hd | hg
  · exact direct_sector_leaf_sound C mu dL dR bL bR M B hd
  · rcases hg with ⟨G⟩
    exact G.sound

inductive EfficientSectorCertificate (C mu dL dR bL bR M : ℚ) : Type
  | base (certificate : SectorCertificate C mu dL dR bL bR M)
  | mixed (B : Cell (Fin 3)) (contains : ContainsCell B sectorRoot)
      (tree : RationalBoxSubdivision.Certificate (EfficientSectorLeaf C mu dL dR bL bR M) B)

theorem EfficientSectorCertificate.sound {C mu dL dR bL bR M : ℚ}
    (T : EfficientSectorCertificate C mu dL dR bL bR M) :
    ∀ a ∈ Set.Icc (0 : ℝ) Real.pi, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ v ∈ Set.Icc (0 : ℝ) 1,
      MetricSectorBoxCertificate.sectorObjective C mu dL dR bL bR a u v ≤ (M : ℝ) := by
  cases T with
  | base certificate => exact certificate.sound
  | mixed B contains tree =>
    have H := certificate_sound tree
      (fun x => MetricSectorBoxCertificate.sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ)) (by
        intro D hl x hx
        exact efficient_sector_leaf_sound hl x hx)
    intro a ha u hu v hv
    have hx : Mem sectorRoot ![a,u,v] := by
      intro i
      fin_cases i
      · simpa [sectorRoot,RatInterval.mem_iff] using
          (show (0 : ℝ) ≤ a ∧ a ≤ (RatInterval.piHi : ℝ) from
            ⟨ha.1,ha.2.trans RatInterval.pi_lt_piHi.le⟩)
      · simpa [sectorRoot,RatInterval.mem_iff] using hu
      · simpa [sectorRoot,RatInterval.mem_iff] using hv
    exact H ![a,u,v] (mem_of_contains contains hx)

end N11Formalization.SharedMomentEfficientFactorCertificate
#print axioms N11Formalization.SharedMomentEfficientFactorCertificate.EfficientFaceCertificate.sound
#print axioms N11Formalization.SharedMomentEfficientFactorCertificate.efficient_sector_leaf_sound
#print axioms N11Formalization.SharedMomentEfficientFactorCertificate.EfficientSectorCertificate.sound
