import N11Formalization.SharedMomentConcreteFace1Part3

set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteFace1
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz

theorem start0_face1_full_domain_upper :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      SharedMomentFactorGridCertificate.faceObjective (fun s => (start0_face1_p s : ℝ))
        (fun s => (start0_face1_q s : ℝ)) (fun s => (start0_face1_b s : ℝ)) a y ≤ (start0_face1_bound : ℝ) := by
  apply face_upper_of_gradient_plane_tree start0_face1_p start0_face1_q start0_face1_b start0_face1_bound (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ))
  · intro i
    fin_cases i <;> norm_num [planeBox,RatInterval.piHi]
  · exact start0_face1_node_1238

#print axioms start0_face1_full_domain_upper
end N11Formalization.SharedMomentConcreteFace1
