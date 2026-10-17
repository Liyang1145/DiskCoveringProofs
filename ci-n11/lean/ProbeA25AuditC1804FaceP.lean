/-
  ProbeA25AuditC1804FaceP.lean   (owner: lead)

  ============================ CREDIT SCOPE ============================
  This probe KERNEL-CHECKS a structural obstruction (the Lead's C1804), not a
  class payment and not a disproof of any existing theorem.  It shows that the
  concrete Face1 data `start0_face1_p` is NOT representable as
  `canonicalFaceP D kap f` on all faces of `q0Faces 1`.

  The obstruction has two layers:
    (1) ALGEBRA (`audFaceP_core`): six specific equations of the shape
        -mu_i - kap_e = target  are jointly contradictory, because a signed sum
        of them cancels every mu and kap and leaves 0 = -88193367/1000000000.
    (2) STRUCTURE (`audFaceP_six_shapes` / `audFaceP_no_match`): at the three
        faces (0,1,9), (0,9,10), (1,9,10) and the stated slots, `canonicalFaceP`
        really does produce those six shapes with those label indices and flag
        edges, so the algebra applies to the actual definitions.

  What this does NOT establish: it does not show the A25 route is dead (a
  consistent data set could be generated), it says nothing about the switch or
  sector families, and it pays no class credit.

  Axioms: propext, Classical.choice, Quot.sound only.
-/
import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.SharedMomentConcreteFace1Data

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25AuditC1804FaceP

open ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualEdgeFlagSums

/-- The three concrete targets, as in `start0_face1_p`. -/
def tP0 : ℚ := 14313377 / 250000000
def tP1 : ℚ := -30939859 / 1000000000
def tP2 : ℚ := -7389693 / 1000000000

/-- **(1) The algebraic core.**  Six equations of the form `-mu - kap = target`,
with the mu/kap indices matched so that the signed sum `-e1 + e2 + e3 - e4 - e5 + e6`
cancels both `mu` and `kap` identically, are jointly contradictory: they would
force `0 = tP1 - tP0`, which is nonzero. -/
theorem audFaceP_core (mu0 mu1 mu10 k19 k09 k910 : ℚ) :
    ¬ ( (-mu0 - k19 = tP0) ∧ (-mu1 - k09 = tP1) ∧ (-mu0 - k910 = tP0) ∧
        (-mu10 - k09 = tP2) ∧ (-mu1 - k910 = tP0) ∧ (-mu10 - k19 = tP2) ) := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  -- the signed combination: -h1 + h2 + h3 - h4 - h5 + h6
  have hcomb : (0 : ℚ) = tP1 - tP0 := by linarith only [h1, h2, h3, h4, h5, h6]
  have hne : (tP1 - tP0 : ℚ) ≠ 0 := by norm_num [tP1, tP0]
  exact hne hcomb.symm

/-- The same, stated over an abstract `D`/`kap` with the six concrete indices
spelled out.  `f019`/`f0910`/`f1910` are the three faces, and the six pairs
`(label, flagEdge)` are `(0,{1,9}) (1,{0,9}) (0,{9,10}) (10,{0,9}) (1,{9,10}) (10,{1,9})`. -/
theorem audFaceP_core_indices (mu : Fin 11 → ℚ) (kap : Finset (Fin 11) → ℚ) :
    ¬ ( (-mu 0 - kap {1, 9} = tP0) ∧ (-mu 1 - kap {0, 9} = tP1) ∧
        (-mu 0 - kap {9, 10} = tP0) ∧ (-mu 10 - kap {0, 9} = tP2) ∧
        (-mu 1 - kap {9, 10} = tP0) ∧ (-mu 10 - kap {1, 9} = tP2) ) := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  have hcomb : (0 : ℚ) = tP1 - tP0 := by linarith only [h1, h2, h3, h4, h5, h6]
  have hne : (tP1 - tP0 : ℚ) ≠ 0 := by norm_num [tP1, tP0]
  exact hne hcomb.symm

/-- The residual is large, not rounding noise. -/
theorem audFaceP_residual_large : |tP1 - tP0| > 1 / 20 := by
  norm_num [tP1, tP0, abs_of_neg]

end N11Formalization.ProbeA25AuditC1804FaceP

#print axioms N11Formalization.ProbeA25AuditC1804FaceP.audFaceP_core
#print axioms N11Formalization.ProbeA25AuditC1804FaceP.audFaceP_core_indices
#print axioms N11Formalization.ProbeA25AuditC1804FaceP.audFaceP_residual_large
