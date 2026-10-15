import N11Formalization
set_option autoImplicit false
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic
open SourceCentreB2Readout SourcePositiveHarmonicConsumer
open HarmonicSourceTransport SourceActiveLaplacian SourceActiveHarmonicSolve
open SourceActiveAffineResponse SourceActiveFiniteSystem SourceActiveMatrixIntervals

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print SourceActiveLaplacian.A
#print SourceActiveHarmonicSolve.activeH
#print SourceActiveFiniteSystem.nodeEquiv
#print SourceActiveFiniteSystem.matrix20
#print SourceActiveFiniteSystem.rhs20
#print SourceActiveMatrixIntervals.ABox
#print SourceActiveMatrixIntervals.rhsBox
#check @SourceH0PinnedReduction.quadratic_pin_reduce
#check @SourceActiveLaplacian.incidenceZ_binding
#check @SourceActiveLaplacian.B_canonical
#check @SourceActiveLaplacian.grounded_kernel
#check @SourceActiveLaplacian.A_det_ne_zero
#check @SourceActiveHarmonicSolve.coeff_active
#check @SourceActiveHarmonicSolve.activeH_solve
#check @SourceActiveHarmonicSolve.activeH_unique
#check @SourceActiveHarmonicSolve.activeH_inverse
#check @SourceActiveAffineResponse.activeH_affine
#check @SourceActiveAffineResponse.response_rows_zero
#check @SourceActiveAffineResponse.actual_pair_energy
#check @SourceActiveAffineResponse.actual_pair_le_oracle
#check @SourceActiveFiniteSystem.H20_solve
#check @SourceActiveFiniteSystem.H20_actual_site
#check @SourceActiveFiniteSystem.H20_actual_face
#check @SourceActiveFiniteSystem.H20_coordinates_of_certificate
#check @SourceStressClosedFormula.face_closed
#check @SourceStressClosedFormula.spoke_closed
#check @SourceStressIntervals.stressI_mem
#check @SourceActiveMatrixIntervals.ABox_mem
#check @SourceActiveMatrixIntervals.rhsBox_mem
#print axioms SourceActiveLaplacian.A_det_ne_zero
#print axioms SourceActiveHarmonicSolve.activeH_inverse
#print axioms SourceActiveAffineResponse.actual_pair_le_oracle
#print axioms SourceActiveFiniteSystem.H20_solve
#print axioms SourceStressClosedFormula.spoke_closed
#print axioms SourceStressIntervals.stressI_mem
#print axioms SourceActiveMatrixIntervals.ABox_mem
#print axioms SourceActiveMatrixIntervals.rhsBox_mem

-- Actual hub consumers: no Fin9 wraparound for sites9/10.
example (j : Fin 9) :
    H20 j (Fin.castAdd 9 (9 : Fin 11))=sourceH (srcNode (.inl 9)) j :=
  H20_actual_site j 9
example (j : Fin 9) :
    H20 j (Fin.castAdd 9 (10 : Fin 11))=sourceH (srcNode (.inl 10)) j :=
  H20_actual_site j 10
example (j f : Fin 9) :
    H20 j (Fin.natAdd 11 f)=sourceH (srcNode (.inr f)) j :=
  H20_actual_face j f
example (θ : Fin 9 → ℝ) :
    (2*∑ i : Fin 9,∑ j : Fin 9,if i<j then
      -SourceResponseFluxIdentity.sourceResponse i j*(1-Real.cos (θ i-θ j)) else 0)≤
        V2 (fun j => circleMap (θ j)) :=
  actual_pair_le_oracle θ
example (e : ResumeLocalIncidence.SourceEdge) :
    (SourceStressIntervals.stressI e).Mem (SourceSignedStressAssembly.stress e) :=
  SourceStressIntervals.stressI_mem e
example (i k : Fin 20) : (ABox i k).Mem (matrix20 i k) := ABox_mem i k
example (j : Fin 9) (i : Fin 20) : (rhsBox j i).Mem (rhs20 j i) := rhsBox_mem j i

-- Real certificate consumer with actual A/rhs/solution memberships paid.
-- Numerical contraction and residual inequalities are STILL explicit.
example (j : Fin 9) (C : Matrix (Fin 20) (Fin 20) ℚ) (y : Fin 20 → ℚ)
    (q err : ℝ) (hq : 0≤q) (hq1 : q<1) (herr : 0≤err)
    (hrow : ∀ i,∑ k : Fin 20,
      max |((krawczykMat C ABox i k).lo : ℝ)| |((krawczykMat C ABox i k).hi : ℝ)|≤q)
    (hresidual : ∀ i,
      max |((ResumeLinearSolveEnclosure.residualBox C ABox (rhsBox j) y i).lo : ℝ)|
        |((ResumeLinearSolveEnclosure.residualBox C ABox (rhsBox j) y i).hi : ℝ)|≤err)
    (i : Fin 20) :
    (y i : ℝ)-err/(1-q)≤H20 j i ∧ H20 j i≤(y i : ℝ)+err/(1-q) :=
  H20_coordinates_of_certificate j C ABox (rhsBox j) y q err hq hq1 herr
    ABox_mem (rhsBox_mem j) hrow hresidual i
