import N11Formalization.SourceActiveLaplacian

/-! Exact20-node harmonic solve for SAME actual stress. The restriction of the
constructed22-node H solves the nonsingular source free block after the correct
source/canonical reindexing; slack rows never enter this active solve.
Provides an actual inverse representation for later interval certification.
No numerical solution, inverse, connectivity or missing balance premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceActiveHarmonicSolve
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux
open ResumeLocalIncidence HarmonicSourceTransport SourceCentreB2Readout
open SourcePositiveHarmonicConsumer SourceActiveLaplacian
noncomputable section

def activeH (v : SrcFree) (j : Fin 9) : ℝ := sourceH (srcNode v) j
def anchorRow (e : SourceEdge) (j : Fin 9) : ℝ := anchorIncidence (edgeMap e) j
def K (e : SourceEdge) (j : Fin 9) : ℝ :=
  LaplacianSchurBridge.edgeCoeff B anchorRow activeH e j

theorem unused_incidence (e : Edge) (he : canonicalStress e≠0) (v : Free)
    (hv : ∀ w : SrcFree,srcNode w≠v) : incidence e v=0 := by
  rcases unused_iff_slack v hv with rfl | rfl
  · rcases e with ⟨i,s⟩ | ⟨f,q⟩
    · simp [incidence]
    · by_cases hf : f=5
      · subst f
        exact (he (canonical_slack_zero q).1).elim
      · simp [incidence,hf,Ne.symm hf]
  · rcases e with ⟨i,s⟩ | ⟨f,q⟩
    · simp [incidence]
    · by_cases hf : f=7
      · subst f
        exact (he (canonical_slack_zero q).2).elim
      · simp [incidence,hf,Ne.symm hf]

theorem coeff_active (e : SourceEdge) (j : Fin 9) :
    coeff sourceH (edgeMap e) j=K e j := by
  have he : canonicalStress (edgeMap e)≠0 := by
    rw [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
    exact ne_of_gt (SourceBoundaryStressPositive.stress_pos e)
  have h := HarmonicUnusedExtension.edgeCoeff_extend_eq
    (α := canonicalStress) (B := incidence) (a := anchorIncidence) (active := srcNode)
    srcNode_injective unused_incidence
    (h := activeH) (H := sourceH) (fun _ _ => rfl) (e := edgeMap e) (j := j) he
  rw [NetworkSchurBinding.coeff_eq,activeCoeff_eq_srcCoeff] at h
  simpa only [K,LaplacianSchurBridge.edgeCoeff,anchorRow,srcCoeff,B_binding] using h

theorem active_balance (v : SrcFree) (j : Fin 9) :
    ∑ e : SourceEdge,(SourceSignedStressAssembly.stress e*B e v)*K e j=0 := by
  have h := sourceH_columns (srcNode v) j
  have hr := sum_edge_eq_sum_sourceEdge
    (α := canonicalStress)
    (F := fun e => incidence e (srcNode v)*coeff sourceH e j)
    (zero_off_image_of_slack canonical_slack_zero)
  have hc :
      (∑ e : Edge,canonicalStress e*(incidence e (srcNode v)*coeff sourceH e j))=0 := by
    convert h using 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hr] at hc
  simp only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap,coeff_active] at hc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro e _
  rw [B_canonical]
  ring

def rhs (v : SrcFree) (j : Fin 9) : ℝ :=
  -LaplacianSchurBridge.crossBlock SourceSignedStressAssembly.stress B anchorRow v j

/-- The actual restricted sourceH solves the actual nonsingular20-node system. -/
theorem activeH_solve (j : Fin 9) :
    A.mulVec (fun w => activeH w j)=fun v => rhs v j := by
  have hb : LaplacianSchurBridge.Balanced SourceSignedStressAssembly.stress B anchorRow activeH :=
    active_balance
  have h := (LaplacianSchurBridge.balanced_iff_normal_eq
    SourceSignedStressAssembly.stress B anchorRow activeH).mp hb
  funext v
  exact h v j

theorem activeH_unique (j : Fin 9) (x : SrcFree → ℝ)
    (hx : A.mulVec x=fun v => rhs v j) : x=fun v => activeH v j :=
  A_mulVec_injective (hx.trans (activeH_solve j).symm)

theorem activeH_inverse (j : Fin 9) :
    (fun v => activeH v j)=A⁻¹.mulVec (fun v => rhs v j) := by
  have h := congrArg (fun y : SrcFree → ℝ => A⁻¹.mulVec y) (activeH_solve j)
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr A_det_ne_zero),
    Matrix.one_mulVec] at h
  exact h

end
end N11Formalization.SourceActiveHarmonicSolve
#check @N11Formalization.SourceActiveHarmonicSolve.coeff_active
#check @N11Formalization.SourceActiveHarmonicSolve.activeH_solve
#check @N11Formalization.SourceActiveHarmonicSolve.activeH_unique
#check @N11Formalization.SourceActiveHarmonicSolve.activeH_inverse
#print axioms N11Formalization.SourceActiveHarmonicSolve.activeH_inverse
