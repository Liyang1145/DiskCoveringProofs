import N11Formalization.MetricAreaGridCertificate

/-! One consumer for finite node certificates and the complete real-area
contradiction. The weighted angle balance must be produced from actual
geometry. Numeric node bounds and the final strict bound remain inputs. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaGridDual

open ActualSectorAreaEnvelope MetricAreaGridCertificate

theorem exclude_of_grid_certificate
    {E I : Type*} [Fintype E] [Fintype I]
    (θ : E → ℝ) (α : I → ℝ) (c : E → ℝ) (mu : I → ℝ) (K : ℝ)
    (hθ : ∀ e : E, 0 ≤ θ e ∧ θ e ≤ Real.pi)
    (hα : ∀ i : I, 0 ≤ α i ∧ α i ≤ Real.pi)
    (hbalance : (∑ e : E, c e*θ e)+(∑ i : I, mu i*α i)=K)
    (harea : Real.pi ≤ (19/50 : ℝ)^2*(∑ e : E, Real.sin (θ e)) +
      ∑ i : I, areaEnvelope (α i))
    (hwidth : 2*Real.pi ≤ ∑ i : I, widthEnvelope (α i))
    (lam : ℝ) (hlam : 0 ≤ lam) (U : ℝ) (hU : Real.pi ≤ U)
    (N : ℕ) (hN : 0 < N) (edgeMax : E → ℝ) (sectorMax : I → ℝ)
    (hedge : ∀ (e : E) (k : Fin (N+1)),
      edgeResidual (c e) (gridPoint U N k) ≤ edgeMax e)
    (hsector : ∀ (i : I) (k : Fin (N+1)),
      sectorResidual (mu i) lam (gridPoint U N k) ≤ sectorMax i)
    (hstrict : K-2*Real.pi*lam +
      (∑ e : E, (edgeMax e+((19/50 : ℝ)^2+|c e|)*U/(N : ℝ))) +
      (∑ i : I, (sectorMax i+(1+lam+|mu i|)*U/(N : ℝ))) < Real.pi) : False := by
  classical
  have he : (∑ e : E, edgeResidual (c e) (θ e)) ≤
      ∑ e : E, (edgeMax e+((19/50 : ℝ)^2+|c e|)*U/(N : ℝ)) := by
    apply Finset.sum_le_sum
    intro e _
    exact edge_full_domain_upper_of_grid hN hU (c e) (hedge e) (θ e) (hθ e).1 (hθ e).2
  have hs : (∑ i : I, sectorResidual (mu i) lam (α i)) ≤
      ∑ i : I, (sectorMax i+(1+lam+|mu i|)*U/(N : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    exact sector_full_domain_upper_of_grid hN hU hlam (mu i) (hsector i)
      (α i) (hα i).1 (hα i).2
  have hw := mul_le_mul_of_nonneg_left hwidth hlam
  unfold edgeResidual at he
  unfold sectorResidual at hs
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib] at he hstrict
  nlinarith only [he,hs,hw,hbalance,harea,hstrict]

end N11Formalization.MetricAreaGridDual
#check @N11Formalization.MetricAreaGridDual.exclude_of_grid_certificate
#print axioms N11Formalization.MetricAreaGridDual.exclude_of_grid_certificate
