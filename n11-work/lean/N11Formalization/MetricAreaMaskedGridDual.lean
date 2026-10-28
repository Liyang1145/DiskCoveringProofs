import N11Formalization.MetricAreaGridCertificate

/-! A closed-grid area dual with an additional width budget on an arbitrary
finite mask. The extra multiplier is nonnegative and its geometric budget
must be produced by an actual consumer; no numerical class is certified here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaMaskedGridDual
open ActualSectorAreaEnvelope MetricAreaGridCertificate

def widthMultiplier {I : Type*} [DecidableEq I] (J : Finset I)
    (lam eta : ℝ) (i : I) : ℝ := lam+if i ∈ J then eta else 0

theorem widthMultiplier_nonneg {I : Type*} [DecidableEq I] (J : Finset I)
    {lam eta : ℝ} (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (i : I) :
    0 ≤ widthMultiplier J lam eta i := by
  unfold widthMultiplier
  split_ifs <;> linarith

theorem masked_width_sum {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I) (lam eta : ℝ) (w : I → ℝ) :
    (∑ i : I, widthMultiplier J lam eta i*w i) =
      lam*(∑ i : I, w i)+eta*(∑ i ∈ J, w i) := by
  have hi (i : I) : widthMultiplier J lam eta i*w i =
      lam*w i+(if i ∈ J then eta*w i else 0) := by
    unfold widthMultiplier
    split_ifs <;> ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib,Finset.sum_ite_mem_eq,← Finset.mul_sum,← Finset.mul_sum]

theorem masked_width_budget {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I) (α : I → ℝ) (B : ℝ) {lam eta : ℝ}
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hwidth : 2*Real.pi ≤ ∑ i : I, widthEnvelope (α i))
    (hmask : 2*Real.pi-2*B ≤ ∑ i ∈ J, widthEnvelope (α i)) :
    2*Real.pi*lam+(2*Real.pi-2*B)*eta ≤
      ∑ i : I, widthMultiplier J lam eta i*widthEnvelope (α i) := by
  rw [masked_width_sum]
  have h1 := mul_le_mul_of_nonneg_left hwidth hlam
  have h2 := mul_le_mul_of_nonneg_left hmask heta
  nlinarith only [h1,h2]

theorem exclude_of_masked_grid_certificate
    {E I : Type*} [Fintype E] [Fintype I] [DecidableEq I]
    (θ : E → ℝ) (α : I → ℝ) (c : E → ℝ) (mu : I → ℝ) (K : ℝ)
    (hθ : ∀ e : E, 0 ≤ θ e ∧ θ e ≤ Real.pi)
    (hα : ∀ i : I, 0 ≤ α i ∧ α i ≤ Real.pi)
    (hbalance : (∑ e : E, c e*θ e)+(∑ i : I, mu i*α i)=K)
    (harea : Real.pi ≤ (19/50 : ℝ)^2*(∑ e : E, Real.sin (θ e))+
      ∑ i : I, areaEnvelope (α i))
    (hwidth : 2*Real.pi ≤ ∑ i : I, widthEnvelope (α i))
    (J : Finset I) (B : ℝ)
    (hmask : 2*Real.pi-2*B ≤ ∑ i ∈ J, widthEnvelope (α i))
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (U : ℝ) (hU : Real.pi ≤ U) (N : ℕ) (hN : 0 < N)
    (edgeMax : E → ℝ) (sectorMax : I → ℝ)
    (hedge : ∀ (e : E) (k : Fin (N+1)),
      edgeResidual (c e) (gridPoint U N k) ≤ edgeMax e)
    (hsector : ∀ (i : I) (k : Fin (N+1)),
      sectorResidual (mu i) (widthMultiplier J lam eta i) (gridPoint U N k) ≤ sectorMax i)
    (hstrict : K-2*Real.pi*lam-(2*Real.pi-2*B)*eta +
      (∑ e : E, (edgeMax e+((19/50 : ℝ)^2+|c e|)*U/(N : ℝ))) +
      (∑ i : I, (sectorMax i+(1+widthMultiplier J lam eta i+|mu i|)*U/(N : ℝ))) < Real.pi) :
    False := by
  classical
  have he : (∑ e : E, edgeResidual (c e) (θ e)) ≤
      ∑ e : E, (edgeMax e+((19/50 : ℝ)^2+|c e|)*U/(N : ℝ)) := by
    apply Finset.sum_le_sum
    intro e _
    exact edge_full_domain_upper_of_grid hN hU (c e) (hedge e) (θ e) (hθ e).1 (hθ e).2
  have hs : (∑ i : I, sectorResidual (mu i) (widthMultiplier J lam eta i) (α i)) ≤
      ∑ i : I, (sectorMax i+(1+widthMultiplier J lam eta i+|mu i|)*U/(N : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    exact sector_full_domain_upper_of_grid hN hU (widthMultiplier_nonneg J hlam heta i)
      (mu i) (hsector i) (α i) (hα i).1 (hα i).2
  have hw := masked_width_budget J α B hlam heta hwidth hmask
  unfold edgeResidual at he
  unfold sectorResidual at hs
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at he
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hs
  simp only [Finset.sum_add_distrib] at he hstrict
  nlinarith only [he,hs,hw,hbalance,harea,hstrict]

end N11Formalization.MetricAreaMaskedGridDual
#check @N11Formalization.MetricAreaMaskedGridDual.exclude_of_masked_grid_certificate
#print axioms N11Formalization.MetricAreaMaskedGridDual.masked_width_budget
#print axioms N11Formalization.MetricAreaMaskedGridDual.exclude_of_masked_grid_certificate
