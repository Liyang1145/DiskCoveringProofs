import N11Formalization.ActualSectorAreaEnvelope

/-! The finite continuous-certificate consumer for the degree-three area route.
No proposed multiplier, numerical bound, or actual graph realization is paid
by this module. Every pointwise bound covers its entire closed real domain.
The actual edge incidence/area producer is a separate geometric obligation. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaDual

open ActualSectorAreaEnvelope

def endpointAngleMass {V E : Type*} [Fintype E] [DecidableEq V]
    (p : E → V) (θ : E → ℝ) (i : V) : ℝ :=
  ∑ e : E, if p e = i then θ e else 0

theorem weighted_endpoint_sum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (p : E → V) (θ : E → ℝ) (μ : V → ℝ) :
    (∑ i : V, μ i*endpointAngleMass p θ i) = ∑ e : E, μ (p e)*θ e := by
  classical
  unfold endpointAngleMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [mul_ite, eq_comm]

theorem weighted_site_balance {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (a b : E → V) (B : Finset V) (θ : E → ℝ) (α μ : V → ℝ)
    (hsite : ∀ i : V, endpointAngleMass a θ i + endpointAngleMass b θ i +
      (if i ∈ B then α i else 0) = 2*Real.pi) :
    (∑ e : E, (μ (a e)+μ (b e))*θ e) + (∑ i ∈ B, μ i*α i) =
      2*Real.pi*(∑ i : V, μ i) := by
  classical
  have hs : (∑ i : V, μ i*(endpointAngleMass a θ i + endpointAngleMass b θ i +
      (if i ∈ B then α i else 0))) = ∑ i : V, μ i*(2*Real.pi) :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun x : ℝ => μ i*x) (hsite i))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [weighted_endpoint_sum a θ μ, weighted_endpoint_sum b θ μ] at hs
  have hb : (∑ i : V, μ i*(if i ∈ B then α i else 0)) = ∑ i ∈ B, μ i*α i := by
    simp [mul_ite, Finset.sum_ite_mem]
  rw [hb, ← Finset.sum_mul] at hs
  simp only [add_mul, Finset.sum_add_distrib]
  linarith

/-- A finite graph certificate becomes a contradiction only after real
angle balances, area/width budgets, full-domain inequalities and the strict
final rational/trigonometric bound have all been supplied. -/
theorem exclude_of_full_domain_certificate
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (a b : E → V) (B : Finset V) (θ : E → ℝ) (α : V → ℝ)
    (hθ : ∀ e : E, 0 ≤ θ e ∧ θ e ≤ Real.pi)
    (hα : ∀ i ∈ B, 0 ≤ α i ∧ α i ≤ Real.pi)
    (hsite : ∀ i : V, endpointAngleMass a θ i + endpointAngleMass b θ i +
      (if i ∈ B then α i else 0) = 2*Real.pi)
    (harea : Real.pi ≤ (19/50 : ℝ)^2*(∑ e : E, Real.sin (θ e)) +
      ∑ i ∈ B, areaEnvelope (α i))
    (hwidth : 2*Real.pi ≤ ∑ i ∈ B, widthEnvelope (α i))
    (μ : V → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (edgeUpper : E → ℝ) (sectorUpper : V → ℝ)
    (hedge : ∀ (e : E) (t : ℝ), 0 ≤ t → t ≤ Real.pi →
      (19/50 : ℝ)^2*Real.sin t-(μ (a e)+μ (b e))*t ≤ edgeUpper e)
    (hsector : ∀ i ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi →
      areaEnvelope t+lam*widthEnvelope t-μ i*t ≤ sectorUpper i)
    (hstrict : 2*Real.pi*((∑ i : V, μ i)-lam) +
      (∑ e : E, edgeUpper e) + (∑ i ∈ B, sectorUpper i) < Real.pi) : False := by
  classical
  have hbalance := weighted_site_balance a b B θ α μ hsite
  have he := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => hedge e (θ e) (hθ e).1 (hθ e).2)
  have hr := Finset.sum_le_sum (s := B)
    (fun i hi => hsector i hi (α i) (hα i hi).1 (hα i hi).2)
  have hw := mul_le_mul_of_nonneg_left hwidth hlam
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hr
  nlinarith only [hbalance,he,hr,hw,harea,hstrict]

end N11Formalization.MetricAreaDual
#check @N11Formalization.MetricAreaDual.weighted_site_balance
#check @N11Formalization.MetricAreaDual.exclude_of_full_domain_certificate
#print axioms N11Formalization.MetricAreaDual.weighted_site_balance
#print axioms N11Formalization.MetricAreaDual.exclude_of_full_domain_certificate
