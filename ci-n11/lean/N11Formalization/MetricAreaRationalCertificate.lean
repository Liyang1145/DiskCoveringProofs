import N11Formalization.ActualMetricGridBridge
import N11Formalization.IntervalsHighLag
import N11Formalization.Interval.Trig

/-! Rational production of every analytic input to the actual grid consumer.
The transcendental node inequalities follow from the existing factorial
Taylor kernel and rational arcsin upper brackets. Only finite rational
comparisons, including the final strict sum, remain for concrete tables. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaRationalCertificate

open ActualSectorAreaEnvelope ActualCircleSegmentAlgebra
open MetricAreaGridCertificate ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualBoundaryNineTies
open ActualRefinementDoubleCounting ActualRingLinkBoundaryData

def nodeQ (U : ℚ) (N : ℕ) (k : Fin (N+1)) : ℚ := U*k.val/N

def capQ (q : ℚ) : ℚ := (19/50)*max (1/2) (min 1 (sinHiNLag (q/2)))

def NodeValid (q a : ℚ) : Prop := 0 ≤ a ∧ a ≤ 1 ∧ capQ q ≤ sinLoNLag a

def edgeUpper (b q : ℚ) : ℚ := (19/50)^2*sinHiNLag q-b*q

def areaUpper (q a : ℚ) : ℚ :=
  (19/50)^2*sinHiNLag q/2+(2*a-sinLoNLag (2*a))/2

def sectorUpper (mu lam q a : ℚ) : ℚ := areaUpper q a+lam*(2*a)-mu*q

theorem nodeQ_cast (U : ℚ) (N : ℕ) (k : Fin (N+1)) :
    (nodeQ U N k : ℝ) = gridPoint (U : ℝ) N k := by
  simp only [nodeQ,gridPoint,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]

theorem capQ_bounds (q : ℚ) : (0 : ℚ) ≤ capQ q ∧ capQ q ≤ 19/50 := by
  have hlo : (1/2 : ℚ) ≤ max (1/2) (min 1 (sinHiNLag (q/2))) := le_max_left _ _
  have hhi : max (1/2 : ℚ) (min 1 (sinHiNLag (q/2))) ≤ 1 :=
    max_le (by norm_num) (min_le_left _ _)
  unfold capQ
  constructor <;> nlinarith only [hlo,hhi]

theorem width_upper_of_node {q a : ℚ} (ha : NodeValid q a) :
    widthEnvelope (q : ℝ) ≤ (2*a : ℚ) := by
  have hs : Real.sin ((q : ℝ)/2) ≤ (min 1 (sinHiNLag (q/2)) : ℚ) := by
    simp only [Rat.cast_min,Rat.cast_one]
    apply le_min (Real.sin_le_one _)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using sin_le_sinHiNLag (q/2)
  have hcap : (19/50 : ℝ)*max (1/2) (Real.sin ((q : ℝ)/2)) ≤ (capQ q : ℝ) := by
    have hm := max_le_max_left (1/2 : ℝ) hs
    unfold capQ
    push_cast at hm ⊢
    nlinarith only [hm]
  have hbox := capQ_bounds q
  have hc : (capQ q : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    have h0 : (0 : ℝ) ≤ capQ q := by exact_mod_cast hbox.1
    have h1 : (capQ q : ℝ) ≤ 19/50 := by
      have hh : (capQ q : ℝ) ≤ ((19/50 : ℚ) : ℝ) := Rat.cast_le.mpr hbox.2
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
      exact hh
    constructor <;> linarith
  have haw : (a : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have h0 : (0 : ℝ) ≤ a := by exact_mod_cast ha.1
    have h1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha.2.1
    constructor <;> linarith [Real.pi_gt_three]
  have hb : Real.arcsin (capQ q : ℝ) ≤ (a : ℝ) := by
    apply (Real.arcsin_le_iff_le_sin hc haw).mpr
    exact (show (capQ q : ℝ) ≤ (sinLoNLag a : ℝ) by exact_mod_cast ha.2.2).trans
      (sinLoNLag_le_sin a)
  have hm := (Real.arcsin_le_arcsin hcap).trans hb
  unfold widthEnvelope
  push_cast
  linarith only [hm]

theorem area_upper_of_node {q a : ℚ} (ha : NodeValid q a) :
    areaEnvelope (q : ℝ) ≤ (areaUpper q a : ℝ) := by
  have hw := width_upper_of_node ha
  have hg := segmentTerm_monotone hw
  have hq := sin_le_sinHiNLag q
  have hs := sinLoNLag_le_sin (2*a)
  unfold areaEnvelope areaUpper segmentTerm at *
  push_cast at *
  nlinarith only [hg,hq,hs]

theorem edge_upper (b q : ℚ) : edgeResidual (b : ℝ) (q : ℝ) ≤ (edgeUpper b q : ℝ) := by
  have h := sin_le_sinHiNLag q
  unfold edgeResidual edgeUpper
  push_cast
  nlinarith only [h]

theorem sector_upper {mu lam q a : ℚ} (hlam : 0 ≤ lam) (ha : NodeValid q a) :
    sectorResidual (mu : ℝ) (lam : ℝ) (q : ℝ) ≤ (sectorUpper mu lam q a : ℝ) := by
  have hf := area_upper_of_node ha
  have hw := mul_le_mul_of_nonneg_left (width_upper_of_node ha)
    (show (0 : ℝ) ≤ lam by exact_mod_cast hlam)
  unfold sectorResidual sectorUpper
  push_cast at *
  linarith only [hf,hw]

def piProductUpper (b : ℚ) : ℚ := b*(if b < 0 then RatInterval.piLo else RatInterval.piHi)

theorem pi_product_upper (b : ℚ) : (b : ℝ)*Real.pi ≤ (piProductUpper b : ℝ) := by
  unfold piProductUpper
  by_cases hb : b < 0
  · rw [if_pos hb,Rat.cast_mul]
    exact mul_le_mul_of_nonpos_left RatInterval.piLo_lt_pi.le
      (show (b : ℝ) ≤ 0 by exact_mod_cast hb.le)
  · rw [if_neg hb,Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left RatInterval.pi_lt_piHi.le
      (show (0 : ℝ) ≤ b by exact_mod_cast (not_lt.mp hb))

def totalUpper {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (mu : Fin 11 → ℚ) (lam U : ℚ) (N : ℕ)
    (edgeMax : Finset (Fin 11) → ℚ) (sectorMax : Fin 9 → ℚ) : ℚ :=
  piProductUpper (2*((∑ j : Fin 11, mu j)-lam)) +
    (∑ e ∈ edges R, (edgeMax e+((19/50 : ℚ)^2+|∑ j ∈ e, mu j|)*U/N)) +
    (∑ i : Fin 9, (sectorMax i+(1+lam+|mu (nextSite i)|)*U/N))

/-- Every input to the contradiction is an exact finite rational check.
No sampled maximum, real node bound, or strict transcendental sum is assumed. -/
theorem exclude_representative_of_rational_certificate
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r)
    (mu : Fin 11 → ℚ) (lam U : ℚ) (hlam : 0 ≤ lam)
    (hU : RatInterval.piHi ≤ U) (N : ℕ) (hN : 0 < N)
    (a : Fin (N+1) → ℚ) (ha : ∀ k, NodeValid (nodeQ U N k) (a k))
    (edgeMax : Finset (Fin 11) → ℚ) (sectorMax : Fin 9 → ℚ)
    (hedge : ∀ e ∈ edges R, ∀ k : Fin (N+1),
      edgeUpper (∑ j ∈ e, mu j) (nodeQ U N k) ≤ edgeMax e)
    (hsector : ∀ (i : Fin 9) (k : Fin (N+1)),
      sectorUpper (mu (nextSite i)) lam (nodeQ U N k) (a k) ≤ sectorMax i)
    (hstrict : totalUpper R mu lam U N edgeMax sectorMax < RatInterval.piLo) : False := by
  classical
  have hUr : Real.pi ≤ (U : ℝ) :=
    RatInterval.pi_lt_piHi.le.trans (by exact_mod_cast hU)
  have hp := pi_product_upper (2*((∑ j : Fin 11, mu j)-lam))
  have hp' : 2*Real.pi*((∑ j : Fin 11, (mu j : ℝ))-(lam : ℝ)) ≤
      (piProductUpper (2*((∑ j : Fin 11, mu j)-lam)) : ℝ) := by
    convert hp using 1 <;> push_cast <;> ring
  have ht : (totalUpper R mu lam U N edgeMax sectorMax : ℝ) < Real.pi :=
    (show (totalUpper R mu lam U N edgeMax sectorMax : ℝ) < (RatInterval.piLo : ℝ)
      by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hs : 2*Real.pi*((∑ j : Fin 11, (mu j : ℝ))-(lam : ℝ)) +
      (∑ e ∈ edges R, ((edgeMax e : ℝ)+((19/50 : ℝ)^2+|∑ j ∈ e, (mu j : ℝ)|)*(U : ℝ)/(N : ℝ))) +
      (∑ i : Fin 9, ((sectorMax i : ℝ)+(1+(lam : ℝ)+|(mu (nextSite i) : ℝ)|)*(U : ℝ)/(N : ℝ))) < Real.pi := by
    unfold totalUpper at ht
    push_cast at ht
    linarith only [hp',ht]
  apply ActualMetricGridBridge.exclude_representative_of_grid_certificate
    h hr R v (fun j => (mu j : ℝ)) (lam : ℝ) (by exact_mod_cast hlam)
    (U : ℝ) hUr N hN (fun e => (edgeMax e : ℝ)) (fun i => (sectorMax i : ℝ))
    ?_ ?_ hs
  · intro e he k
    rw [← nodeQ_cast]
    have hn := edge_upper (∑ j ∈ e, mu j) (nodeQ U N k)
    have hb : (edgeUpper (∑ j ∈ e, mu j) (nodeQ U N k) : ℝ) ≤ (edgeMax e : ℝ) :=
      by exact_mod_cast hedge e he k
    simpa only [Rat.cast_sum] using hn.trans hb
  · intro i k
    rw [← nodeQ_cast]
    exact (sector_upper hlam (ha k)).trans (by exact_mod_cast hsector i k)

end N11Formalization.MetricAreaRationalCertificate
#check @N11Formalization.MetricAreaRationalCertificate.exclude_representative_of_rational_certificate
#print axioms N11Formalization.MetricAreaRationalCertificate.width_upper_of_node
#print axioms N11Formalization.MetricAreaRationalCertificate.area_upper_of_node
#print axioms N11Formalization.MetricAreaRationalCertificate.pi_product_upper
#print axioms N11Formalization.MetricAreaRationalCertificate.exclude_representative_of_rational_certificate
