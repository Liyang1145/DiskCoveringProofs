import N11Formalization.FlashCosineLeaf284Oracle
import N11Formalization.SourceChartIsometry
import N11Formalization.EnergyCommonChart

/-! Generic checked integer harmonic witnesses on the ACTUAL canonical51 graph.
Valid is explicit until instantiated by kernel-paid integer rows. No host
solver, matrix invertibility, recorded weight, or oracle assumption is used. -/
set_option autoImplicit false
namespace N11Formalization.CertifiedHarmonicField
open Finset ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeSchurEnergy
open FlashCosineLeaf284Bridge (iOf jOf)
set_option maxRecDepth 10000

structure Packet where
  mass : ℤ
  denominator : ℤ
  edgeNumerator : Fin 51 → ℤ
  harmonicNumerator : Fin 22 → Fin 9 → ℤ
  weightNumerator : Fin 36 → ℤ
  weightDenominator : Fin 36 → ℤ
abbrev Field := Packet
def A (f : Field) : ℤ := f.mass
def D (f : Field) : ℤ := f.denominator
def aV (f : Field) : Fin 51 → ℤ := f.edgeNumerator
def HV (f : Field) : Fin 22 → Fin 9 → ℤ := f.harmonicNumerator
def wNum (f : Field) : Fin 36 → ℤ := f.weightNumerator
def wDen (f : Field) : Fin 36 → ℤ := f.weightDenominator
def edgeIdx : Edge → Fin 51
  | .inl (i, s) => ⟨2 * i.val + s.val, by omega⟩
  | .inr (f, v) => ⟨18 + 3 * f.val + v.val, by omega⟩
def freeIdx : Free → Fin 22
  | .inl s => ⟨s.val, by omega⟩
  | .inr f => ⟨11 + f.val, by omega⟩
def aZ (f : Field) (e : Edge) : ℤ := aV f (edgeIdx e)
def HZ (f : Field) (v : Free) (j : Fin 9) : ℤ := HV f (freeIdx v) j
def incZ : Edge → Free → ℤ
  | .inl (i, _), v => if v = .inl ⟨i.val, by omega⟩ then 1 else 0
  | .inr (f, j), v => (if v = .inl (face f j) then 1 else 0) - (if v = .inr f then 1 else 0)
/-- Edge coefficients are defined from the harmonic matrix and actual network. -/
def bZ (f : Field) : Edge → Fin 9 → ℤ
  | .inl (i, side), j => HZ f (.inl ⟨i.val, by omega⟩) j - (if j = anchorIndex i side then D f else 0)
  | .inr (g, k), j => HZ f (.inl (face g k)) j - HZ f (.inr g) j


structure Valid (f : Field) : Prop where
  mass_pos : 0 < A f
  denominator_pos : 0 < D f
  edge_pos : ∀ e : Edge, 0 < aZ f e
  mass_sum : ∑ e : Edge, aZ f e = A f
  harmonic_row : ∀ v : Free, ∑ j : Fin 9, HZ f v j = D f
  balance : ∀ v : Free, ∀ j : Fin 9,
    ∑ e : Edge, aZ f e * incZ e v * bZ f e j = 0
  weights : ∀ k : Fin 36,
    (∑ e : Edge, aZ f e * bZ f e (iOf k) * bZ f e (jOf k)) * wDen f k =
      -(wNum f k) * A f * D f * D f
  weight_denominator_pos : ∀ k : Fin 36, 0 < wDen f k

theorem A_pos (f : Field) (hf : Valid f) : 0 < A f := hf.mass_pos
theorem D_pos (f : Field) (hf : Valid f) : 0 < D f := hf.denominator_pos
theorem a_pos (f : Field) (hf : Valid f) : ∀ e : Edge, 0 < aZ f e := hf.edge_pos
theorem a_sum (f : Field) (hf : Valid f) : ∑ e : Edge, aZ f e = A f := hf.mass_sum
theorem H_row (f : Field) (hf : Valid f) : ∀ v : Free, ∑ j : Fin 9, HZ f v j = D f :=
  hf.harmonic_row
theorem bal_all (f : Field) (hf : Valid f) : ∀ v : Free, ∀ j : Fin 9,
    ∑ e : Edge, aZ f e * incZ e v * bZ f e j = 0 := hf.balance
theorem weight_identity (f : Field) (hf : Valid f) : ∀ k : Fin 36,
    (∑ e : Edge, aZ f e * bZ f e (iOf k) * bZ f e (jOf k)) * wDen f k =
      -(wNum f k) * A f * D f * D f := hf.weights
theorem den_pos (f : Field) (hf : Valid f) : ∀ k : Fin 36, 0 < wDen f k :=
  hf.weight_denominator_pos

noncomputable def αR (f : Field) (e : Edge) : ℝ := (aZ f e : ℝ) / (A f : ℝ)
noncomputable def HR (f : Field) (v : Free) (j : Fin 9) : ℝ := (HZ f v j : ℝ) / (D f : ℝ)
noncomputable def weight (f : Field) (k : Fin 36) : ℝ := (wNum f k : ℝ) / (wDen f k : ℝ)

theorem A_ne (f : Field) (hf : Valid f) : (A f : ℝ) ≠ 0 := by exact_mod_cast (A_pos f hf).ne'
theorem D_ne (f : Field) (hf : Valid f) : (D f : ℝ) ≠ 0 := by exact_mod_cast (D_pos f hf).ne'

theorem inc_cast (e : Edge) (v : Free) : ((incZ e v : ℤ) : ℝ) = incidence e v := by
  rcases e with ⟨i, s⟩ | ⟨f, j⟩ <;> simp [incZ, incidence]

theorem coeff_eq (f : Field) (hf : Valid f) (e : Edge) (j : Fin 9) :
    coeff (HR f) e j = (bZ f e j : ℝ) / (D f : ℝ) := by
  have hD := D_ne f hf
  rcases e with ⟨i, side⟩ | ⟨g, k⟩
  · simp only [coeff, bZ, HR]
    split_ifs
    all_goals (push_cast; field_simp)
    all_goals ring
  · simp only [coeff, bZ, HR]
    push_cast
    field_simp

theorem hα (f : Field) (hf : Valid f) : ∀ e, 0 ≤ αR f e := fun e =>
  div_nonneg (by exact_mod_cast (a_pos f hf e).le) (by exact_mod_cast (A_pos f hf).le)

theorem hs (f : Field) (hf : Valid f) : ∑ e, αR f e = 1 := by
  simp only [αR]
  rw [← Finset.sum_div]
  have h : (∑ e, (aZ f e : ℝ)) = (A f : ℝ) := by exact_mod_cast a_sum f hf
  rw [h, div_self (A_ne f hf)]

theorem hbal (f : Field) (hf : Valid f) : ∀ v j, ∑ e, (αR f e * incidence e v) * coeff (HR f) e j = 0 := by
  intro v j
  have hc : ((∑ e, aZ f e * incZ e v * bZ f e j : ℤ) : ℝ) = 0 := by exact_mod_cast bal_all f hf v j
  push_cast at hc
  have hr : ∀ e, (αR f e * incidence e v) * coeff (HR f) e j =
      ((aZ f e : ℝ) * (incZ e v : ℝ) * (bZ f e j : ℝ)) / ((A f : ℝ) * (D f : ℝ)) := by
    intro e; rw [coeff_eq f hf, ← inc_cast, αR]; ring
  simp_rw [hr, ← Finset.sum_div, hc, zero_div]

theorem hH (f : Field) (hf : Valid f) : ∀ v, ∑ j, HR f v j = 1 := by
  intro v
  simp only [HR]
  rw [← Finset.sum_div]
  have h : (∑ j, (HZ f v j : ℝ)) = (D f : ℝ) := by exact_mod_cast H_row f hf v
  rw [h, div_self (D_ne f hf)]

theorem weight_eq_neg_gram (f : Field) (hf : Valid f) (k : Fin 36) :
    weight f k = -gram (αR f) (HR f) (iOf k) (jOf k) := by
  have hW : (wDen f k : ℝ) ≠ 0 := by exact_mod_cast (den_pos f hf k).ne'
  have he : gram (αR f) (HR f) (iOf k) (jOf k) =
      (∑ e, (aZ f e : ℝ) * (bZ f e (iOf k) : ℝ) * (bZ f e (jOf k) : ℝ)) /
      ((A f : ℝ) * (D f : ℝ) * (D f : ℝ)) := by
    simp only [gram, αR, coeff_eq f hf]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hw : (∑ e, (aZ f e : ℝ) * (bZ f e (iOf k) : ℝ) * (bZ f e (jOf k) : ℝ)) *
      (wDen f k : ℝ) = -(wNum f k : ℝ) * A f * D f * D f := by
    exact_mod_cast weight_identity f hf k
  rw [he, weight]
  rw [← neg_div, div_eq_div_iff hW (mul_ne_zero (mul_ne_zero (A_ne f hf) (D_ne f hf)) (D_ne f hf))]
  nlinarith only [hw]

/-- Actual 36 unordered pairs equal the upper triangular double sum. -/
theorem pairs_to_double (g : Fin 9 → Fin 9 → ℝ) :
    (∑ k : Fin 36, g (iOf k) (jOf k)) = ∑ i, ∑ j, if i < j then g i j else 0 :=
  FlashCosineLeaf284Oracle.pairs_to_double g

noncomputable def fieldEnergy (f : Field) (θ : Fin 9 → ℝ) : ℝ :=
  2 * ∑ k : Fin 36, weight f k * (1 - Real.cos (θ (iOf k) - θ (jOf k)))

/-- A complete source-field-to-oracle consumer, with no stationarity premise. -/
theorem source_energy_le_oracle (f : Field) (hf : Valid f) (θ : Fin 9 → ℝ) :
    fieldEnergy f θ ≤ V2 (fun j => circleMap (θ j)) := by
  unfold fieldEnergy
  simp_rw [weight_eq_neg_gram f hf]
  rw [pairs_to_double (fun i j => -gram (αR f) (HR f) i j * (1 - Real.cos (θ i - θ j)))]
  exact cosine_energy_le_oracle (αR f) (HR f) (hα f hf) (hs f hf) (hbal f hf) (hH f hf) θ


theorem chart_energy_le_oracle (f : Field) (hf : Valid f) (y : Fin 9 → ℝ) :
    fieldEnergy f (FlashCosine.theta y) ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have h := source_energy_le_oracle f hf (FlashCosine.theta y)
  rw [EnergyCommonChart.anchors_identity] at h
  exact h
end N11Formalization.CertifiedHarmonicField
#check @N11Formalization.CertifiedHarmonicField.source_energy_le_oracle
#check @N11Formalization.CertifiedHarmonicField.chart_energy_le_oracle
#print axioms N11Formalization.CertifiedHarmonicField.source_energy_le_oracle
#print axioms N11Formalization.CertifiedHarmonicField.chart_energy_le_oracle
