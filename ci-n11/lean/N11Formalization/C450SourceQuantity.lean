import N11Formalization.C450NormalizedInterface
import N11Formalization.C450Identify
import N11Formalization.FlashTenBoundaryHper

/-! Actual normalized integrals -> source t/v/e/Bool-sign quantity.
The interval inequality is EXPLICIT, not replaced by numerical evidence. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SourceQuantity
open scoped Interval
open MeasureTheory
open C450NormalizedInterface

def rho (t : ℝ) (sign : Bool) : ℝ :=
  Real.cos t+(if sign then 1 else -1)*Real.sqrt ((19/50:ℝ)^2-(Real.sin t)^2)
def scalarEll (r v e : ℝ) : ℝ :=
  Real.sqrt ((r*v-e)^2+(r*Real.sqrt (1-v^2))^2)

theorem legal_sin_sq {t : ℝ} (ht0 : 0 ≤ t) (htR : t ≤ Real.arcsin (19/50)) :
    (Real.sin t)^2 ≤ (19/50:ℝ)^2 := by
  have hupper : Real.sin t ≤ (19/50:ℝ) := by
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ t)
      (Real.arcsin_le_pi_div_two (19/50)) htR
    rw [Real.sin_arcsin (by norm_num) (by norm_num)] at hs
    exact hs
  have hnonneg : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc
    ⟨ht0,htR.trans (by linarith [Real.arcsin_le_pi_div_two (19/50),Real.pi_pos])⟩
  nlinarith

theorem parameters {c : Point} (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50) :
    ∃ (t : ℝ) (sign : Bool), 0 ≤ t ∧ t ≤ Real.arcsin (19/50) ∧
      ‖c‖ = rho t sign ∧
      Real.arccos ((1+‖c‖^2-(19/50:ℝ)^2)/(2*‖c‖)) = t := by
  obtain ⟨t,ht0,htR,htpi,hroot⟩ := exists_t_of_rho hc0 hc1
  obtain ⟨sign,hrho⟩ : ∃ sign : Bool, ‖c‖ = rho t sign := by
    rcases hroot with hplus | hminus
    · exact ⟨true,by simpa only [rho,if_true,one_mul] using hplus⟩
    · exact ⟨false,by simpa [rho,sub_eq_add_neg] using hminus⟩
  have hn : ‖c‖ ≠ 0 := by
    have hp : 0 < ‖c‖ := by linarith
    exact hp.ne'
  have hsgn : ((if sign then 1 else -1):ℝ)^2 = 1 := by cases sign <;> norm_num
  have hR : (19:ℝ)^2/50^2 = (19/50:ℝ)^2 := by ring
  have hsin : (Real.sin t)^2 ≤ (19:ℝ)^2/50^2 := by
    rw [hR]
    exact legal_sin_sq ht0 htR
  have hroot' : ‖c‖ = Real.cos t+((if sign then 1 else -1):ℝ)*
      Real.sqrt ((19:ℝ)^2/50^2-(Real.sin t)^2) := by
    rw [hR]
    exact hrho
  have ht := halfwidth_arccos hn hsgn hsin ht0 htpi.2 hroot'
  rw [hR] at ht
  exact ⟨t,sign,ht0,htR,hrho,ht⟩

theorem direction_bounds {c : Point} (hc0 : 1-19/50 ≤ ‖c‖) :
    -1 ≤ c 0/‖c‖ ∧ c 0/‖c‖ ≤ 1 := by
  have hn : 0 < ‖c‖ := by linarith
  constructor
  · rw [le_div_iff₀ hn]
    linarith [abs_coord_le_norm c,neg_le_abs (c 0)]
  · rw [div_le_one hn]
    exact (le_abs_self _).trans (abs_coord_le_norm c)

theorem scalarEll_eq {c : Point} {v e : ℝ} (hc0 : 1-19/50 ≤ ‖c‖)
    (hv : v = c 0/‖c‖) :
    scalarEll ‖c‖ v e = ‖c-hubPt e‖ := by
  have hn : ‖c‖ ≠ 0 := by
    have hp : 0 < ‖c‖ := by linarith
    exact hp.ne'
  have hb := direction_bounds hc0
  rw [← hv] at hb
  have hrad : 0 ≤ 1-v^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-v) (by linarith : 0 ≤ 1+v)]
  have hcv : ‖c‖*v = c 0 := by
    rw [hv]
    field_simp
  have hcpow : ‖c‖^2*v^2 = (c 0)^2 := by
    rw [← mul_pow,hcv]
  have hs : (‖c‖*Real.sqrt (1-v^2))^2 = (c 1)^2 := by
    rw [mul_pow,Real.sq_sqrt hrad]
    nlinarith [norm_sq_coord c]
  have hd := norm_sq_coord (c-hubPt e)
  simp only [PiLp.sub_apply,hubPt,Matrix.cons_val_zero,Matrix.cons_val_one,sub_zero] at hd
  unfold scalarEll
  rw [hcv,hs,← hd,Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem quantity_eq (s : TenSeg)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0)
    {c : Point} {t v e : ℝ} {sign : Bool}
    (hc0 : 1-19/50 ≤ ‖c‖) (he0 : 0 ≤ e) (he7 : e ≤ 7/50)
    (hv : v = c 0/‖c‖) (hrho : ‖c‖ = rho t sign)
    (ht : Real.arccos ((1+‖c‖^2-(19/50:ℝ)^2)/(2*‖c‖)) = t) :
    c450Q s.a0 s.a1 s.a2 s.a3 s.b0 s.b1 s.b2 s.b3 t v e sign =
      c450Outer (s.W0 h0) c+c450Inner (s.W1 h1) c e := by
  have hell := scalarEll_eq hc0 hv (e := e)
  have hne : ‖c-hubPt e‖ ≠ 0 := (ell_pos_canonical he0 he7 hc0).ne'
  have hn : ‖c‖ ≠ 0 := by
    have hp : 0 < ‖c‖ := by linarith
    exact hp.ne'
  have hcv : ‖c‖*v = c 0 := by rw [hv]; field_simp
  change outerHalf (s.W0 h0) t v+
    innerHalf (s.W1 h1)
      (if scalarEll (rho t sign) v e < 2*(19/50:ℝ) then
        Real.arccos (scalarEll (rho t sign) v e/(2*(19/50:ℝ))) else 0)
      (if scalarEll (rho t sign) v e = 0 then 1 else
        (rho t sign*v-e)/scalarEll (rho t sign) v e) = _
  rw [← hrho,hell,if_neg hne,hcv]
  change outerHalf (s.W0 h0) t v+
    innerHalf (s.W1 h1) (c450B c e) (c450Cq c e) = _
  congr 1
  · unfold outerHalf c450Outer
    rw [ht,← hv]

/-- Exactly the source legal t/v/e/sign domain, no cover/symmetry premise. -/
def QuantityBound (s : TenSeg) : Prop :=
  ∀ (t v e : ℝ) (sign : Bool),
    0 ≤ t → t ≤ Real.arcsin (19/50) → -1 ≤ v → v ≤ 1 →
    0 ≤ e → (s.eLo:ℝ) ≤ e → e ≤ (s.eHi:ℝ) →
    c450Q s.a0 s.a1 s.a2 s.a3 s.b0 s.b1 s.b2 s.b3 t v e sign <
      Real.pi*((s.a0:ℝ)+(s.b0:ℝ))/10

theorem normalized_of_quantity (s : TenSeg) (hehi : s.eHi ≤ (7/50:ℚ))
    (hq : QuantityBound s)
    (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0) :
    PerDiskNormalized (s.W0 h0) (s.W1 h1) (s.eLo:ℝ) (s.eHi:ℝ) := by
  intro c e hc0 hc1 he0 helo hehigh
  have he7 : e ≤ (7/50:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hehi
    norm_num at hh
    exact hehigh.trans hh
  obtain ⟨t,sign,ht0,htR,hrho,ht⟩ := parameters hc0 hc1
  have hv := direction_bounds hc0
  have hbound := hq t (c 0/‖c‖) e sign ht0 htR hv.1 hv.2 he0 helo hehigh
  rw [quantity_eq s h0 h1 hc0 he0 he7 rfl hrho ht] at hbound
  have hp := pair_canonical (s.W0 h0) (s.W1 h1) he0 he7 hc0 hc1
  have hh := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  change 2*(c450Outer (s.W0 h0) c+c450Inner (s.W1 h1) c e) <
    2*(Real.pi*((s.W0 h0).a0+(s.W1 h1).a0)/10) at hh
  have hfinal : 2*c450Outer (s.W0 h0) c+2*c450Inner (s.W1 h1) c e <
      (2*Real.pi*(s.W0 h0).a0+2*Real.pi*(s.W1 h1).a0)/10 := by
    convert hh using 1 <;> ring
  exact hp.trans_lt hfinal

def SourceQuantityObligation : Prop := ∀ s ∈ c450Segs, QuantityBound s

theorem source_segment_hi : ∀ s ∈ c450Segs, s.eHi ≤ (7/50:ℚ) := by
  have hf : c450Segs.all (fun s => decide (s.eHi ≤ (7/50:ℚ))) = true := by decide +kernel
  have hh := (list_all_eq_true (fun s => decide (s.eHi ≤ (7/50:ℚ))) c450Segs).mp hf
  intro s hs
  exact of_decide_eq_true (hh s hs)

theorem source_of_quantity (hq : SourceQuantityObligation) : SourceObligation := by
  intro s hs h0 h1
  exact normalized_of_quantity s (source_segment_hi s hs) (hq s hs) h0 h1

theorem atom_of_quantity (hq : SourceQuantityObligation) : C450Atom :=
  atom_of_source (source_of_quantity hq)
end N11Formalization.C450SourceQuantity
#check @N11Formalization.C450SourceQuantity.parameters
#check @N11Formalization.C450SourceQuantity.quantity_eq
#check @N11Formalization.C450SourceQuantity.atom_of_quantity
#print axioms N11Formalization.C450SourceQuantity.parameters
#print axioms N11Formalization.C450SourceQuantity.quantity_eq
#print axioms N11Formalization.C450SourceQuantity.atom_of_quantity
