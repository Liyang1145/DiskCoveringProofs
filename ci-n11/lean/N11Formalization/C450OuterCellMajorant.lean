import N11Formalization.C450OuterGeometry

/-! Genuine sign-aware NONCONSTANT outer density cell majorant.
Actual capacity remains pi*(W0.a0+W1.a0)/10, not the outer envelope mean. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450OuterCellMajorant
open C450OuterGeometry C450AngularCellMajorant C450AngularMajorant
open C450RadialMajorant C450NormalizedInterface

def signedFactor (k p : ℝ) : ℝ := if p ≤ 0 then p else k*p
def firstCoeff (W : TrigDensity) (q : ℝ) : ℝ := W.a1*signedFactor (97/100) q
def secondCoeff (W : TrigDensity) (q : ℝ) : ℝ :=
  if q < 0 then |W.a2| else W.a2*signedFactor (4/5) (P2 q)
def thirdCoeff (W : TrigDensity) (q : ℝ) : ℝ :=
  if q < 1/2 then |W.a3| else W.a3*signedFactor (3/4) (P3 q)
def outerCoefficient (W : TrigDensity) (s : Cell) : ℝ :=
  W.a0+firstCoeff W s.lo+secondCoeff W s.lo+thirdCoeff W s.lo

theorem signed_harmonic {a t s w p k : ℝ}
    (ha : a ≤ 0) (hs0 : 0 ≤ s) (hsHi : s ≤ t) (hsLo : k*t ≤ s)
    (hpw : p ≤ w) :
    a*s*w ≤ a*signedFactor k p*t := by
  have hstep := mul_le_mul_of_nonpos_left
    (mul_le_mul_of_nonneg_left hpw hs0) ha
  unfold signedFactor
  split_ifs with hp0
  · have hap : 0 ≤ a*p := mul_nonneg_of_nonpos_of_nonpos ha hp0
    have hh := mul_le_mul_of_nonneg_left hsHi hap
    nlinarith
  · have hap : a*p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha (lt_of_not_ge hp0).le
    have hh := mul_le_mul_of_nonpos_left hsLo hap
    nlinarith

theorem outer_le_cell (W : TrigDensity)
    (h1 : W.a1 ≤ 0) (h2 : W.a2 ≤ 0) (h3 : W.a3 ≤ 0)
    (s : Cell) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (hcq : s.lo ≤ c450Cq c e) :
    c450Outer W c ≤ outerCoefficient W s*outerT c := by
  have ht := outer_t_bounds hc0 hc1
  have hvq : s.lo ≤ outerV c := hcq.trans (inner_cq_le_outer_v he0 he7 hc0)
  have hcp : 0 < ‖c‖ := by linarith
  obtain ⟨phi,hcos,_⟩ := exists_angle_of_point c (norm_pos_iff.mp hcp)
  have hg : Real.cos phi = outerV c := by simpa [outerV] using hcos
  have hc2 : Real.cos (2*phi) = P2 (outerV c) := by
    simpa [P2] using cos_two_mul_of_cos hg
  have hc3 : Real.cos (3*phi) = P3 (outerV c) := by
    simpa [P3] using cos_three_mul_of_cos hg
  have hs1 : 0 ≤ Real.sin (outerT c) := by
    simpa using sin_scaled_nonneg ht.1 ht.2 (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
  have hsHi1 : Real.sin (outerT c) ≤ outerT c := by
    simpa using sin_scaled_upper ht.1 (by norm_num : (0:ℝ) ≤ 1)
  have hH1 : W.a1*Real.sin (outerT c)*outerV c ≤ firstCoeff W s.lo*outerT c :=
    signed_harmonic h1 hs1 hsHi1 (sin97 ht.1 ht.2) hvq
  have hraw2 := harmonic_le W.a2 2 (outerT c) phi (by norm_num) ht.1
  have hraw3 := harmonic_le W.a3 3 (outerT c) phi (by norm_num) ht.1
  rw [hc2] at hraw2
  rw [hc3] at hraw3
  have hH2 : W.a2*Real.sin (2*outerT c)*P2 (outerV c)/2 ≤ secondCoeff W s.lo*outerT c := by
    unfold secondCoeff
    split_ifs with hq0
    · exact hraw2
    · have hq0' : 0 ≤ s.lo := le_of_not_gt hq0
      have hs0 : 0 ≤ Real.sin (2*outerT c)/2 :=
        div_nonneg (sin_scaled_nonneg ht.1 ht.2 (by norm_num : (0:ℝ) ≤ 2) (by norm_num))
          (by norm_num)
      have hsHi : Real.sin (2*outerT c)/2 ≤ outerT c := by
        nlinarith only [sin_scaled_upper ht.1 (by norm_num : (0:ℝ) ≤ 2)]
      have hsLo : (4/5:ℝ)*outerT c ≤ Real.sin (2*outerT c)/2 := by
        nlinarith only [sin2_lower ht.1 ht.2]
      have hh := signed_harmonic h2 hs0 hsHi hsLo (P2_le hq0' hvq)
      have heq : W.a2*(Real.sin (2*outerT c)/2)*P2 (outerV c) =
          W.a2*Real.sin (2*outerT c)*P2 (outerV c)/2 := by ring
      rw [heq] at hh
      exact hh
  have hH3 : W.a3*Real.sin (3*outerT c)*P3 (outerV c)/3 ≤ thirdCoeff W s.lo*outerT c := by
    unfold thirdCoeff
    split_ifs with hqHalf
    · exact hraw3
    · have hqHalf' : (1:ℝ)/2 ≤ s.lo := le_of_not_gt hqHalf
      have hs0 : 0 ≤ Real.sin (3*outerT c)/3 :=
        div_nonneg (sin_scaled_nonneg ht.1 ht.2 (by norm_num : (0:ℝ) ≤ 3) (by norm_num))
          (by norm_num)
      have hsHi : Real.sin (3*outerT c)/3 ≤ outerT c := by
        nlinarith only [sin_scaled_upper ht.1 (by norm_num : (0:ℝ) ≤ 3)]
      have hsLo : (3/4:ℝ)*outerT c ≤ Real.sin (3*outerT c)/3 := by
        nlinarith only [sin3_lower ht.1 ht.2]
      have hh := signed_harmonic h3 hs0 hsHi hsLo (P3_le hqHalf' hvq)
      have heq : W.a3*(Real.sin (3*outerT c)/3)*P3 (outerV c) =
          W.a3*Real.sin (3*outerT c)*P3 (outerV c)/3 := by ring
      rw [heq] at hh
      exact hh
  change W.a0*outerT c+W.a1*Real.sin (outerT c)*outerV c+
    W.a2*Real.sin (2*outerT c)*P2 (outerV c)/2+
    W.a3*Real.sin (3*outerT c)*P3 (outerV c)/3 ≤ outerCoefficient W s*outerT c
  unfold outerCoefficient
  nlinarith only [hH1,hH2,hH3]

def CellModel (W0 W1 : TrigDensity) (eLo E : ℝ) (s : Cell) (r : ℝ) : ℝ :=
  angularModel (outerCoefficient W0 s) (coefficient W1 s) (offset eLo E s) r
def CellRadialBound (W0 W1 : TrigDensity) (eLo E : ℝ) (s : Cell) : Prop :=
  ∀ r : ℝ, 31/50 ≤ r → r ≤ 69/50 →
    CellModel W0 W1 eLo E s r < Real.pi*(W0.a0+W1.a0)/10

theorem pair_le_cell (W0 W1 : TrigDensity)
    (h01 : W0.a1 ≤ 0) (h02 : W0.a2 ≤ 0) (h03 : W0.a3 ≤ 0) (h11 : W1.a1 ≤ 0)
    (s : Cell) (hv : ValidCell s) {c : Point} {e eLo E : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (hcq : c450Cq c e ∈ Set.Icc s.lo s.hi) :
    c450Outer W0 c+c450Inner W1 c e ≤ CellModel W0 W1 eLo E s ‖c‖ := by
  have he0 := hLo0.trans heLo
  have he7 : e ≤ 7/50 := by linarith
  have ho := outer_le_cell W0 h01 h02 h03 s he0 he7 hc0 hc1 hcq.1
  have hi := inner_le_cell W1 h11 s he0 (heE.trans hE) hc0 hcq.1
  have hb := beta_le_cell s hv hLo0 heLo heE hE hc0 hcq.2
  have hm := mul_le_mul_of_nonneg_left hb (coefficient_nonneg W1 h11 s hv)
  exact add_le_add ho (hi.trans hm)

/-- Complete direction/radial certification remains explicit. The outer
harmonics are NOT assumed zero, and the actual source capacity is unchanged. -/
theorem normalized_of_cells {ι : Type*} (cells : ι → Cell)
    (hvalid : ∀ i, ValidCell (cells i)) (hcover : CoversDirections cells)
    (W0 W1 : TrigDensity)
    (h01 : W0.a1 ≤ 0) (h02 : W0.a2 ≤ 0) (h03 : W0.a3 ≤ 0) (h11 : W1.a1 ≤ 0)
    (eLo E : ℝ) (hLo0 : 0 ≤ eLo) (hE : E ≤ 3/25)
    (hrad : ∀ i, CellRadialBound W0 W1 eLo E (cells i)) :
    PerDiskNormalized W0 W1 eLo E := by
  intro c e hc0 hc1 he0 heLo heE
  have he7 : e ≤ 7/50 := by linarith
  obtain ⟨i,hi⟩ := hcover (c450Cq c e) (cq_bounds he0 he7 hc0)
  have hm := pair_le_cell W0 W1 h01 h02 h03 h11 (cells i) (hvalid i)
    hLo0 heLo heE hE hc0 hc1 hi
  have hr0 : (31:ℝ)/50 ≤ ‖c‖ := by linarith
  have hr1 : ‖c‖ ≤ (69:ℝ)/50 := by linarith
  have hb := hm.trans_lt (hrad i ‖c‖ hr0 hr1)
  have hf : 2*c450Outer W0 c+2*c450Inner W1 c e <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
    nlinarith only [hb]
  exact (pair_canonical W0 W1 he0 he7 hc0 hc1).trans_lt hf
end N11Formalization.C450OuterCellMajorant
#check @N11Formalization.C450OuterCellMajorant.outer_le_cell
#check @N11Formalization.C450OuterCellMajorant.normalized_of_cells
#print axioms N11Formalization.C450OuterCellMajorant.signed_harmonic
#print axioms N11Formalization.C450OuterCellMajorant.outer_le_cell
#print axioms N11Formalization.C450OuterCellMajorant.normalized_of_cells
