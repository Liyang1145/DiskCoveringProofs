import N11Formalization.C450SignedAngularMajorant

/-! Arbitrary closed direction cells. The actual direction partition and
continuous radial bounds remain explicit until concretely certified. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450AngularCellMajorant
open C450AngularMajorant C450SignedAngularMajorant
open C450RadialMajorant C450NormalizedInterface

structure Cell where
  lo : ℝ
  hi : ℝ

structure ValidCell (s : Cell) : Prop where
  lower : -1 ≤ s.lo
  ordered : s.lo ≤ s.hi
  upper : s.hi ≤ 1

def coefficient (W : TrigDensity) (s : Cell) : ℝ :=
  tailSup W+W.a1*(if s.lo ≤ 0 then s.lo else (4/5)*s.lo)
def offset (eLo E : ℝ) (s : Cell) : ℝ :=
  (if s.hi ≤ 0 then eLo*s.hi else E*s.hi)+E^2
def CellRadialBound (W0 W1 : TrigDensity) (eLo E : ℝ) (s : Cell) : Prop :=
  AngularRadialBound W0.a0 W1.a0 (coefficient W1 s) (offset eLo E s)
def CoversDirections {ι : Type*} (cells : ι → Cell) : Prop :=
  ∀ q ∈ Set.Icc (-1:ℝ) 1, ∃ i, q ∈ Set.Icc (cells i).lo (cells i).hi

theorem inner_pos_cell (W : TrigDensity) (ha : W.a1 ≤ 0)
    {c : Point} {e qLo : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ 3/25) (hc0 : 1-19/50 ≤ ‖c‖)
    (hq0 : 0 ≤ qLo) (hcq : qLo ≤ c450Cq c e) :
    c450Inner W c e ≤ (tailSup W+(4/5)*W.a1*qLo)*c450B c e := by
  have he7 : e ≤ 7/50 := by linarith
  have ht := inner_le_tail W he0 he7 hc0
  have hb := beta_nonneg c e
  have hlow := sin_lower hb (beta_le_one he0 heE hc0)
  have hsin0 : 0 ≤ Real.sin (c450B c e) := by linarith
  have hm := mul_le_mul_of_nonneg_left hcq hsin0
  have hm2 := mul_le_mul_of_nonpos_left hm ha
  have hm3 := mul_le_mul_of_nonneg_right hlow hq0
  have hm4 := mul_le_mul_of_nonpos_left hm3 ha
  nlinarith

theorem pos_cell_coefficient_nonneg (W : TrigDensity) (ha : W.a1 ≤ 0)
    {qLo : ℝ} (hq0 : 0 ≤ qLo) (hq1 : qLo ≤ 1) :
    0 ≤ tailSup W+(4/5)*W.a1*qLo := by
  have hh := W.hnonneg
  rw [abs_of_nonpos ha] at hh
  have htail : 0 ≤ tailSup W+W.a1 := by
    unfold tailSup
    linarith [abs_nonneg W.a2,abs_nonneg W.a3]
  have hs : 0 ≤ 1-(4/5:ℝ)*qLo := by linarith
  have hm := mul_nonneg (neg_nonneg.mpr ha) hs
  nlinarith

theorem coefficient_nonneg (W : TrigDensity) (ha : W.a1 ≤ 0)
    (s : Cell) (hv : ValidCell s) : 0 ≤ coefficient W s := by
  unfold coefficient
  split_ifs with hlo
  · exact neg_cell_coefficient_nonneg W ha hlo
  · have hh := pos_cell_coefficient_nonneg W ha
      (lt_of_not_ge hlo).le (hv.ordered.trans hv.upper)
    nlinarith

theorem inner_le_cell (W : TrigDensity) (ha : W.a1 ≤ 0)
    (s : Cell) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ 3/25) (hc0 : 1-19/50 ≤ ‖c‖)
    (hcq : s.lo ≤ c450Cq c e) :
    c450Inner W c e ≤ coefficient W s*c450B c e := by
  unfold coefficient
  split_ifs with hlo
  · exact inner_neg_cell W ha he0 (by linarith) hc0 hlo hcq
  · have hh := inner_pos_cell W ha he0 heE hc0 (lt_of_not_ge hlo).le hcq
    nlinarith

theorem beta_le_cell (s : Cell) (hv : ValidCell s)
    {c : Point} {e eLo E : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hcq : c450Cq c e ≤ s.hi) :
    c450B c e ≤ betaUpper ‖c‖ (offset eLo E s) := by
  unfold offset
  split_ifs with hhi
  · exact beta_le_signed hLo0 heLo heE hE hc0
      (hv.lower.trans hv.ordered) hhi hcq
  · exact beta_le_angular (hLo0.trans heLo) heE hE hc0
      (lt_of_not_ge hhi).le hcq

theorem pair_le_cell (W0 W1 : TrigDensity)
    (h01 : W0.a1 = 0) (h02 : W0.a2 = 0) (h03 : W0.a3 = 0)
    (h11 : W1.a1 ≤ 0) (s : Cell) (hv : ValidCell s)
    {c : Point} {e eLo E : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hcq : c450Cq c e ∈ Set.Icc s.lo s.hi) :
    c450Outer W0 c+c450Inner W1 c e ≤
      angularModel W0.a0 (coefficient W1 s) (offset eLo E s) ‖c‖ := by
  have hi := inner_le_cell W1 h11 s (hLo0.trans heLo) (heE.trans hE) hc0 hcq.1
  have hb := beta_le_cell s hv hLo0 heLo heE hE hc0 hcq.2
  have hm := mul_le_mul_of_nonneg_left hb (coefficient_nonneg W1 h11 s hv)
  unfold angularModel
  rw [outer_constant W0 h01 h02 h03]
  exact add_le_add le_rfl (hi.trans hm)

theorem normalized_of_cells {ι : Type*} (cells : ι → Cell)
    (hvalid : ∀ i, ValidCell (cells i)) (hcover : CoversDirections cells)
    (W0 W1 : TrigDensity)
    (h01 : W0.a1 = 0) (h02 : W0.a2 = 0) (h03 : W0.a3 = 0) (h11 : W1.a1 ≤ 0)
    (eLo E : ℝ) (hLo0 : 0 ≤ eLo) (hE : E ≤ 3/25)
    (hrad : ∀ i, CellRadialBound W0 W1 eLo E (cells i)) :
    PerDiskNormalized W0 W1 eLo E := by
  intro c e hc0 hc1 he0 heLo heE
  have he7 : e ≤ 7/50 := by linarith
  have hq := cq_bounds he0 he7 hc0
  obtain ⟨i,hi⟩ := hcover (c450Cq c e) hq
  have hm := pair_le_cell W0 W1 h01 h02 h03 h11 (cells i) (hvalid i)
    hLo0 heLo heE hE hc0 hi
  have hr0 : (31:ℝ)/50 ≤ ‖c‖ := by linarith
  have hr1 : ‖c‖ ≤ (69:ℝ)/50 := by linarith
  have hb := hm.trans_lt (hrad i ‖c‖ hr0 hr1)
  have hf : 2*c450Outer W0 c+2*c450Inner W1 c e <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
    nlinarith only [hb]
  exact (pair_canonical W0 W1 he0 he7 hc0 hc1).trans_lt hf
end N11Formalization.C450AngularCellMajorant
#check @N11Formalization.C450AngularCellMajorant.inner_pos_cell
#check @N11Formalization.C450AngularCellMajorant.normalized_of_cells
#print axioms N11Formalization.C450AngularCellMajorant.inner_pos_cell
#print axioms N11Formalization.C450AngularCellMajorant.pair_le_cell
#print axioms N11Formalization.C450AngularCellMajorant.normalized_of_cells
