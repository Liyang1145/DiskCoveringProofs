import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthRadialControls
open C450RadialPacketKernel C450AngularCellMajorant
def goodParams : Params := C450FourthRadialC01.params
def good : Packet := C450FourthRadialC01.packet0
theorem good_params_valid : ValidParams goodParams := C450FourthRadialC01.params_valid
theorem good_valid : Valid goodParams good := C450FourthRadialC01.valid0
def badM : Params := {goodParams with M := -1}
def badSum : Params := {goodParams with B := -goodParams.A}
def badT : Packet := {good with qt := 0}
def badB : Packet := {good with qb := -1}
def badLo : Packet := {good with lo := 0}
theorem bad_m_rejected : ¬ValidParams badM := by
  intro hp
  have hh := hp.M_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_sum_rejected : ¬ValidParams badSum := by
  intro hp
  have hh := hp.total_pos
  change (0:ℚ) < goodParams.A + -goodParams.A at hh
  norm_num at hh
theorem bad_t_rejected : ¬Valid goodParams badT := by
  intro hp
  have hh : ¬(cosHiNLag badT.qt ≤ C450FirstRadialKernel.zQ badT.hi) := by decide +kernel
  exact hh hp.t_cos
theorem bad_beta_rejected : ¬Valid goodParams badB := by
  intro hp
  have hh := hp.qb_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_domain_rejected : ¬Valid goodParams badLo := by
  intro hp
  have hh := hp.lower
  change (31/50:ℚ) ≤ 0 at hh
  norm_num at hh
def badCell : Cell := ⟨1/2,1/4⟩
theorem bad_cell_rejected : ¬ValidCell badCell := by
  intro hp
  have hh := hp.ordered
  change (1/2:ℝ) ≤ 1/4 at hh
  norm_num at hh
def incomplete : Fin 1 → Cell := fun _ => ⟨0,1/4⟩
theorem incomplete_cells_valid (i : Fin 1) : ValidCell (incomplete i) := by
  constructor <;> norm_num [incomplete]
theorem incomplete_coverage_rejected : ¬CoversDirections incomplete := by
  intro hp
  obtain ⟨i,hi⟩ := hp (-1) ⟨le_rfl,by norm_num⟩
  change (-1:ℝ) ∈ Set.Icc 0 (1/4) at hi
  norm_num at hi
end N11Formalization.C450FourthRadialControls
#print axioms N11Formalization.C450FourthRadialControls.good_params_valid
#print axioms N11Formalization.C450FourthRadialControls.good_valid
#print axioms N11Formalization.C450FourthRadialControls.bad_m_rejected
#print axioms N11Formalization.C450FourthRadialControls.bad_sum_rejected
#print axioms N11Formalization.C450FourthRadialControls.bad_t_rejected
#print axioms N11Formalization.C450FourthRadialControls.bad_beta_rejected
#print axioms N11Formalization.C450FourthRadialControls.bad_domain_rejected
#print axioms N11Formalization.C450FourthRadialControls.bad_cell_rejected
#print axioms N11Formalization.C450FourthRadialControls.incomplete_cells_valid
#print axioms N11Formalization.C450FourthRadialControls.incomplete_coverage_rejected
