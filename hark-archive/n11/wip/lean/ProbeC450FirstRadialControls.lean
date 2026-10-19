import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450FirstRadialControls
open C450FirstRadialKernel
def good : Packet := C450FirstRadialG01.packet0
theorem good_valid : Valid good := C450FirstRadialG01.valid0
def badT : Packet := {good with qt := 0}
def badB : Packet := {good with qb := -1}
def badLo : Packet := {good with lo := 0}
theorem bad_t_rejected : ¬Valid badT := by
  intro hp
  have hh : ¬(cosHiNLag badT.qt ≤ zQ badT.hi) := by decide +kernel
  exact hh hp.t_cos
theorem bad_beta_rejected : ¬Valid badB := by
  intro hp
  have hh := hp.qb_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_domain_rejected : ¬Valid badLo := by
  intro hp
  have hh := hp.lower
  change (31/50:ℚ) ≤ 0 at hh
  norm_num at hh
end N11Formalization.C450FirstRadialControls
#print axioms N11Formalization.C450FirstRadialControls.good_valid
#print axioms N11Formalization.C450FirstRadialControls.bad_t_rejected
#print axioms N11Formalization.C450FirstRadialControls.bad_beta_rejected
#print axioms N11Formalization.C450FirstRadialControls.bad_domain_rejected
