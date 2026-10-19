import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450SecondRadialControls
open C450SecondRadialKernel
def good : Packet := C450SecondRadialNeg.packet0
theorem good_valid : Valid .neg good := C450SecondRadialNeg.valid0
def badT : Packet := {good with qt := 0}
def badB : Packet := {good with qb := -1}
def badLo : Packet := {good with lo := 0}
theorem bad_t_rejected : ¬Valid .neg badT := by
  intro hp
  have hh : ¬(cosHiNLag badT.qt ≤ C450FirstRadialKernel.zQ badT.hi) := by decide +kernel
  exact hh hp.t_cos
theorem bad_beta_rejected : ¬Valid .neg badB := by
  intro hp
  have hh := hp.qb_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_domain_rejected : ¬Valid .neg badLo := by
  intro hp
  have hh := hp.lower
  change (31/50:ℚ) ≤ 0 at hh
  norm_num at hh
theorem zero_norm_coupling (e : ℝ) :
    ‖(!₂[e,0]:Point)‖^2 = ‖(!₂[e,0]:Point)-(!₂[e,0]:Point)‖^2+
      2*e*‖(!₂[e,0]:Point)-(!₂[e,0]:Point)‖*c450Cq (!₂[e,0]:Point) e+e^2 :=
  C450AngularMajorant.norm_coupling _ _
end N11Formalization.C450SecondRadialControls
#print axioms N11Formalization.C450SecondRadialControls.good_valid
#print axioms N11Formalization.C450SecondRadialControls.bad_t_rejected
#print axioms N11Formalization.C450SecondRadialControls.bad_beta_rejected
#print axioms N11Formalization.C450SecondRadialControls.bad_domain_rejected
#print axioms N11Formalization.C450SecondRadialControls.zero_norm_coupling
