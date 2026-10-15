import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450OrientationImportedAudit
open C450OrientationControl
example : seg ∈ c450Segs := member
example : ‖c‖ = (7:ℝ)/10 := norm_c
example : ‖h‖ = (7:ℝ)/50 := norm_h
example : 1-19/50 ≤ ‖c‖ ∧ ‖c‖ ≤ 1+19/50 := by
  rw [norm_c]
  norm_num
example : (seg.eLo:ℝ) ≤ ‖h‖ ∧ ‖h‖ ≤ (seg.eHi:ℝ) := by
  rw [norm_h]
  norm_num [seg,c450Segs]
example : ¬seg.PerDisk := not_perDisk
example : ¬C450PerDiskObligation := not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
end N11Formalization.C450OrientationImportedAudit
#check @N11Formalization.C450OrientationControl.not_perDisk
#check @N11Formalization.C450OrientationControl.not_obligation
#print axioms N11Formalization.C450OrientationControl.member
#print axioms N11Formalization.C450OrientationControl.norm_c
#print axioms N11Formalization.C450OrientationControl.norm_h
#print axioms N11Formalization.C450OrientationControl.outer_integral
#print axioms N11Formalization.C450OrientationControl.inner_integral
#print axioms N11Formalization.C450OrientationControl.not_perDisk
#print axioms N11Formalization.C450OrientationControl.not_obligation
