import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450FirstSegmentImportedAudit
open C450FirstSegment C450FirstRadialKernel
open scoped Interval
open MeasureTheory

example : C450NormalizedInterface.SegmentNormalized first := first_paid
example (c : Point) (e : ℝ) (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (he0 : 0 ≤ e) (he1 : e ≤ 1/250) :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
  have hp := first_paid nn0 nn1
  have h0 : (first.eLo:ℝ) = 0 := by norm_num [first,c450Segs]
  have h1 : (first.eHi:ℝ) = (1/250:ℝ) := by norm_num [first,c450Segs]
  rw [h0,h1] at hp
  exact hp c e hc0 hc1 he0 he0 he1
example : model ((31:ℝ)/50) < (cap:ℝ) :=
  model_bound _ ⟨le_rfl,by norm_num⟩
example : model ((191:ℝ)/250) < (cap:ℝ) :=
  model_bound _ ⟨by norm_num,by norm_num⟩
example : model ((69:ℝ)/50) < (cap:ℝ) :=
  model_bound _ ⟨by norm_num,le_rfl⟩
example (hr : RemainingSourceObligation) : C450Atom := atom_of_remaining hr
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450FirstSegmentImportedAudit
#print N11Formalization.C450FirstSegment.RemainingSourceObligation
#check @N11Formalization.C450FirstSegment.first_paid
#check @N11Formalization.C450FirstSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450RadialMajorant.inner_le_density
#print axioms N11Formalization.C450RadialMajorant.normalized_of_radial
#print axioms N11Formalization.C450FirstRadialKernel.packet_bound
#print axioms N11Formalization.C450FirstSegment.near_bound
#print axioms N11Formalization.C450FirstSegment.far_bound
#print axioms N11Formalization.C450FirstSegment.radial_paid
#print axioms N11Formalization.C450FirstSegment.first_paid
#print axioms N11Formalization.C450FirstSegment.atom_of_remaining
