import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450SecondSegmentImportedAudit
open C450SecondSegment
open scoped Interval
open MeasureTheory

example : C450NormalizedInterface.SegmentNormalized second := second_paid
example : C450NormalizedInterface.SegmentNormalized C450FirstSegment.first :=
  C450FirstSegment.first_paid
theorem actual_per_disk (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (1:ℝ)/250 ≤ e) (heHi : e ≤ 71/10000) :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
  have hp := second_paid nn0 nn1
  have h0 : (second.eLo:ℝ) = (1/250:ℝ) := by norm_num [second,c450Segs]
  have h1 : (second.eHi:ℝ) = (71/10000:ℝ) := by norm_num [second,c450Segs]
  rw [h0,h1] at hp
  exact hp c e hc0 hc1 (by linarith) heLo heHi

theorem all_radial_endpoints (k : C450SecondRadialKernel.Branch) :
    C450SecondRadialKernel.model k ((31:ℝ)/50) < (C450SecondRadialKernel.cap:ℝ) ∧
    C450SecondRadialKernel.model k (C450SecondRadialKernel.finish k:ℝ) <
      (C450SecondRadialKernel.cap:ℝ) ∧
    C450SecondRadialKernel.model k ((69:ℝ)/50) < (C450SecondRadialKernel.cap:ℝ) := by
  cases k
  all_goals
    first
    | exact ⟨C450SecondRadialNeg.bound _ ⟨le_rfl,by norm_num⟩,
        C450SecondRadialKernel.far_bound .neg _ ⟨le_rfl,by norm_num [C450SecondRadialKernel.finish,C450SecondRadialKernel.F,C450SecondRadialKernel.E,C450SecondRadialKernel.R]⟩,
        C450SecondRadialNeg.bound _ ⟨by norm_num,le_rfl⟩⟩
    | exact ⟨C450SecondRadialMid.bound _ ⟨le_rfl,by norm_num⟩,
        C450SecondRadialKernel.far_bound .mid _ ⟨le_rfl,by norm_num [C450SecondRadialKernel.finish,C450SecondRadialKernel.F,C450SecondRadialKernel.E,C450SecondRadialKernel.R]⟩,
        C450SecondRadialMid.bound _ ⟨by norm_num,le_rfl⟩⟩
    | exact ⟨C450SecondRadialPos.bound _ ⟨le_rfl,by norm_num⟩,
        C450SecondRadialKernel.far_bound .pos _ ⟨le_rfl,by norm_num [C450SecondRadialKernel.finish,C450SecondRadialKernel.F,C450SecondRadialKernel.E,C450SecondRadialKernel.R]⟩,
        C450SecondRadialPos.bound _ ⟨by norm_num,le_rfl⟩⟩
example : remainingSegs.length = 34 := remaining_count
example (hr : RemainingSourceObligation) : C450Atom := atom_of_remaining hr
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450SecondSegmentImportedAudit
#print N11Formalization.C450SecondSegment.RemainingSourceObligation
#check @N11Formalization.C450AngularMajorant.normalized_of_three
#check @N11Formalization.C450SecondSegment.second_paid
#check @N11Formalization.C450SecondSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450AngularMajorant.norm_coupling
#print axioms N11Formalization.C450AngularMajorant.ell_lower
#print axioms N11Formalization.C450AngularMajorant.sin_lower
#print axioms N11Formalization.C450AngularMajorant.normalized_of_three
#print axioms N11Formalization.C450SecondRadialKernel.packet_bound
#print axioms N11Formalization.C450SecondRadialKernel.far_bound
#print axioms N11Formalization.C450SecondSegment.neg_radial_paid
#print axioms N11Formalization.C450SecondSegment.mid_radial_paid
#print axioms N11Formalization.C450SecondSegment.pos_radial_paid
#print axioms N11Formalization.C450SecondSegment.second_paid
#print axioms N11Formalization.C450SecondSegment.atom_of_remaining
#print axioms N11Formalization.C450SecondSegmentImportedAudit.actual_per_disk
#print axioms N11Formalization.C450SecondSegmentImportedAudit.all_radial_endpoints
