import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450ThirdSegmentImportedAudit
open C450ThirdSegment C450RadialPacketKernel
open scoped Interval
open MeasureTheory

example : C450NormalizedInterface.SegmentNormalized third := third_paid
example : C450NormalizedInterface.SegmentNormalized C450FirstSegment.first :=
  C450FirstSegment.first_paid
example : C450NormalizedInterface.SegmentNormalized C450SecondSegment.second :=
  C450SecondSegment.second_paid
theorem actual_per_disk (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (71:ℝ)/10000 ≤ e) (heHi : e ≤ 1/125) :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
  have hp := third_paid nn0 nn1
  have h0 : (third.eLo:ℝ) = (71/10000:ℝ) := by norm_num [third,c450Segs]
  have h1 : (third.eHi:ℝ) = (1/125:ℝ) := by norm_num [third,c450Segs]
  rw [h0,h1] at hp
  exact hp c e hc0 hc1 (by linarith) heLo heHi

def Endpoints (p : Params) : Prop :=
  model p ((31:ℝ)/50) < (cap p:ℝ) ∧
  model p (finish p:ℝ) < (cap p:ℝ) ∧
  model p ((69:ℝ)/50) < (cap p:ℝ)
private theorem endpoints_of_bound (p : Params) (hp : ValidParams p)
    (hb : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model p r < (cap p:ℝ))
    (hf : (finish p:ℝ) ≤ (69:ℝ)/50) : Endpoints p := by
  have hl : (31:ℝ)/50 ≤ (finish p:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hp.finish_lower
    norm_num at hh
    exact hh
  exact ⟨hb _ ⟨le_rfl,by norm_num⟩,hb _ ⟨hl,hf⟩,hb _ ⟨by norm_num,le_rfl⟩⟩
theorem neg1_endpoints : Endpoints C450ThirdRadialNeg1.params :=
  endpoints_of_bound _ C450ThirdRadialNeg1.params_valid C450ThirdRadialNeg1.bound
    (by norm_num [finish,C450ThirdRadialNeg1.params])
theorem neg2_endpoints : Endpoints C450ThirdRadialNeg2.params :=
  endpoints_of_bound _ C450ThirdRadialNeg2.params_valid C450ThirdRadialNeg2.bound
    (by norm_num [finish,C450ThirdRadialNeg2.params])
theorem mid_endpoints : Endpoints C450ThirdRadialMid.params :=
  endpoints_of_bound _ C450ThirdRadialMid.params_valid C450ThirdRadialMid.bound
    (by norm_num [finish,C450ThirdRadialMid.params])
theorem pos_endpoints : Endpoints C450ThirdRadialPos.params :=
  endpoints_of_bound _ C450ThirdRadialPos.params_valid C450ThirdRadialPos.bound
    (by norm_num [finish,C450ThirdRadialPos.params])
example : remainingSegs.length = 33 := remaining_count
example (hr : RemainingSourceObligation) : C450Atom := atom_of_remaining hr
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450ThirdSegmentImportedAudit
#print N11Formalization.C450ThirdSegment.RemainingSourceObligation
#check @N11Formalization.C450SignedAngularMajorant.normalized_of_four
#check @N11Formalization.C450ThirdSegment.third_paid
#check @N11Formalization.C450ThirdSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450SignedAngularMajorant.ell_lower_signed
#print axioms N11Formalization.C450SignedAngularMajorant.inner_neg_cell
#print axioms N11Formalization.C450SignedAngularMajorant.normalized_of_four
#print axioms N11Formalization.C450RadialPacketKernel.packet_bound
#print axioms N11Formalization.C450RadialPacketKernel.closed_of_near
#print axioms N11Formalization.C450ThirdSegment.neg1_radial_paid
#print axioms N11Formalization.C450ThirdSegment.neg2_radial_paid
#print axioms N11Formalization.C450ThirdSegment.mid_radial_paid
#print axioms N11Formalization.C450ThirdSegment.pos_radial_paid
#print axioms N11Formalization.C450ThirdSegment.third_paid
#print axioms N11Formalization.C450ThirdSegment.atom_of_remaining
#print axioms N11Formalization.C450ThirdSegmentImportedAudit.actual_per_disk
#print axioms N11Formalization.C450ThirdSegmentImportedAudit.neg1_endpoints
#print axioms N11Formalization.C450ThirdSegmentImportedAudit.neg2_endpoints
#print axioms N11Formalization.C450ThirdSegmentImportedAudit.mid_endpoints
#print axioms N11Formalization.C450ThirdSegmentImportedAudit.pos_endpoints
