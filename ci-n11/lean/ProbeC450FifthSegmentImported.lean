import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthSegmentImportedAudit
open C450FifthSegment C450RadialPacketKernel
open scoped Interval
open MeasureTheory

example : C450NormalizedInterface.SegmentNormalized fifth := fifth_paid
example : C450NormalizedInterface.SegmentNormalized C450FirstSegment.first :=
  C450FirstSegment.first_paid
example : C450NormalizedInterface.SegmentNormalized C450SecondSegment.second :=
  C450SecondSegment.second_paid
example : C450NormalizedInterface.SegmentNormalized C450ThirdSegment.third :=
  C450ThirdSegment.third_paid
example : C450NormalizedInterface.SegmentNormalized C450FourthSegment.fourth :=
  C450FourthSegment.fourth_paid
theorem actual_per_disk (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (3:ℝ)/250 ≤ e) (heHi : e ≤ 2/125) :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
  have hp := fifth_paid nn0 nn1
  have h0 : (fifth.eLo:ℝ) = (3/250:ℝ) := by norm_num [fifth,c450Segs]
  have h1 : (fifth.eHi:ℝ) = (2/125:ℝ) := by norm_num [fifth,c450Segs]
  rw [h0,h1] at hp
  exact hp c e hc0 hc1 (by linarith) heLo heHi
theorem all_radial_endpoints (i : Case) :
    model (params i) ((31:ℝ)/50) < (cap (params i):ℝ) ∧
    model (params i) (finish (params i):ℝ) < (cap (params i):ℝ) ∧
    model (params i) ((69:ℝ)/50) < (cap (params i):ℝ) := by
  have hl : (31:ℝ)/50 ≤ (finish (params i):ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (params_valid i).finish_lower
    norm_num at hh
    exact hh
  have hu : (finish (params i):ℝ) ≤ (69:ℝ)/50 := by
    fin_cases i <;> norm_num [finish,params,C450FifthRadialC01.params,
      C450FifthRadialC02.params,C450FifthRadialC03.params,C450FifthRadialC04.params,
      C450FifthRadialC05.params,C450FifthRadialC06.params,C450FifthRadialC07.params,
      C450FifthRadialC08.params,C450FifthRadialC09.params,C450FifthRadialC10.params,
      C450FifthRadialC11.params,C450FifthRadialC12.params,C450FifthRadialC13.params,
      C450FifthRadialC14.params,C450FifthRadialC15.params,C450FifthRadialC16.params]
  exact ⟨model_bound i _ ⟨le_rfl,by norm_num⟩,
    model_bound i _ ⟨hl,hu⟩,model_bound i _ ⟨by norm_num,le_rfl⟩⟩
def cqGrid (i : Fin 17) : ℝ := -1+(i.val:ℝ)/8
theorem all_direction_endpoints (i : Fin 17) :
    ∃ j : Case, cqGrid i ∈ Set.Icc (cells j).lo (cells j).hi := by
  apply cells_cover
  fin_cases i <;> norm_num [cqGrid]
example : remainingSegs.length = 31 := remaining_count
example (hr : RemainingSourceObligation) : C450Atom := atom_of_remaining hr
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450FifthSegmentImportedAudit
#print N11Formalization.C450FifthSegment.RemainingSourceObligation
#check @N11Formalization.C450AngularCellMajorant.normalized_of_cells
#check @N11Formalization.C450FifthSegment.cells_cover
#check @N11Formalization.C450FifthSegment.fifth_paid
#check @N11Formalization.C450FifthSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450AngularCellMajorant.inner_pos_cell
#print axioms N11Formalization.C450AngularCellMajorant.coefficient_nonneg
#print axioms N11Formalization.C450AngularCellMajorant.pair_le_cell
#print axioms N11Formalization.C450AngularCellMajorant.normalized_of_cells
#print axioms N11Formalization.C450RadialPacketKernel.packet_bound
#print axioms N11Formalization.C450FifthSegment.cells_valid
#print axioms N11Formalization.C450FifthSegment.cells_cover
#print axioms N11Formalization.C450FifthSegment.params_valid
#print axioms N11Formalization.C450FifthSegment.model_eq
#print axioms N11Formalization.C450FifthSegment.radial_paid
#print axioms N11Formalization.C450FifthSegment.fifth_paid
#print axioms N11Formalization.C450FifthSegment.atom_of_remaining
#print axioms N11Formalization.C450FifthSegmentImportedAudit.actual_per_disk
#print axioms N11Formalization.C450FifthSegmentImportedAudit.all_radial_endpoints
#print axioms N11Formalization.C450FifthSegmentImportedAudit.all_direction_endpoints
