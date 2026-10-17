import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthSegmentImportedAudit
open C450SixthSegment C450SixthAnalytic C450RadialPacketKernel
open scoped Interval
open MeasureTheory

example : C450NormalizedInterface.SegmentNormalized sixth := sixth_paid
example : C450NormalizedInterface.SegmentNormalized C450FifthSegment.fifth :=
  C450FifthSegment.fifth_paid
theorem actual_per_disk (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (2:ℝ)/125 ≤ e) (heHi : e ≤ 1/50) :
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
  have hp := sixth_paid nn0 nn1
  have h0 : (sixth.eLo:ℝ) = (2/125:ℝ) := by norm_num [sixth,c450Segs]
  have h1 : (sixth.eHi:ℝ) = (1/50:ℝ) := by norm_num [sixth,c450Segs]
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
  have huQ : ∀ j : Case, finish (params j) ≤ (69/50:ℚ) := by decide +kernel
  have hu : (finish (params i):ℝ) ≤ (69:ℝ)/50 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (huQ i)
    norm_num at hh
    exact hh
  exact ⟨model_bound i _ ⟨le_rfl,by norm_num⟩,
    model_bound i _ ⟨hl,hu⟩,model_bound i _ ⟨by norm_num,le_rfl⟩⟩
def cqGrid (i : Fin 65) : ℝ := -1+(i.val:ℝ)/32
theorem all_direction_endpoints (i : Fin 65) :
    ∃ j : Case, cqGrid i ∈ Set.Icc (cells j).lo (cells j).hi := by
  apply cells_cover
  have hi : (i.val:ℝ) ≤ 64 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hl : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  constructor <;> unfold cqGrid <;> linarith
example : remainingSegs.length = 30 := remaining_count
example (hr : RemainingSourceObligation) : C450Atom := atom_of_remaining hr
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450SixthSegmentImportedAudit
#print N11Formalization.C450SixthSegment.RemainingSourceObligation
#check @N11Formalization.C450SixthSegment.cells_cover
#check @N11Formalization.C450SixthSegment.sixth_paid
#check @N11Formalization.C450SixthSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450OuterGeometry.inner_cq_le_outer_v
#print axioms N11Formalization.C450OuterCellMajorant.outer_le_cell
#print axioms N11Formalization.C450OuterCellMajorant.normalized_of_cells
#print axioms N11Formalization.C450RadialPacketKernel.packet_bound
#print axioms N11Formalization.C450SixthSegment.cells_valid
#print axioms N11Formalization.C450SixthSegment.cells_cover
#print axioms N11Formalization.C450SixthSegment.params_valid
#print axioms N11Formalization.C450SixthSegment.params_sum
#print axioms N11Formalization.C450SixthSegment.model_eq
#print axioms N11Formalization.C450SixthSegment.radial_paid
#print axioms N11Formalization.C450SixthSegment.sixth_paid
#print axioms N11Formalization.C450SixthSegment.atom_of_remaining
#print axioms N11Formalization.C450SixthSegmentImportedAudit.actual_per_disk
#print axioms N11Formalization.C450SixthSegmentImportedAudit.all_radial_endpoints
#print axioms N11Formalization.C450SixthSegmentImportedAudit.all_direction_endpoints
