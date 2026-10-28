import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NonconstantOuterImportedAudit
open C450OuterGeometry C450OuterCellMajorant C450AngularCellMajorant
open C450SixthAnalytic

theorem actual_directions (c : Point) (e : ℝ)
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Cq c e ≤ outerV c := inner_cq_le_outer_v he0 he7 hc0
theorem actual_sixth_pair (s : Cell) (hv : ValidCell s) (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (2:ℝ)/125 ≤ e) (heHi : e ≤ 1/50)
    (hcq : c450Cq c e ∈ Set.Icc s.lo s.hi) :
    c450Outer W0 c+c450Inner W1 c e ≤ CellModel W0 W1 (2/125) (1/50) s ‖c‖ :=
  actual_pair_bound s hv c e hc0 hc1 heLo heHi hcq
example {ι : Type*} (cells : ι → Cell)
    (hv : ∀ i, ValidCell (cells i)) (hc : CoversDirections cells)
    (hr : RadialObligation cells) :
    C450NormalizedInterface.SegmentNormalized sixth :=
  normalized_of_certificate cells hv hc hr
example {ι : Type*} (cells : ι → Cell)
    (hv : ∀ i, ValidCell (cells i)) (hc : CoversDirections cells)
    (hr : RadialObligation cells) (hl : LaterSourceObligation) : C450Atom :=
  atom_of_certificate cells hv hc hr hl
example (s : Cell) : outerCoefficient W0 s+capacityB s = W0.a0+W1.a0 := capacity_sum s
example : (97/100:ℝ)*0 ≤ Real.sin 0 := sin97 (by norm_num) (by norm_num)
example : (97/100:ℝ)*(2/5) ≤ Real.sin (2/5) := sin97 (by norm_num) le_rfl
example : (4/5:ℝ)*(2*(2/5)) ≤ Real.sin (2*(2/5)) := sin2_lower (by norm_num) le_rfl
example : (3/4:ℝ)*(3*(2/5)) ≤ Real.sin (3*(2/5)) := sin3_lower (by norm_num) le_rfl
example : P3 ((1:ℝ)/2) ≤ P3 1 := P3_le le_rfl (by norm_num)
example : outerV (!₂[(7/10:ℝ),0]:Point) = 1 := by
  rw [outerV,norm_pair_zero (by norm_num)]
  norm_num
example : C450NormalizedInterface.SegmentNormalized C450FifthSegment.fifth :=
  C450FifthSegment.fifth_paid
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450NonconstantOuterImportedAudit
#print N11Formalization.C450SixthAnalytic.RadialObligation
#print N11Formalization.C450OuterCellMajorant.CellRadialBound
#check @N11Formalization.C450OuterGeometry.inner_cq_le_outer_v
#check @N11Formalization.C450OuterCellMajorant.normalized_of_cells
#check @N11Formalization.C450SixthAnalytic.normalized_of_certificate
#check @N11Formalization.C450SixthAnalytic.atom_of_certificate
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450OuterGeometry.inner_cq_le_outer_v
#print axioms N11Formalization.C450OuterGeometry.outer_t_bounds
#print axioms N11Formalization.C450OuterGeometry.sin97
#print axioms N11Formalization.C450OuterGeometry.sin3_lower
#print axioms N11Formalization.C450OuterGeometry.P3_le
#print axioms N11Formalization.C450OuterCellMajorant.signed_harmonic
#print axioms N11Formalization.C450OuterCellMajorant.outer_le_cell
#print axioms N11Formalization.C450OuterCellMajorant.normalized_of_cells
#print axioms N11Formalization.C450SixthAnalytic.actual_pair_bound
#print axioms N11Formalization.C450SixthAnalytic.capacity_sum
#print axioms N11Formalization.C450SixthAnalytic.normalized_of_certificate
#print axioms N11Formalization.C450SixthAnalytic.atom_of_certificate
#print axioms N11Formalization.C450NonconstantOuterImportedAudit.actual_directions
#print axioms N11Formalization.C450NonconstantOuterImportedAudit.actual_sixth_pair
