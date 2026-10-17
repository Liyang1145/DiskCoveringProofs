import N11Formalization.C450OuterCellMajorant
import N11Formalization.C450FifthSegment

/-! Actual sixth source weights consume the nonconstant outer engine.
Cell coverage and continuous radial certification stay EXPLICIT/UNPROVED. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthAnalytic
open C450AngularCellMajorant C450NormalizedInterface

def sixth : TenSeg := c450Segs[5]'(by decide +kernel)
theorem sixth_mem : sixth ∈ c450Segs := by decide +kernel
theorem nn0 : |sixth.a1|+|sixth.a2|+|sixth.a3| ≤ sixth.a0 :=
  (c450Segs_nonneg sixth sixth_mem).1
theorem nn1 : |sixth.b1|+|sixth.b2|+|sixth.b3| ≤ sixth.b0 :=
  (c450Segs_nonneg sixth sixth_mem).2
def W0 : TrigDensity := sixth.W0 nn0
def W1 : TrigDensity := sixth.W1 nn1

theorem outer_signs : W0.a1 ≤ 0 ∧ W0.a2 ≤ 0 ∧ W0.a3 ≤ 0 := by
  norm_num [W0,sixth,c450Segs,TenSeg.W0]
theorem inner_sign : W1.a1 ≤ 0 := by
  norm_num [W1,sixth,c450Segs,TenSeg.W1]
theorem outer_not_constant : W0.a1 ≠ 0 := by
  norm_num [W0,sixth,c450Segs,TenSeg.W0]

theorem actual_pair_bound (s : Cell) (hv : ValidCell s) (c : Point) (e : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (heLo : (2:ℝ)/125 ≤ e) (heHi : e ≤ 1/50)
    (hcq : c450Cq c e ∈ Set.Icc s.lo s.hi) :
    c450Outer W0 c+c450Inner W1 c e ≤
      C450OuterCellMajorant.CellModel W0 W1 (2/125) (1/50) s ‖c‖ :=
  C450OuterCellMajorant.pair_le_cell W0 W1 outer_signs.1 outer_signs.2.1
    outer_signs.2.2 inner_sign s hv (by norm_num) heLo heHi
    (by norm_num) hc0 hc1 hcq

def RadialObligation {ι : Type*} (cells : ι → Cell) : Prop :=
  ∀ i, C450OuterCellMajorant.CellRadialBound W0 W1 (2/125) (1/50) (cells i)

theorem normalized_of_certificate {ι : Type*} (cells : ι → Cell)
    (hv : ∀ i, ValidCell (cells i)) (hc : CoversDirections cells)
    (hr : RadialObligation cells) : SegmentNormalized sixth := by
  intro h0 h1
  have hp := C450OuterCellMajorant.normalized_of_cells cells hv hc W0 W1
    outer_signs.1 outer_signs.2.1 outer_signs.2.2 inner_sign
    (2/125) (1/50) (by norm_num) (by norm_num) hr
  have he0 : (sixth.eLo:ℝ) = (2/125:ℝ) := by norm_num [sixth,c450Segs]
  have he1 : (sixth.eHi:ℝ) = (1/50:ℝ) := by norm_num [sixth,c450Segs]
  rw [he0,he1]
  exact hp

/-- A capacity scalar, not a replacement inner density. -/
def capacityB (s : Cell) : ℝ :=
  W0.a0+W1.a0-C450OuterCellMajorant.outerCoefficient W0 s
theorem capacity_sum (s : Cell) :
    C450OuterCellMajorant.outerCoefficient W0 s+capacityB s = W0.a0+W1.a0 := by
  unfold capacityB
  ring

def LaterSourceObligation : Prop :=
  ∀ s ∈ C450FifthSegment.remainingSegs, s ≠ sixth → SegmentNormalized s

/-- Still conditional on the actual continuous cell certificate and all
other source segments; no sixth/whole-C450 count is claimed here. -/
theorem atom_of_certificate {ι : Type*} (cells : ι → Cell)
    (hv : ∀ i, ValidCell (cells i)) (hc : CoversDirections cells)
    (hr : RadialObligation cells) (hl : LaterSourceObligation) : C450Atom := by
  apply C450FifthSegment.atom_of_remaining
  intro s hs
  by_cases heq : s = sixth
  · rw [heq]
    exact normalized_of_certificate cells hv hc hr
  · exact hl s hs heq
end N11Formalization.C450SixthAnalytic
#check @N11Formalization.C450SixthAnalytic.actual_pair_bound
#check @N11Formalization.C450SixthAnalytic.normalized_of_certificate
#check @N11Formalization.C450SixthAnalytic.atom_of_certificate
#print axioms N11Formalization.C450SixthAnalytic.actual_pair_bound
#print axioms N11Formalization.C450SixthAnalytic.capacity_sum
#print axioms N11Formalization.C450SixthAnalytic.normalized_of_certificate
#print axioms N11Formalization.C450SixthAnalytic.atom_of_certificate
