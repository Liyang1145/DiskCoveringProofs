import N11Formalization.MetricSectorLocalGradientCertificate

/-! A concrete positive closed sector leaf from the exact saved proposal.
This control checks the signed-gradient producer, not the complete sector root. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteSectorGradientControls
open RationalBoxSubdivision MetricSectorRationalCellCertificate MetricSectorLocalGradientCertificate
open MetricSectorRationalNodes MetricSectorBoxCertificate RationalTrigCellBounds RationalTrigLocalLipschitz

def start0_sector0_positive_cell : Cell (Fin 3) := ![⟨(1/4 : ℚ),(3/10 : ℚ)⟩,⟨(1/5 : ℚ),(1/4 : ℚ)⟩,⟨(1/10 : ℚ),(3/20 : ℚ)⟩]
def start0_sector0_C : ℚ := (0 : ℚ)
def start0_sector0_mu : ℚ := (30939859/1000000000 : ℚ)
def start0_sector0_dL : ℚ := (41834891/1000000000 : ℚ)
def start0_sector0_dR : ℚ := (1195057/250000000 : ℚ)
def start0_sector0_bL : ℚ := (-8660027/1000000000 : ℚ)
def start0_sector0_bR : ℚ := (-605467/1000000000 : ℚ)
def start0_sector0_positive_bounds : CellBounds := ⟨(6116663/100000000 : ℚ),(16079661/100000000 : ℚ),(11621/1000000 : ℚ),(30557/1000000 : ℚ)⟩
def start0_sector0_denominator_bounds : GradientBounds := ⟨(9/10 : ℚ),(1 : ℚ)⟩
def start0_sector0_midpoint_bounds : NodeBounds := ⟨(2751543/25000000 : ℚ),(11006173/100000000 : ℚ),(20913/1000000 : ℚ),(10457/500000 : ℚ)⟩
def start0_sector0_tight_bound : ℚ := (71/125000 : ℚ)

theorem start0_sector0_positive_bounds_valid : BoundsValid start0_sector0_positive_cell start0_sector0_positive_bounds := by
  constructor
  · constructor
    · intro s
      fin_cases s <;> norm_num [start0_sector0_positive_cell,RatInterval.Valid]
    · constructor <;> norm_num [start0_sector0_positive_cell,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  all_goals norm_num [start0_sector0_positive_cell,start0_sector0_positive_bounds,start0_sector0_denominator_bounds,start0_sector0_midpoint_bounds,start0_sector0_C,start0_sector0_mu,start0_sector0_dL,start0_sector0_dR,start0_sector0_bL,start0_sector0_bR,start0_sector0_tight_bound,qCell,qRawCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,sinCell,cosCell,squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,Finset.sum_range_succ,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_sector0_positive_gradient_valid : GradientValid start0_sector0_positive_cell start0_sector0_positive_bounds start0_sector0_denominator_bounds := by
  constructor
  · exact start0_sector0_positive_bounds_valid
  all_goals norm_num [start0_sector0_positive_cell,start0_sector0_positive_bounds,start0_sector0_denominator_bounds,start0_sector0_midpoint_bounds,start0_sector0_C,start0_sector0_mu,start0_sector0_dL,start0_sector0_dR,start0_sector0_bL,start0_sector0_bR,start0_sector0_tight_bound,qCell,qRawCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,sinCell,cosCell,squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,Finset.sum_range_succ,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_sector0_positive_midpoint_valid : NodeValid
    (RationalBoxSubdivision.midpoint start0_sector0_positive_cell 0)
    (RationalBoxSubdivision.midpoint start0_sector0_positive_cell 1)
    (RationalBoxSubdivision.midpoint start0_sector0_positive_cell 2) start0_sector0_midpoint_bounds := by
  constructor <;> norm_num [chordSqLoQ,chordSqHiQ,RationalBoxSubdivision.midpoint,start0_sector0_positive_cell,start0_sector0_positive_bounds,start0_sector0_denominator_bounds,start0_sector0_midpoint_bounds,start0_sector0_C,start0_sector0_mu,start0_sector0_dL,start0_sector0_dR,start0_sector0_bL,start0_sector0_bR,start0_sector0_tight_bound,qCell,qRawCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,sinCell,cosCell,squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,Finset.sum_range_succ,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_sector0_positive_gradient_comparison :
    gradientUpperQ start0_sector0_C start0_sector0_mu start0_sector0_dL start0_sector0_dR start0_sector0_bL start0_sector0_bR start0_sector0_positive_cell start0_sector0_positive_bounds
      start0_sector0_denominator_bounds start0_sector0_midpoint_bounds ≤ start0_sector0_tight_bound := by
  norm_num [gradientUpperQ,gradientErrorQ,sectorGradientCell,triangleGradientCell,penaltyGradientCell,
    widthGradientCell,widthNumeratorCell,reciprocalCell,HCell,widthCell,absBoundQ,sectorUpperQ,
    factorUpperQ,signedWidthUpperQ,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,Fin.sum_univ_three,start0_sector0_positive_cell,start0_sector0_positive_bounds,start0_sector0_denominator_bounds,start0_sector0_midpoint_bounds,start0_sector0_C,start0_sector0_mu,start0_sector0_dL,start0_sector0_dR,start0_sector0_bL,start0_sector0_bR,start0_sector0_tight_bound,qCell,qRawCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,sinCell,cosCell,squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,Finset.sum_range_succ,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

def start0_sector0_positive_certificate : PositiveCertificate start0_sector0_C start0_sector0_mu start0_sector0_dL start0_sector0_dR start0_sector0_bL start0_sector0_bR
    start0_sector0_tight_bound start0_sector0_positive_cell :=
  ⟨start0_sector0_positive_bounds,start0_sector0_denominator_bounds,start0_sector0_positive_gradient_valid,
    start0_sector0_midpoint_bounds,start0_sector0_positive_midpoint_valid,start0_sector0_positive_gradient_comparison⟩

theorem start0_sector0_positive_cell_upper :
    ∀ x, Mem start0_sector0_positive_cell x → sectorBoxObjective start0_sector0_C start0_sector0_mu start0_sector0_dL start0_sector0_dR start0_sector0_bL start0_sector0_bR x ≤ (start0_sector0_tight_bound : ℝ) :=
  start0_sector0_positive_certificate.sound

#print axioms start0_sector0_positive_bounds_valid
#print axioms start0_sector0_positive_gradient_valid
#print axioms start0_sector0_positive_midpoint_valid
#print axioms start0_sector0_positive_gradient_comparison
#print axioms start0_sector0_positive_cell_upper
end N11Formalization.SharedMomentConcreteSectorGradientControls
