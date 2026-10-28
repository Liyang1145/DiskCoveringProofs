import N11Formalization.MetricSectorRationalCellCertificate

/-! One genuine complete-sector certificate from the saved start-0 proposal.
The intentionally coarse bound tests the whole-cell sqrt/arcsin producer;
it is not the tight sector bound needed to exclude a covering class. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteSectorControls

open RationalBoxSubdivision MetricSectorRationalCellCertificate
open MetricSectorBoxCertificate MetricSectorRationalNodes RationalTrigCellBounds

def start0_sector0_cell : Cell (Fin 3) := ![⟨0,RatInterval.piHi⟩,⟨0,1⟩,⟨0,1⟩]
def start0_sector0_bounds : CellBounds := ⟨0,2,0,39/100⟩
def start0_sector0_C : ℚ := 0
def start0_sector0_mu : ℚ := 30939859/1000000000
def start0_sector0_dL : ℚ := 41834891/1000000000
def start0_sector0_dR : ℚ := 1195057/250000000
def start0_sector0_bL : ℚ := -8660027/1000000000
def start0_sector0_bR : ℚ := -605467/1000000000
def start0_sector0_bound : ℚ := 1/8

theorem start0_sector0_bounds_valid : BoundsValid start0_sector0_cell start0_sector0_bounds := by
  constructor
  · constructor
    · intro s
      fin_cases s <;> norm_num [start0_sector0_cell,RatInterval.Valid,RatInterval.piHi]
    · constructor <;> norm_num [start0_sector0_cell,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · norm_num [start0_sector0_bounds]
  · norm_num [start0_sector0_bounds]
  · change (0 : ℚ)^2 ≤ max 0 (qRawCell start0_sector0_cell).lo
    calc
      (0 : ℚ)^2=0 := by norm_num
      _ ≤ max 0 (qRawCell start0_sector0_cell).lo := le_max_left _ _
  · calc
      (qCell start0_sector0_cell).hi ≤ 4 := min_le_left _ _
      _ ≤ start0_sector0_bounds.chordHi^2 := by norm_num [start0_sector0_bounds]
  · norm_num [start0_sector0_bounds]
  · norm_num [start0_sector0_bounds]
  · norm_num [start0_sector0_bounds,sinHiNLag,sinTQ,Finset.sum_range_succ]
  · norm_num [start0_sector0_bounds,sinLoNLag,sinTQ,Finset.sum_range_succ]

theorem start0_sector0_direct_comparison :
    sectorDirectUpperQ start0_sector0_C start0_sector0_mu start0_sector0_dL
      start0_sector0_dR start0_sector0_bL start0_sector0_bR
      start0_sector0_cell start0_sector0_bounds ≤ start0_sector0_bound := by
  norm_num [sectorDirectUpperQ,triangleCell,penaltyCell,start0_sector0_C,start0_sector0_mu,
    start0_sector0_dL,start0_sector0_dR,start0_sector0_bL,start0_sector0_bR,start0_sector0_bound,
    start0_sector0_cell,start0_sector0_bounds,signedWidthUpperQ,
    RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,
    sinCell,squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,
    sinLoNLag,sinHiNLag,sinTQ,Finset.sum_range_succ,RatInterval.piHi,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_sector0_full_domain_upper :
    ∀ a ∈ Set.Icc (0 : ℝ) Real.pi, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      sectorObjective start0_sector0_C start0_sector0_mu start0_sector0_dL
        start0_sector0_dR start0_sector0_bL start0_sector0_bR a u v ≤ (start0_sector0_bound : ℝ) := by
  intro a ha u hu v hv
  have h0 : (start0_sector0_cell 0).Mem a := by
    change ((0 : ℚ) : ℝ) ≤ a ∧ a ≤ (RatInterval.piHi : ℝ)
    rw [Rat.cast_zero]
    exact ⟨ha.1,ha.2.trans RatInterval.pi_lt_piHi.le⟩
  have h1 : (start0_sector0_cell 1).Mem u := by
    simpa [start0_sector0_cell,RatInterval.mem_iff] using hu
  have h2 : (start0_sector0_cell 2).Mem v := by
    simpa [start0_sector0_cell,RatInterval.mem_iff] using hv
  have hx : Mem start0_sector0_cell ![a,u,v] := by
    intro s
    fin_cases s
    · simpa using h0
    · simpa using h1
    · simpa using h2
  have H := sector_upper_of_direct_certificate start0_sector0_C start0_sector0_mu
    start0_sector0_dL start0_sector0_dR start0_sector0_bL start0_sector0_bR
    start0_sector0_cell start0_sector0_bounds start0_sector0_bounds_valid
    start0_sector0_bound start0_sector0_direct_comparison ![a,u,v] hx
  simpa [sectorBoxObjective] using H

#print axioms start0_sector0_bounds_valid
#print axioms start0_sector0_direct_comparison
#print axioms start0_sector0_full_domain_upper
end N11Formalization.SharedMomentConcreteSectorControls
