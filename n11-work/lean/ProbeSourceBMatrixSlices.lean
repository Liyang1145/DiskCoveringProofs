import N11Formalization.SourceBMatrixIntervals
set_option autoImplicit false
open N11Formalization SourceBMatrixIntervals RatInterval

#check @SourceBMatrixIntervals.BBox_mem
#check @SourceBMatrixIntervals.auxBox_mem
#print axioms SourceBMatrixIntervals.BBox_mem

private theorem spoke_box_shape :
    BBox 0 0 = sub (ndRingBox ndBox 0 0) (ndArcBox ndBox 0 0) := by
  simp [BBox,edgeBox,nodeBox,siteBox,SourceN2.srcEdgeV2,SourceN2.srcEdgeW2,
    RatInterval.add,RatInterval.ofRat]

private theorem hub_box_shape :
    BBox 18 19 = sub (ndBox 4) (ndWPointBox ndBox 0) := by
  simp [BBox,edgeBox,nodeBox,siteBox,auxBox,flipBox,representativeBox,
    SourceAllFaceBalance.mirrored,SourceAllFaceBalance.repIndex,
    SourceN2.srcEdgeV2,SourceN2.srcEdgeW2,SourceN2.srcFaceSite2,
    ResumeLocalIncidence.sourceFaces,Fin.reduceFinMk,RatInterval.add,RatInterval.ofRat,
    ndHub0Box_0]

theorem source_B_spoke_slice :
    (-1 : ℝ)/20 ≤ SourceN2.srcB2 SourceExactRoot.sourceRoot 0 0 ∧
      SourceN2.srcB2 SourceExactRoot.sourceRoot 0 0 ≤ 0 := by
  have hm := BBox_mem 0 0
  have hl : (-1 : ℚ)/20 ≤ (BBox 0 0).lo := by
    rw [spoke_box_shape]
    nd_eval
  have hh : (BBox 0 0).hi ≤ 0 := by
    rw [spoke_box_shape]
    nd_eval
  have hlr : (-1 : ℝ)/20 ≤ ((BBox 0 0).lo : ℝ) := by exact_mod_cast hl
  have hhr : ((BBox 0 0).hi : ℝ) ≤ 0 := by exact_mod_cast hh
  exact ⟨hlr.trans hm.1,hm.2.trans hhr⟩

-- Actual hub9 x / face0 edge19, not legacy hub9 wrapped to site0.
theorem source_B_hub_slice :
    (1 : ℝ)/5 ≤ SourceN2.srcB2 SourceExactRoot.sourceRoot 18 19 ∧
      SourceN2.srcB2 SourceExactRoot.sourceRoot 18 19 ≤ 1/4 := by
  have hm := BBox_mem 18 19
  have hl : (1 : ℚ)/5 ≤ (BBox 18 19).lo := by
    rw [hub_box_shape]
    nd_eval
  have hh : (BBox 18 19).hi ≤ (1 : ℚ)/4 := by
    rw [hub_box_shape]
    nd_eval
  have hlr : (1 : ℝ)/5 ≤ ((BBox 18 19).lo : ℝ) := by
    have h : (((1 : ℚ)/5 : ℚ) : ℝ) ≤ ((BBox 18 19).lo : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hl
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hhr : ((BBox 18 19).hi : ℝ) ≤ (1 : ℝ)/4 := by
    have h : ((BBox 18 19).hi : ℝ) ≤ (((1 : ℚ)/4 : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hh
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  exact ⟨hlr.trans hm.1,hm.2.trans hhr⟩

example (e : Fin 45) : SourceN2.srcB2 SourceExactRoot.sourceRoot 40 e = 1 :=
  actual_mass_row e

example (i : Fin 41) (e : Fin 45) :
    (BBox i e).Mem (SourceN2.srcB2 SourceExactRoot.sourceRoot i e) := BBox_mem i e

#print axioms source_B_spoke_slice
#print axioms source_B_hub_slice
