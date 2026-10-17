import N11Formalization.MetricSectorLocalCertificate
import N11Formalization.RationalTrigCellBounds

/-! Finite rational enclosures for the complete skew-sector cell. The chord
uses a sum of squares and the proved closed-unit-radius bound, so coincident
endpoints and zero chord require no positivity premise. The only supplied
sqrt/arcsin data are finite rational square and sine comparisons. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorRationalCellCertificate

open RationalBoxSubdivision RationalTrigCellBounds MetricSectorRationalNodes
open MetricSectorLocalCertificate MetricSectorCompactRegularity MetricSectorBoxCertificate
open ActualCircleSegmentAlgebra ActualSectorAreaEnvelope

def qRawCell (B : Cell (Fin 3)) : RatInterval :=
  (squareCell ((B 1).sub (B 2))).add
    (((RatInterval.ofRat 4).mul ((B 1).mul (B 2))).mul
      (squareCell (sinCell ((RatInterval.ofRat (1/2)).mul (B 0)))))

def qCell (B : Cell (Fin 3)) : RatInterval :=
  ⟨max 0 (qRawCell B).lo,min 4 (qRawCell B).hi⟩

abbrev CellBounds := NodeBounds

structure BoundsValid (B : Cell (Fin 3)) (K : CellBounds) : Prop where
  valid : CellValid B
  chordLo_nonneg : 0 ≤ K.chordLo
  chordHi_nonneg : 0 ≤ K.chordHi
  squareLo : K.chordLo^2 ≤ (qCell B).lo
  squareHi : (qCell B).hi ≤ K.chordHi^2
  halfWidthLo_mem : K.halfWidthLo ∈ Set.Icc (0 : ℚ) 1
  halfWidthHi_mem : K.halfWidthHi ∈ Set.Icc (0 : ℚ) 1
  sinHi_le : sinHiNLag K.halfWidthLo ≤ (19/100)*K.chordLo
  le_sinLo : (19/100)*K.chordHi ≤ sinLoNLag K.halfWidthHi

theorem chord_square_identity (a u v : ℝ) :
    (u-v)^2+4*(u*v)*Real.sin (a/2)^2=u^2+v^2-2*u*v*Real.cos a := by
  have hc := Real.cos_two_mul (a/2)
  rw [show 2*(a/2)=a by ring] at hc
  have ht := Real.sin_sq_add_cos_sq (a/2)
  have he : Real.cos a=1-2*Real.sin (a/2)^2 := by nlinarith only [hc,ht]
  rw [he]
  ring

theorem qRawCell_mem {B : Cell (Fin 3)} {x : Fin 3 → ℝ} (hx : Mem B x) :
    (qRawCell B).Mem (x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0)) := by
  have hhalf : ((RatInterval.ofRat (1/2)).mul (B 0)).Mem (x 0/2) := by
    convert RatInterval.mul_mem (RatInterval.ofRat_mem (1/2 : ℚ)) (hx 0) using 1 <;>
      norm_num <;> ring
  have h4 : (RatInterval.ofRat 4).Mem (4 : ℝ) := by
    simpa using RatInterval.ofRat_mem (4 : ℚ)
  have hh := RatInterval.add_mem (squareCell_mem (RatInterval.sub_mem (hx 1) (hx 2)))
    (RatInterval.mul_mem (RatInterval.mul_mem h4 (RatInterval.mul_mem (hx 1) (hx 2)))
      (squareCell_mem (sinCell_mem hhalf)))
  rw [chord_square_identity] at hh
  exact hh

theorem qCell_mem {B : Cell (Fin 3)} (hB : RadiusBoxValid B)
    {x : Fin 3 → ℝ} (hx : Mem B x) :
    (qCell B).Mem (x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0)) := by
  have hraw := qRawCell_mem hx
  have hr := radii_mem hB hx
  have hq : 0 ≤ x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0) := by
    rw [← chord_vector_sq]
    exact sq_nonneg _
  have hch := chordLength_box (a := x 0) hr.1 hr.2
  have he : chordLength (x 0) (x 1) (x 2)^2=
      x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0) := by
    exact Real.sq_sqrt hq
  have hh := (sq_le_sq₀ hch.1 (by norm_num : (0 : ℝ) ≤ 2)).mpr hch.2
  have hfour : x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0) ≤ 4 := by
    nlinarith only [he,hh]
  change ((max 0 (qRawCell B).lo : ℚ) : ℝ) ≤ _ ∧
    _ ≤ ((min 4 (qRawCell B).hi : ℚ) : ℝ)
  push_cast
  exact ⟨max_le hq hraw.1,le_min hfour hraw.2⟩

theorem chord_bounds_of_cell {B : Cell (Fin 3)} {K : CellBounds}
    (hK : BoundsValid B K) {x : Fin 3 → ℝ} (hx : Mem B x) :
    (K.chordLo : ℝ) ≤ chordLength (x 0) (x 1) (x 2) ∧
      chordLength (x 0) (x 1) (x 2) ≤ (K.chordHi : ℝ) := by
  have hq := qCell_mem hK.valid.radii hx
  have hl : (K.chordLo : ℝ)^2 ≤ ((qCell B).lo : ℝ) := by exact_mod_cast hK.squareLo
  have hh : ((qCell B).hi : ℝ) ≤ (K.chordHi : ℝ)^2 := by exact_mod_cast hK.squareHi
  exact ⟨Real.le_sqrt_of_sq_le (hl.trans hq.1),
    Real.sqrt_le_iff.mpr ⟨by exact_mod_cast hK.chordHi_nonneg,hq.2.trans hh⟩⟩

theorem width_bounds_of_cell {B : Cell (Fin 3)} {K : CellBounds}
    (hK : BoundsValid B K) {x : Fin 3 → ℝ} (hx : Mem B x) :
    (2*K.halfWidthLo : ℚ) ≤ sectorWidth (x 0) (x 1) (x 2) ∧
      sectorWidth (x 0) (x 1) (x 2) ≤ (2*K.halfWidthHi : ℚ) := by
  have hc := chord_bounds_of_cell hK hx
  have hr := radii_mem hK.valid.radii hx
  have hch := chordLength_box (a := x 0) hr.1 hr.2
  have harg : (19/50 : ℝ)*chordLength (x 0) (x 1) (x 2)/2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith only [hch.1,hch.2]
  have hl : (K.halfWidthLo : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have h0 : (0 : ℝ) ≤ K.halfWidthLo := by exact_mod_cast hK.halfWidthLo_mem.1
    have h1 : (K.halfWidthLo : ℝ) ≤ 1 := by exact_mod_cast hK.halfWidthLo_mem.2
    constructor <;> linarith [Real.pi_gt_three]
  have hh : (K.halfWidthHi : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have h0 : (0 : ℝ) ≤ K.halfWidthHi := by exact_mod_cast hK.halfWidthHi_mem.1
    have h1 : (K.halfWidthHi : ℝ) ≤ 1 := by exact_mod_cast hK.halfWidthHi_mem.2
    constructor <;> linarith [Real.pi_gt_three]
  have hslo : Real.sin (K.halfWidthLo : ℝ) ≤
      (19/50 : ℝ)*chordLength (x 0) (x 1) (x 2)/2 := by
    have hsin : (sinHiNLag K.halfWidthLo : ℝ) ≤ (19/100 : ℝ)*K.chordLo := by
      have ht : (sinHiNLag K.halfWidthLo : ℝ) ≤ ((19/100)*K.chordLo : ℚ) :=
        by exact_mod_cast hK.sinHi_le
      norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at ht
      exact ht
    have hm := (sin_le_sinHiNLag K.halfWidthLo).trans hsin
    linarith only [hm,hc.1]
  have hshi : (19/50 : ℝ)*chordLength (x 0) (x 1) (x 2)/2 ≤
      Real.sin (K.halfWidthHi : ℝ) := by
    have hsin : (19/100 : ℝ)*K.chordHi ≤ (sinLoNLag K.halfWidthHi : ℝ) := by
      have ht : (((19/100)*K.chordHi : ℚ) : ℝ) ≤ (sinLoNLag K.halfWidthHi : ℝ) :=
        by exact_mod_cast hK.le_sinLo
      norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at ht
      exact ht
    have hm := hsin.trans (sinLoNLag_le_sin K.halfWidthHi)
    linarith only [hm,hc.2]
  have hal := (Real.le_arcsin_iff_sin_le hl harg).mpr hslo
  have hah := (Real.arcsin_le_iff_le_sin harg hh).mpr hshi
  unfold sectorWidth
  push_cast
  constructor <;> linarith only [hal,hah]

def triangleCell (B : Cell (Fin 3)) : RatInterval :=
  ((RatInterval.ofRat ((19/50 : ℚ)^2/2)).mul ((B 1).mul (B 2))).mul (sinCell (B 0))

def penaltyCell (c : ℚ) (I : RatInterval) : RatInterval := (RatInterval.ofRat (-c)).mul I

def sectorDirectUpperQ (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3)) (K : CellBounds) : ℚ :=
  (triangleCell B).hi+(2*K.halfWidthHi-sinLoNLag (2*K.halfWidthHi))/2+
    signedWidthUpperQ C K+(penaltyCell mu (B 0)).hi+
      (penaltyCell dL (squareCell (B 1))).hi+(penaltyCell dR (squareCell (B 2))).hi+
        (penaltyCell bL (B 1)).hi+(penaltyCell bR (B 2)).hi

theorem triangleCell_mem {B : Cell (Fin 3)} {x : Fin 3 → ℝ} (hx : Mem B x) :
    (triangleCell B).Mem ((19/50 : ℝ)^2*x 1*x 2*Real.sin (x 0)/2) := by
  have hc : (RatInterval.ofRat ((19/50 : ℚ)^2/2)).Mem ((19/50 : ℝ)^2/2) := by
    convert RatInterval.ofRat_mem ((19/50 : ℚ)^2/2) using 1 <;> norm_num
  have hh := RatInterval.mul_mem (RatInterval.mul_mem hc (RatInterval.mul_mem (hx 1) (hx 2)))
    (sinCell_mem (hx 0))
  convert hh using 1
  · rfl
  · ring

theorem penaltyCell_mem (c : ℚ) {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    (penaltyCell c I).Mem (-(c : ℝ)*x) := by
  simpa only [penaltyCell,Rat.cast_neg] using RatInterval.mul_mem (RatInterval.ofRat_mem (-c)) hx

theorem sector_cell_upper (C mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} {K : CellBounds} (hK : BoundsValid B K)
    {x : Fin 3 → ℝ} (hx : Mem B x) :
    sectorBoxObjective C mu dL dR bL bR x ≤ (sectorDirectUpperQ C mu dL dR bL bR B K : ℝ) := by
  have ht := (triangleCell_mem hx).2
  have hw := width_bounds_of_cell hK hx
  have hg := segmentTerm_monotone hw.2
  have hs := sinLoNLag_le_sin (2*K.halfWidthHi)
  push_cast at hs
  have hcap : segmentTerm (sectorWidth (x 0) (x 1) (x 2)) ≤
      ((2*K.halfWidthHi-sinLoNLag (2*K.halfWidthHi))/2 : ℚ) := by
    unfold segmentTerm at hg ⊢
    push_cast at hg ⊢
    linarith only [hg,hs]
  have hc : (C : ℝ)*sectorWidth (x 0) (x 1) (x 2) ≤ (signedWidthUpperQ C K : ℝ) := by
    unfold signedWidthUpperQ
    by_cases hC : 0 ≤ C
    · rw [if_pos hC,Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left hw.2 (by exact_mod_cast hC)
    · rw [if_neg hC,Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left hw.1 (by exact_mod_cast (not_le.mp hC).le)
  have hmu := (penaltyCell_mem mu (hx 0)).2
  have hdL := (penaltyCell_mem dL (squareCell_mem (hx 1))).2
  have hdR := (penaltyCell_mem dR (squareCell_mem (hx 2))).2
  have hbL := (penaltyCell_mem bL (hx 1)).2
  have hbR := (penaltyCell_mem bR (hx 2)).2
  unfold sectorBoxObjective sectorObjective sectorFactor sectorDirectUpperQ
  push_cast at hcap
  push_cast
  linarith only [ht,hcap,hc,hmu,hdL,hdR,hbL,hbR]

theorem sector_upper_of_direct_certificate (C mu dL dR bL bR : ℚ)
    (B : Cell (Fin 3)) (K : CellBounds) (hK : BoundsValid B K) (M : ℚ)
    (hbound : sectorDirectUpperQ C mu dL dR bL bR B K ≤ M) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  intro x hx
  exact (sector_cell_upper C mu dL dR bL bR hK hx).trans (by exact_mod_cast hbound)

#print axioms chord_square_identity
#print axioms qRawCell_mem
#print axioms qCell_mem
#print axioms chord_bounds_of_cell
#print axioms width_bounds_of_cell
#print axioms triangleCell_mem
#print axioms penaltyCell_mem
#print axioms sector_cell_upper
#print axioms sector_upper_of_direct_certificate
end N11Formalization.MetricSectorRationalCellCertificate
