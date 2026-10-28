import N11Formalization.MetricSectorBoxCertificate
import N11Formalization.MetricAreaRationalCertificate

/-! Exact rational nodes for the full skew-sector objective. The angle has
no range restriction, both endpoint radii vary independently, and square
and sine brackets include the coincident-endpoint locus. All certificate
checks are rational comparisons; sqrt, arcsin and trigonometric node
inequalities are conclusions. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorRationalNodes

open MetricSectorCompactRegularity MetricSectorBoxCertificate
open ActualCircleSegmentAlgebra ActualSectorAreaEnvelope
open CompactBoxGridCertificate MetricAreaRationalCertificate

def chordSqLoQ (a u v : ℚ) : ℚ :=
  max 0 (u^2+v^2-2*u*v*cosHiNLag a)

def chordSqHiQ (a u v : ℚ) : ℚ :=
  u^2+v^2-2*u*v*cosLoNLag a

structure NodeBounds where
  chordLo : ℚ
  chordHi : ℚ
  halfWidthLo : ℚ
  halfWidthHi : ℚ

/-- Only finite rational domain, square and Taylor-bracket checks. -/
structure NodeValid (a u v : ℚ) (B : NodeBounds) : Prop where
  radiusLeft : u ∈ Set.Icc (0 : ℚ) 1
  radiusRight : v ∈ Set.Icc (0 : ℚ) 1
  chordLo_nonneg : 0 ≤ B.chordLo
  chordHi_nonneg : 0 ≤ B.chordHi
  squareLo : B.chordLo^2 ≤ chordSqLoQ a u v
  squareHi : chordSqHiQ a u v ≤ B.chordHi^2
  halfWidthLo_mem : B.halfWidthLo ∈ Set.Icc (0 : ℚ) 1
  halfWidthHi_mem : B.halfWidthHi ∈ Set.Icc (0 : ℚ) 1
  sinHi_le : sinHiNLag B.halfWidthLo ≤ (19/100)*B.chordLo
  le_sinLo : (19/100)*B.chordHi ≤ sinLoNLag B.halfWidthHi

theorem chordSq_brackets {a u v : ℚ}
    (hu : u ∈ Set.Icc (0 : ℚ) 1) (hv : v ∈ Set.Icc (0 : ℚ) 1) :
    (chordSqLoQ a u v : ℝ) ≤ (u : ℝ)^2+(v : ℝ)^2-2*u*v*Real.cos a ∧
      (u : ℝ)^2+(v : ℝ)^2-2*u*v*Real.cos a ≤ (chordSqHiQ a u v : ℝ) := by
  have huv : (0 : ℝ) ≤ 2*(u : ℝ)*v :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast hu.1))
      (by exact_mod_cast hv.1)
  have hlo := mul_le_mul_of_nonneg_left (cosLoNLag_le_cos a) huv
  have hhi := mul_le_mul_of_nonneg_left (cos_le_cosHiNLag a) huv
  have hq : (0 : ℝ) ≤ (u : ℝ)^2+(v : ℝ)^2-2*u*v*Real.cos a := by
    rw [← chord_vector_sq]
    exact sq_nonneg _
  unfold chordSqLoQ chordSqHiQ
  push_cast
  exact ⟨max_le hq (by linarith only [hhi]),by linarith only [hlo]⟩

theorem chord_bounds_of_node {a u v : ℚ} {B : NodeBounds}
    (hB : NodeValid a u v B) :
    (B.chordLo : ℝ) ≤ chordLength a u v ∧ chordLength a u v ≤ (B.chordHi : ℝ) := by
  have hq := chordSq_brackets (a := a) hB.radiusLeft hB.radiusRight
  have hl : (B.chordLo : ℝ)^2 ≤ (chordSqLoQ a u v : ℝ) :=
    by exact_mod_cast hB.squareLo
  have hh : (chordSqHiQ a u v : ℝ) ≤ (B.chordHi : ℝ)^2 :=
    by exact_mod_cast hB.squareHi
  unfold chordLength
  exact ⟨Real.le_sqrt_of_sq_le (hl.trans hq.1),
    Real.sqrt_le_iff.mpr ⟨by exact_mod_cast hB.chordHi_nonneg,hq.2.trans hh⟩⟩

theorem width_bounds_of_node {a u v : ℚ} {B : NodeBounds}
    (hB : NodeValid a u v B) :
    (2*B.halfWidthLo : ℚ) ≤ sectorWidth a u v ∧
      sectorWidth a u v ≤ (2*B.halfWidthHi : ℚ) := by
  have hc := chord_bounds_of_node hB
  have hu : (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by exact_mod_cast hB.radiusLeft.1,by exact_mod_cast hB.radiusLeft.2⟩
  have hv : (v : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by exact_mod_cast hB.radiusRight.1,by exact_mod_cast hB.radiusRight.2⟩
  have hch := chordLength_box (a := (a : ℝ)) hu hv
  have hx : (19/50 : ℝ)*chordLength a u v/2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith only [hch.1,hch.2]
  have hl : (B.halfWidthLo : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have h0 : (0 : ℝ) ≤ B.halfWidthLo := by exact_mod_cast hB.halfWidthLo_mem.1
    have h1 : (B.halfWidthLo : ℝ) ≤ 1 := by exact_mod_cast hB.halfWidthLo_mem.2
    constructor <;> linarith [Real.pi_gt_three]
  have hh : (B.halfWidthHi : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have h0 : (0 : ℝ) ≤ B.halfWidthHi := by exact_mod_cast hB.halfWidthHi_mem.1
    have h1 : (B.halfWidthHi : ℝ) ≤ 1 := by exact_mod_cast hB.halfWidthHi_mem.2
    constructor <;> linarith [Real.pi_gt_three]
  have hslo : Real.sin (B.halfWidthLo : ℝ) ≤ (19/50 : ℝ)*chordLength a u v/2 := by
    have hsin : (sinHiNLag B.halfWidthLo : ℝ) ≤ (19/100 : ℝ)*B.chordLo := by
      have ht : (sinHiNLag B.halfWidthLo : ℝ) ≤ ((19/100)*B.chordLo : ℚ) :=
        by exact_mod_cast hB.sinHi_le
      norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at ht
      exact ht
    have hm := (sin_le_sinHiNLag B.halfWidthLo).trans hsin
    linarith only [hm,hc.1]
  have hshi : (19/50 : ℝ)*chordLength a u v/2 ≤ Real.sin (B.halfWidthHi : ℝ) := by
    have hsin : (19/100 : ℝ)*B.chordHi ≤ (sinLoNLag B.halfWidthHi : ℝ) := by
      have ht : (((19/100)*B.chordHi : ℚ) : ℝ) ≤ (sinLoNLag B.halfWidthHi : ℝ) :=
        by exact_mod_cast hB.le_sinLo
      norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at ht
      exact ht
    have hm := hsin.trans (sinLoNLag_le_sin B.halfWidthHi)
    linarith only [hm,hc.2]
  have hal := (Real.le_arcsin_iff_sin_le hl hx).mpr hslo
  have hah := (Real.arcsin_le_iff_le_sin hx hh).mpr hshi
  unfold sectorWidth
  push_cast
  constructor <;> linarith only [hal,hah]

def factorUpperQ (a u v : ℚ) (B : NodeBounds) : ℚ :=
  (19/50)^2*u*v*sinHiNLag a/2+
    (2*B.halfWidthHi-sinLoNLag (2*B.halfWidthHi))/2

def signedWidthUpperQ (C : ℚ) (B : NodeBounds) : ℚ :=
  C*(if 0 ≤ C then 2*B.halfWidthHi else 2*B.halfWidthLo)

def sectorUpperQ (C mu dL dR bL bR a u v : ℚ) (B : NodeBounds) : ℚ :=
  factorUpperQ a u v B+signedWidthUpperQ C B-mu*a-dL*u^2-dR*v^2-bL*u-bR*v

theorem factor_upper_of_node {a u v : ℚ} {B : NodeBounds}
    (hB : NodeValid a u v B) : sectorFactor a u v ≤ (factorUpperQ a u v B : ℝ) := by
  have hw := width_bounds_of_node hB
  have hg := segmentTerm_monotone hw.2
  have hsin := sin_le_sinHiNLag a
  have huv : (0 : ℝ) ≤ (19/50 : ℝ)^2*(u : ℝ)*v/2 := by
    have hu : (0 : ℝ) ≤ u := by exact_mod_cast hB.radiusLeft.1
    have hv : (0 : ℝ) ≤ v := by exact_mod_cast hB.radiusRight.1
    positivity
  have hs := mul_le_mul_of_nonneg_left hsin huv
  have ht := sinLoNLag_le_sin (2*B.halfWidthHi)
  unfold sectorFactor factorUpperQ segmentTerm at *
  push_cast at *
  nlinarith only [hg,hs,ht]

theorem signed_width_upper_of_node (C : ℚ) {a u v : ℚ} {B : NodeBounds}
    (hB : NodeValid a u v B) : (C : ℝ)*sectorWidth a u v ≤ (signedWidthUpperQ C B : ℝ) := by
  have hw := width_bounds_of_node hB
  unfold signedWidthUpperQ
  by_cases hC : 0 ≤ C
  · rw [if_pos hC,Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left hw.2 (by exact_mod_cast hC)
  · rw [if_neg hC,Rat.cast_mul]
    exact mul_le_mul_of_nonpos_left hw.1 (by exact_mod_cast (not_le.mp hC).le)

theorem sector_upper_of_node (C mu dL dR bL bR : ℚ) {a u v : ℚ} {B : NodeBounds}
    (hB : NodeValid a u v B) :
    sectorObjective C mu dL dR bL bR a u v ≤ (sectorUpperQ C mu dL dR bL bR a u v B : ℝ) := by
  have hf := factor_upper_of_node hB
  have hw := signed_width_upper_of_node C hB
  unfold sectorObjective sectorUpperQ
  push_cast
  linarith only [hf,hw]

def sectorBoxSidesQ (U : ℚ) : Fin 3 → ℚ := ![U,1,1]

def sectorGridVectorQ (U : ℚ) (N : Fin 3 → ℕ) (k : ∀ j, Fin (N j+1)) : Fin 3 → ℚ :=
  fun j => nodeQ (sectorBoxSidesQ U j) (N j) (k j)

theorem sectorGridVectorQ_cast (U : ℚ) (N : Fin 3 → ℕ) (k : ∀ j, Fin (N j+1)) :
    (fun j => (sectorGridVectorQ U N k j : ℝ)) = gridVector (sectorBoxSides U) N k := by
  funext j
  rw [sectorGridVectorQ,nodeQ_cast]
  unfold gridVector
  congr 1
  fin_cases j <;> simp [sectorBoxSidesQ,sectorBoxSides]

theorem grid_node_upper_of_rational (C mu dL dR bL bR U M : ℚ)
    (N : Fin 3 → ℕ) (k : ∀ j, Fin (N j+1)) (B : NodeBounds)
    (hB : NodeValid (sectorGridVectorQ U N k 0) (sectorGridVectorQ U N k 1)
      (sectorGridVectorQ U N k 2) B)
    (hupper : sectorUpperQ C mu dL dR bL bR (sectorGridVectorQ U N k 0)
      (sectorGridVectorQ U N k 1) (sectorGridVectorQ U N k 2) B ≤ M) :
    sectorBoxObjective C mu dL dR bL bR (gridVector (sectorBoxSides U) N k) ≤ (M : ℝ) := by
  rw [← sectorGridVectorQ_cast]
  exact (sector_upper_of_node C mu dL dR bL bR hB).trans (by exact_mod_cast hupper)

theorem sector_box_upper_of_rational_certificate (C mu dL dR bL bR U M : ℚ)
    (hU : 0 ≤ U) (N : Fin 3 → ℕ) (hN : ∀ j, 0 < N j)
    (B : (∀ j, Fin (N j+1)) → NodeBounds)
    (hB : ∀ k, NodeValid (sectorGridVectorQ U N k 0) (sectorGridVectorQ U N k 1)
      (sectorGridVectorQ U N k 2) (B k))
    (hupper : ∀ k, sectorUpperQ C mu dL dR bL bR (sectorGridVectorQ U N k 0)
      (sectorGridVectorQ U N k 1) (sectorGridVectorQ U N k 2) (B k) ≤ M) :
    ∀ x ∈ Box (sectorBoxSides (U : ℝ)), sectorBoxObjective C mu dL dR bL bR x ≤
      (M : ℝ)+sectorGridError C mu dL dR bL bR U N := by
  apply sectorObjective_box_upper_of_grid C mu dL dR bL bR (by exact_mod_cast hU) N hN
  intro k
  exact grid_node_upper_of_rational C mu dL dR bL bR U M N k (B k) (hB k) (hupper k)

end N11Formalization.MetricSectorRationalNodes
#check @N11Formalization.MetricSectorRationalNodes.sector_upper_of_node
#check @N11Formalization.MetricSectorRationalNodes.sector_box_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorRationalNodes.chord_bounds_of_node
#print axioms N11Formalization.MetricSectorRationalNodes.width_bounds_of_node
#print axioms N11Formalization.MetricSectorRationalNodes.sector_upper_of_node
#print axioms N11Formalization.MetricSectorRationalNodes.sector_box_upper_of_rational_certificate
