import N11Formalization.ActualEarMaskedGridBridge
import N11Formalization.MetricAreaRationalCertificate

/-! Every analytic node input and the large-cap constant in the actual ear
masked dual is produced from exact rational Taylor/bracket checks. The
nonnegative mask multiplier preserves the direction of the arcsin upper
replacement. No numerical class table is asserted by this generic consumer. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaMaskedRationalCertificate

open ActualSectorAreaEnvelope MetricAreaGridCertificate MetricAreaMaskedGridDual
open MetricAreaRationalCertificate ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualBoundaryNineTies ActualRefinementDoubleCounting
open ActualRingLinkBoundaryData ActualEarOwnedWidth ActualQ1CoreFans

def widthMultiplierQ {I : Type*} [DecidableEq I] (J : Finset I)
    (lam eta : ℚ) (i : I) : ℚ := lam+if i ∈ J then eta else 0

theorem widthMultiplierQ_cast {I : Type*} [DecidableEq I] (J : Finset I)
    (lam eta : ℚ) (i : I) :
    (widthMultiplierQ J lam eta i : ℝ) = widthMultiplier J (lam : ℝ) (eta : ℝ) i := by
  by_cases hi : i ∈ J <;> simp [widthMultiplierQ,widthMultiplier,hi]

theorem widthMultiplierQ_nonneg {I : Type*} [DecidableEq I] (J : Finset I)
    {lam eta : ℚ} (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (i : I) :
    0 ≤ widthMultiplierQ J lam eta i := by
  unfold widthMultiplierQ
  split_ifs <;> linarith

def BigCapBracketValid (B : ℚ) : Prop :=
  0 ≤ B ∧ B ≤ 1 ∧ (19/25 : ℚ) ≤ sinLoNLag B

theorem big_cap_bracket_upper {B : ℚ} (hB : BigCapBracketValid B) :
    Real.arcsin (19/25 : ℝ) ≤ (B : ℝ) := by
  have hx : (19/25 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hb : (B : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    have hb0 : (0 : ℝ) ≤ B := by exact_mod_cast hB.1
    have hb1 : (B : ℝ) ≤ 1 := by exact_mod_cast hB.2.1
    constructor <;> linarith [Real.pi_gt_three]
  apply (Real.arcsin_le_iff_le_sin hx hb).mpr
  have hs : ((19/25 : ℚ) : ℝ) ≤ (sinLoNLag B : ℝ) := Rat.cast_le.mpr hB.2.2
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hs
  exact hs.trans (sinLoNLag_le_sin B)

/-- One shared bracket is paid by a factorial-Taylor rational check, rather
than by a floating-point arcsin evaluation or a proposed class table. -/
theorem bracket_108_125_valid : BigCapBracketValid (108/125) := by
  unfold BigCapBracketValid
  decide +kernel

theorem arcsin_19_25_le_108_125 : Real.arcsin (19/25 : ℝ) ≤ (108/125 : ℝ) := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using big_cap_bracket_upper bracket_108_125_valid

def totalUpper {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (ear : Fin 9) (mu : Fin 11 → ℚ) (lam eta B U : ℚ) (N : ℕ)
    (edgeMax : Finset (Fin 11) → ℚ) (sectorMax : Fin 9 → ℚ) : ℚ :=
  piProductUpper (2*((∑ j : Fin 11, mu j)-lam-eta)) + 2*B*eta +
    (∑ e ∈ edges R, (edgeMax e+((19/50 : ℚ)^2+|∑ j ∈ e, mu j|)*U/N)) +
    (∑ i : Fin 9, (sectorMax i+
      (1+widthMultiplierQ (outsideGaps ear) lam eta i+|mu (nextSite i)|)*U/N))

/-- Only finite rational checks remain, including the large-cap arcsin
bracket, all nodes and the strict total. The actual selected ear supplies
the masked width budget internally through the real grid bridge. -/
theorem exclude_selected_ear_of_rational_certificate
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) (E : EarData R)
    (mu : Fin 11 → ℚ) (lam eta B U : ℚ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hB : BigCapBracketValid B) (hU : RatInterval.piHi ≤ U)
    (N : ℕ) (hN : 0 < N)
    (a : Fin (N+1) → ℚ) (ha : ∀ k, NodeValid (nodeQ U N k) (a k))
    (edgeMax : Finset (Fin 11) → ℚ) (sectorMax : Fin 9 → ℚ)
    (hedge : ∀ e ∈ edges R, ∀ k : Fin (N+1),
      edgeUpper (∑ j ∈ e, mu j) (nodeQ U N k) ≤ edgeMax e)
    (hsector : ∀ (i : Fin 9) (k : Fin (N+1)),
      sectorUpper (mu (nextSite i)) (widthMultiplierQ (outsideGaps E.center) lam eta i)
        (nodeQ U N k) (a k) ≤ sectorMax i)
    (hstrict : totalUpper R E.center mu lam eta B U N edgeMax sectorMax < RatInterval.piLo) :
    False := by
  classical
  have hUr : Real.pi ≤ (U : ℝ) :=
    RatInterval.pi_lt_piHi.le.trans (by exact_mod_cast hU)
  have hp := pi_product_upper (2*((∑ j : Fin 11, mu j)-lam-eta))
  have hp' : 2*Real.pi*((∑ j : Fin 11, (mu j : ℝ))-(lam : ℝ)-(eta : ℝ)) ≤
      (piProductUpper (2*((∑ j : Fin 11, mu j)-lam-eta)) : ℝ) := by
    convert hp using 1 <;> push_cast <;> ring
  have hBp := mul_le_mul_of_nonneg_right (big_cap_bracket_upper hB)
    (show (0 : ℝ) ≤ eta by exact_mod_cast heta)
  have hconstant : 2*Real.pi*((∑ j : Fin 11, (mu j : ℝ))-(lam : ℝ)) -
      (2*Real.pi-2*Real.arcsin (19/25))*(eta : ℝ) ≤
      (piProductUpper (2*((∑ j : Fin 11, mu j)-lam-eta))+2*B*eta : ℚ) := by
    push_cast
    nlinarith only [hp',hBp]
  push_cast at hconstant
  have ht : (totalUpper R E.center mu lam eta B U N edgeMax sectorMax : ℝ) < Real.pi :=
    (show (totalUpper R E.center mu lam eta B U N edgeMax sectorMax : ℝ) <
      (RatInterval.piLo : ℝ) by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hs : 2*Real.pi*((∑ j : Fin 11, (mu j : ℝ))-(lam : ℝ)) -
      (2*Real.pi-2*Real.arcsin (19/25))*(eta : ℝ) +
      (∑ e ∈ edges R, ((edgeMax e : ℝ)+
        ((19/50 : ℝ)^2+|∑ j ∈ e, (mu j : ℝ)|)*(U : ℝ)/(N : ℝ))) +
      (∑ i : Fin 9, ((sectorMax i : ℝ)+
        (1+widthMultiplier (outsideGaps E.center) (lam : ℝ) (eta : ℝ) i+
          |(mu (nextSite i) : ℝ)|)*(U : ℝ)/(N : ℝ))) < Real.pi := by
    unfold totalUpper at ht
    push_cast at ht
    simp_rw [widthMultiplierQ_cast] at ht
    linarith only [hconstant,ht]
  apply ActualEarMaskedGridBridge.exclude_selected_ear_of_masked_grid_certificate
    h hr R v E (fun j => (mu j : ℝ)) (lam : ℝ) (eta : ℝ)
    (by exact_mod_cast hlam) (by exact_mod_cast heta) (U : ℝ) hUr N hN
    (fun e => (edgeMax e : ℝ)) (fun i => (sectorMax i : ℝ)) ?_ ?_ hs
  · intro e he k
    rw [← nodeQ_cast]
    have hn := edge_upper (∑ j ∈ e, mu j) (nodeQ U N k)
    have hb : (edgeUpper (∑ j ∈ e, mu j) (nodeQ U N k) : ℝ) ≤ (edgeMax e : ℝ) :=
      by exact_mod_cast hedge e he k
    simpa only [Rat.cast_sum] using hn.trans hb
  · intro i k
    rw [← nodeQ_cast,← widthMultiplierQ_cast]
    exact (sector_upper (widthMultiplierQ_nonneg (outsideGaps E.center) hlam heta i)
      (ha k)).trans (by exact_mod_cast hsector i k)

end N11Formalization.MetricAreaMaskedRationalCertificate
#check @N11Formalization.MetricAreaMaskedRationalCertificate.big_cap_bracket_upper
#check @N11Formalization.MetricAreaMaskedRationalCertificate.arcsin_19_25_le_108_125
#check @N11Formalization.MetricAreaMaskedRationalCertificate.exclude_selected_ear_of_rational_certificate
#print axioms N11Formalization.MetricAreaMaskedRationalCertificate.big_cap_bracket_upper
#print axioms N11Formalization.MetricAreaMaskedRationalCertificate.bracket_108_125_valid
#print axioms N11Formalization.MetricAreaMaskedRationalCertificate.arcsin_19_25_le_108_125
#print axioms N11Formalization.MetricAreaMaskedRationalCertificate.exclude_selected_ear_of_rational_certificate
