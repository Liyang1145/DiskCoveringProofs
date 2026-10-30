import N11Formalization.SevenClassQ0Deg3EdgeShape
import N11Formalization.SevenClassQ0Deg3SectorShape

/-! Lane A: derivative form of the sector upper bracket.

The node table is constant inside each of the eight bins.  On such a bin the
only varying quantity is the grid node, so the analytic shape of a sector row
is governed by `(19/50)^2 * cosHiReal x / 2 - mu`.  This module supplies that
derivative and its monotonicity wrapper; the eight jumps between bins remain
separate exact rational obligations. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorCalculus

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3Mono
open SevenClassQ0Deg3SectorShape

/-- The real upper sector bracket on a fixed node value. -/
def sectorHiReal (mu lam x : ℝ) (a : ℚ) : ℝ :=
  (19 / 50 : ℝ) ^ 2 * sinHiReal x / 2 +
    (2 * (a : ℝ) - ((sinLoNLag (2 * a) : ℚ) : ℝ)) / 2 +
      2 * lam * (a : ℝ) - mu * x

theorem hasDerivAt_sectorHiReal (mu lam x : ℝ) (a : ℚ) :
    HasDerivAt (fun y => sectorHiReal mu lam y a)
      ((19 / 50 : ℝ) ^ 2 * cosHiReal x / 2 - mu) x := by
  have hsin := (hasDerivAt_sinHiReal x).const_mul ((19 / 50 : ℝ) ^ 2 / 2)
  have hlin := (hasDerivAt_id x).const_mul mu
  have hconst : HasDerivAt
      (fun _ : ℝ => (2 * (a : ℝ) - ((sinLoNLag (2 * a) : ℚ) : ℝ)) / 2 +
        2 * lam * (a : ℝ)) 0 x := hasDerivAt_const x _
  refine ((hsin.add hconst).sub hlin).congr_deriv ?_
  simp only [cosHiReal, Pi.sub_apply, id_eq]
  ring

/-- The rational sector bracket is exactly the real bracket after casting. -/
theorem sectorUpper_cast_eq (mu lam q a : ℚ) (hq : 0 ≤ q) :
    ((sectorUpper mu lam q a : ℚ) : ℝ) = sectorHiReal mu lam q a := by
  unfold sectorUpper areaUpper sectorHiReal
  rw [sinHiNLag_cast]
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [abs_of_nonneg hqR]
  push_cast
  ring

/-- Cast bridge from the finite sector table to the fixed-bin real bracket. -/
theorem sectorValue_cast_eq_sectorHiReal (i : Fin 9) (k : Fin 2049) :
    ((sectorValue i k : ℚ) : ℝ) =
      sectorHiReal ((mu (nextSite i) : ℚ) : ℝ) ((lam : ℚ) : ℝ)
        (nodeQ RatInterval.piHi 2048 k) (nodeBin k) := by
  unfold sectorValue
  apply sectorUpper_cast_eq
  unfold nodeQ
  positivity

/-- A nonnegative derivative on an interval makes a fixed-node sector bracket
monotone there. -/
theorem sectorHiReal_monotoneOn_of_deriv_nonneg (mu lam : ℝ) (a : ℚ) {s t : ℝ}
    (hderiv : ∀ x ∈ Set.Ioc s t,
      (19 / 50 : ℝ) ^ 2 * cosHiReal x / 2 - mu ≥ 0) :
    MonotoneOn (fun x => sectorHiReal mu lam x a) (Set.Icc s t) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc s t) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_sectorHiReal mu lam x a).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_sectorHiReal mu lam x a).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_sectorHiReal mu lam x a).deriv]
    exact hderiv x ⟨hx.1.le, hx.2⟩

/-- A nonpositive derivative gives the decreasing half on a fixed-node bin. -/
theorem sectorHiReal_antitoneOn_of_deriv_nonpos (mu lam : ℝ) (a : ℚ) {s t : ℝ}
    (hderiv : ∀ x ∈ Set.Ioc s t,
      (19 / 50 : ℝ) ^ 2 * cosHiReal x / 2 - mu ≤ 0) :
    AntitoneOn (fun x => sectorHiReal mu lam x a) (Set.Icc s t) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc s t) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_sectorHiReal mu lam x a).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_sectorHiReal mu lam x a).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_sectorHiReal mu lam x a).deriv]
    exact hderiv x ⟨hx.1.le, hx.2⟩

/-- A real monotone result for one fixed node value transfers back to an
adjacent step of the rational sector table.  The caller supplies that both
grid points lie in the analytic interval and that the node value is unchanged;
the latter makes the cast bridge applicable at both endpoints. -/
theorem sectorValue_le_of_monotoneOn (i : Fin 9) (k l : Fin 2049)
    (ha : nodeBin k = nodeBin l) {s t : ℝ}
    (hk : s ≤ (nodeQ RatInterval.piHi 2048 k : ℚ))
    (hk' : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ t)
    (hl : s ≤ (nodeQ RatInterval.piHi 2048 l : ℚ))
    (hl' : (nodeQ RatInterval.piHi 2048 l : ℚ) ≤ t)
    (hmono : MonotoneOn
      (fun x => sectorHiReal ((mu (nextSite i) : ℚ) : ℝ) ((lam : ℚ) : ℝ)
        x (nodeBin k)) (Set.Icc s t)) :
    sectorValue i k ≤ sectorValue i l := by
  have hreal := hmono ⟨hk, hk'⟩ ⟨hl, hl'⟩
  have hcast : ((sectorValue i k : ℚ) : ℝ) ≤ ((sectorValue i l : ℚ) : ℝ) := by
    simpa [sectorValue_cast_eq_sectorHiReal, ha] using hreal
  exact_mod_cast hcast

/-- Antitone form of `sectorValue_le_of_monotoneOn`. -/
theorem sectorValue_le_of_antitoneOn (i : Fin 9) (k l : Fin 2049)
    (ha : nodeBin k = nodeBin l) {s t : ℝ}
    (hk : s ≤ (nodeQ RatInterval.piHi 2048 k : ℚ))
    (hk' : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ t)
    (hl : s ≤ (nodeQ RatInterval.piHi 2048 l : ℚ))
    (hl' : (nodeQ RatInterval.piHi 2048 l : ℚ) ≤ t)
    (hanti : AntitoneOn
      (fun x => sectorHiReal ((mu (nextSite i) : ℚ) : ℝ) ((lam : ℚ) : ℝ)
        x (nodeBin k)) (Set.Icc s t)) :
    sectorValue i l ≤ sectorValue i k := by
  have hreal := hanti ⟨hl, hl'⟩ ⟨hk, hk'⟩
  have hcast : ((sectorValue i l : ℚ) : ℝ) ≤ ((sectorValue i k : ℚ) : ℝ) := by
    simpa [sectorValue_cast_eq_sectorHiReal, ha] using hreal
  exact_mod_cast hcast

/-- A lower cosine crossing bound discharges one increasing adjacent sector
step.  The bound is the exact derivative threshold `2*mu/A^2`, with
`A = (19/50)^2`; all node-bin membership conditions remain explicit. -/
theorem sectorValue_le_of_cos_ge (i : Fin 9) (k l : Fin 2049)
    (ha : nodeBin k = nodeBin l) {s t : ℝ}
    (hk : s ≤ (nodeQ RatInterval.piHi 2048 k : ℚ))
    (hk' : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ t)
    (hl : s ≤ (nodeQ RatInterval.piHi 2048 l : ℚ))
    (hl' : (nodeQ RatInterval.piHi 2048 l : ℚ) ≤ t)
    (hcos : ∀ x ∈ Set.Ioc s t,
      2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x) :
    sectorValue i k ≤ sectorValue i l := by
  apply sectorValue_le_of_monotoneOn i k l ha hk hk' hl hl'
  apply sectorHiReal_monotoneOn_of_deriv_nonneg
  intro x hx
  have hA : (0 : ℝ) < (19 / 50 : ℝ) ^ 2 := by norm_num
  have hm := mul_le_mul_of_nonneg_left (hcos x hx) hA.le
  nlinarith

/-- Upper cosine crossing bound form for a decreasing adjacent sector step. -/
theorem sectorValue_le_of_cos_le (i : Fin 9) (k l : Fin 2049)
    (ha : nodeBin k = nodeBin l) {s t : ℝ}
    (hk : s ≤ (nodeQ RatInterval.piHi 2048 k : ℚ))
    (hk' : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ t)
    (hl : s ≤ (nodeQ RatInterval.piHi 2048 l : ℚ))
    (hl' : (nodeQ RatInterval.piHi 2048 l : ℚ) ≤ t)
    (hcos : ∀ x ∈ Set.Ioc s t,
      cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2) :
    sectorValue i l ≤ sectorValue i k := by
  apply sectorValue_le_of_antitoneOn i k l ha hk hk' hl hl'
  apply sectorHiReal_antitoneOn_of_deriv_nonpos
  intro x hx
  have hA : (0 : ℝ) < (19 / 50 : ℝ) ^ 2 := by norm_num
  have hm := mul_le_mul_of_nonneg_left (hcos x hx) hA.le
  nlinarith

end N11Formalization.SevenClassQ0Deg3SectorCalculus
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorUpper_cast_eq
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorValue_cast_eq_sectorHiReal
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.hasDerivAt_sectorHiReal
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorHiReal_monotoneOn_of_deriv_nonneg
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorHiReal_antitoneOn_of_deriv_nonpos
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorValue_le_of_monotoneOn
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorValue_le_of_antitoneOn
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorValue_le_of_cos_ge
#check @N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorValue_le_of_cos_le
#print axioms N11Formalization.SevenClassQ0Deg3SectorCalculus.sectorHiReal_monotoneOn_of_deriv_nonneg
