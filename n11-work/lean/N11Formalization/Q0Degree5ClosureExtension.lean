import N11Formalization.Q0Degree5SourceData
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import N11Formalization.ActualCanonicalMomentTransport
import N11Formalization.ActualSectorMetricDomain
import N11Formalization.ActualCanonicalSharedMomentConsumer

/-! Exact closure-extension data for q0(5,8).

The source dual has nine closure multipliers that are absent from
`CanonicalCoeffQ`.  This module binds those exact source values and records the
three additive terms needed by a closure-aware certificate: the switch term,
the sector term, and the negative-pi constant.  No factor bound, strict total,
or exclusion is asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Q0Degree5ClosureExtension

open ActualOrderedMetricGraphs ActualCanonicalMomentTransport
open ActualMetricAngleAtoms ActualSectorMetricDomain
open ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualOwnedSectorDecomposition ActualBoundaryCyclicOrder ActualRingLinkBoundaryData
open ActualCanonicalSharedMomentConsumer SharedMomentFactorGridCertificate

abbrev ClosureVector := Fin 9 → ℚ

def closure : ClosureVector := Q0Degree5SourceData.closure

theorem closure_nonnegative : ∀ i : Fin 9, 0 ≤ closure i := by
  decide +kernel

theorem closure_sum_pos : 0 < ∑ i : Fin 9, closure i := by
  decide +kernel

/-- Additive factor term contributed by closure `i` at switch angle `t`. -/
def switchTerm (w : ClosureVector) (i : Fin 9) (t : ℝ) : ℝ :=
  2*t*(w i : ℝ)

/-- Additive factor term contributed by the two adjacent closure multipliers
to sector `i`.  The caller supplies the exact normalized endpoint angles and
the exact sector width. -/
def sectorTerm (w : ClosureVector) (i : Fin 9) (left right width : ℝ) : ℝ :=
  (w (i-1) : ℝ)*(left+width/2)+(w i : ℝ)*(right+width/2)

/-- Constant term contributed by the nine closure multipliers. -/
def constantTerm (w : ClosureVector) : ℝ :=
  -(Real.pi*(∑ i : Fin 9, (w i : ℝ)))

theorem degree5_sectorTerm_formula (i : Fin 9) (left right width : ℝ) :
    sectorTerm closure i left right width =
      (Q0Degree5SourceData.closure (i-1) : ℝ)*(left+width/2)+
        (Q0Degree5SourceData.closure i : ℝ)*(right+width/2) := rfl

theorem degree5_switchTerm_formula (i : Fin 9) (t : ℝ) :
    switchTerm closure i t = 2*t*(Q0Degree5SourceData.closure i : ℝ) := rfl

theorem degree5_constantTerm_formula :
    constantTerm closure =
      -(Real.pi*(∑ i : Fin 9, (Q0Degree5SourceData.closure i : ℝ))) := rfl

/-- The base angle at the left endpoint `A = switchPoint i` of sector `i`
(triangle `A-C-B`, with `C = c(nextSite i)`). -/
def leftBaseAngle {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  EuclideanGeometry.angle (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))

/-- The base angle at the right endpoint `B = switchPoint (i+1)` of sector `i`. -/
def rightBaseAngle {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  EuclideanGeometry.angle (c (nextSite i)) (switchPoint v (nextRing i)) (switchPoint v i)

theorem leftBaseAngle_nonnegative {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) : 0 ≤ leftBaseAngle v i :=
  EuclideanGeometry.angle_nonneg _ _ _

theorem rightBaseAngle_nonnegative {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) : 0 ≤ rightBaseAngle v i :=
  EuclideanGeometry.angle_nonneg _ _ _

theorem switchTerm_nonnegative (i : Fin 9) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ switchTerm closure i t := by
  have hw := closure_nonnegative i
  unfold switchTerm
  exact mul_nonneg (mul_nonneg (by norm_num) ht) (by exact_mod_cast hw)

theorem sectorTerm_nonnegative (i : Fin 9) {left right width : ℝ}
    (hleft : 0 ≤ left) (hright : 0 ≤ right) (hwidth : 0 ≤ width) :
    0 ≤ sectorTerm closure i left right width := by
  have hwleft := closure_nonnegative (i-1)
  have hwright := closure_nonnegative i
  have hleft' : 0 ≤ left+width/2 := by positivity
  have hright' : 0 ≤ right+width/2 := by positivity
  unfold sectorTerm
  exact add_nonneg (mul_nonneg (by exact_mod_cast hwleft) hleft')
    (mul_nonneg (by exact_mod_cast hwright) hright')

/-- A source closure-switch bound bounds the underlying canonical switch
objective, because the added closure term is nonnegative on the switch domain. -/
theorem switchObjective_le_of_augmented {objective bound : ℝ} (i : Fin 9)
    {t : ℝ} (ht : 0 ≤ t) (h : objective+switchTerm closure i t ≤ bound) :
    objective ≤ bound :=
  (le_add_of_nonneg_right (switchTerm_nonnegative i ht)).trans h

/-- The analogous lifting lemma for a sector factor bound. -/
theorem sectorObjective_le_of_augmented {objective bound : ℝ} (i : Fin 9)
    {left right width : ℝ} (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hwidth : 0 ≤ width)
    (h : objective+sectorTerm closure i left right width ≤ bound) :
    objective ≤ bound :=
  (le_add_of_nonneg_right
    (sectorTerm_nonnegative i hleft hright hwidth)).trans h

/-- Generic sector coordinates for the source closure term.  The source
emitter evaluates the left/right base angles (and width) from each box point. -/
structure ClosureSectorCoordinates where
  leftBase : ℝ → ℝ → ℝ → ℝ
  rightBase : ℝ → ℝ → ℝ → ℝ
  width : ℝ → ℝ → ℝ → ℝ

/-- The source emitter's normalized chord length, transcribed with exact
`sqrt`/`cos` operations (no decimal evaluation). -/
def sourceSectorChordLength (a u v : ℝ) : ℝ :=
  Real.sqrt (u^2+v^2-2*u*v*Real.cos a)

/-- The source emitter's exact normalized sector width. -/
def sourceSectorWidth (a u v : ℝ) : ℝ :=
  2*Real.arcsin ((19/50 : ℝ)*sourceSectorChordLength a u v/2)

/-- The source emitter's left base angle, using `Complex.arg` for its
two-argument arctangent. -/
def sourceLeftBaseAngle (a u v : ℝ) : ℝ :=
  Complex.arg ⟨u-v*Real.cos a, v*Real.sin a⟩

/-- The source emitter's right base angle, using `Complex.arg` for its
two-argument arctangent. -/
def sourceRightBaseAngle (a u v : ℝ) : ℝ :=
  Complex.arg ⟨v-u*Real.cos a, u*Real.sin a⟩

/-- The exact box-coordinate functions used by the source closure dual. -/
def sourceSectorCoordinates : ClosureSectorCoordinates where
  leftBase := sourceLeftBaseAngle
  rightBase := sourceRightBaseAngle
  width := sourceSectorWidth

theorem sourceLeftBaseAngle_nonnegative {a u v : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) Real.pi) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sourceLeftBaseAngle a u v := by
  rw [sourceLeftBaseAngle, Complex.arg_nonneg_iff]
  exact mul_nonneg hv.1 (Real.sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2)

theorem sourceRightBaseAngle_nonnegative {a u v : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) Real.pi) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sourceRightBaseAngle a u v := by
  rw [sourceRightBaseAngle, Complex.arg_nonneg_iff]
  exact mul_nonneg hu.1 (Real.sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2)

theorem sourceLeftBaseAngle_le_pi (a u v : ℝ) :
    sourceLeftBaseAngle a u v ≤ Real.pi :=
  Complex.arg_le_pi _

theorem sourceRightBaseAngle_le_pi (a u v : ℝ) :
    sourceRightBaseAngle a u v ≤ Real.pi :=
  Complex.arg_le_pi _

theorem sourceSectorWidth_nonnegative (a u v : ℝ) :
    0 ≤ sourceSectorWidth a u v := by
  unfold sourceSectorWidth
  apply mul_nonneg (by norm_num)
  apply Real.arcsin_nonneg.mpr
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by norm_num)

theorem sourceSectorWidth_le_pi (a u v : ℝ) :
    sourceSectorWidth a u v ≤ Real.pi := by
  unfold sourceSectorWidth
  calc
    2 * Real.arcsin ((19 / 50 : ℝ) * sourceSectorChordLength a u v / 2) ≤
        2 * (Real.pi / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.arcsin_le_pi_div_two _) (by norm_num)
    _ = Real.pi := by ring

/-- Full-domain factor bounds for the source certificate, retaining the nine
closure multipliers.  The switch and sector fields add the exact source
closure terms before comparing with the same rational maxima used by
`CanonicalFactorBounds`. -/
structure ClosureFactorBounds {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ)
    (ear : Fin 9) (eta : ℚ) (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (S : ClosureSectorCoordinates) : Prop where
  face : ∀ (f : F) (a : Fin 3 → ℝ),
    (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (canonicalFaceP D kap f s : ℝ))
        (fun s => (canonicalFaceQ D f s : ℝ)) (fun s => (canonicalFaceB D f s : ℝ)) a y ≤ faceMax f
  switch : ∀ (i : Fin 9) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective (canonicalSwitchP D kap i) (canonicalSwitchQ D i) (canonicalSwitchB D i)
        (canonicalSwitchD2 D i) (canonicalSwitchD1 D i) t y+
        switchTerm closure i t ≤ switchMax i
  sector : ∀ (i : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      MetricSectorBoxCertificate.sectorObjective (canonicalSectorC D ear eta i)
        (D.mu (nextSite i)) (D.leftSecond i) (D.rightSecond i)
        (D.leftFirst i) (D.rightFirst i) a u v+
        sectorTerm closure i (S.leftBase a u v) (S.rightBase a u v) (S.width a u v) ≤
          sectorMax i
  sectorLeft_nonnegative : ∀ a u v, a ∈ Set.Icc (0 : ℝ) Real.pi →
    u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ S.leftBase a u v
  sectorRight_nonnegative : ∀ a u v, a ∈ Set.Icc (0 : ℝ) Real.pi →
    u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ S.rightBase a u v
  sectorWidth_nonnegative : ∀ a u v, a ∈ Set.Icc (0 : ℝ) Real.pi →
    u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ S.width a u v

/-- Remove the nonnegative closure terms from closure-aware bounds, recovering
the unchanged canonical factor interface. -/
def ClosureFactorBounds.toCanonical {F : Finset (Finset (Fin 11))}
    {D : CanonicalCoeffQ F} {kap : Finset (Fin 11) → ℚ}
    {ear : Fin 9} {eta : ℚ} {faceMax : F → ℚ} {switchMax sectorMax : Fin 9 → ℚ}
    {S : ClosureSectorCoordinates}
    (H : ClosureFactorBounds D kap ear eta faceMax switchMax sectorMax S) :
    CanonicalFactorBounds D kap ear eta faceMax switchMax sectorMax := by
  refine ⟨H.face, ?_, ?_⟩
  · intro i t ht y hy
    exact switchObjective_le_of_augmented i ht.1 (H.switch i t ht y hy)
  · intro i a ha u hu v hv
    exact sectorObjective_le_of_augmented i
      (H.sectorLeft_nonnegative a u v ha hu hv)
      (H.sectorRight_nonnegative a u v ha hu hv)
      (H.sectorWidth_nonnegative a u v ha hu hv)
      (H.sector i a ha u hu v hv)

def closureTotalUpperQ {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℚ :=
  canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax

def closureTotalUpper {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℝ :=
  (closureTotalUpperQ D kap eta alpha faceMax switchMax sectorMax : ℝ)+constantTerm closure

/-- Complete premises of a closure-aware source certificate.  Only the factor
bounds differ from `CanonicalCertificate`; the rational strict total remains
the unchanged base total. -/
structure ClosureCertificate {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta alpha : ℚ)
    (S : ClosureSectorCoordinates) where
  faceMax : F → ℚ
  switchMax : Fin 9 → ℚ
  sectorMax : Fin 9 → ℚ
  balance : CanonicalMaskBalancedQ D
  edge_nonnegative : ∀ e ∈ faceEdges F, 0 ≤ kap e
  eta_nonnegative : 0 ≤ eta
  bracket : EarAsinBracket alpha
  bounds : ClosureFactorBounds D kap ear eta faceMax switchMax sectorMax S
  strict : canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax < RatInterval.piLo

/-- Convert a closure-aware source certificate to the unchanged canonical
consumer, eliminating the nine multiplier terms through nonnegativity. -/
def ClosureCertificate.toCanonical {F : Finset (Finset (Fin 11))}
    {D : CanonicalCoeffQ F} {kap : Finset (Fin 11) → ℚ} {ear : Fin 9}
    {eta alpha : ℚ} {S : ClosureSectorCoordinates}
    (K : ClosureCertificate D kap ear eta alpha S) :
    CanonicalCertificate D kap ear eta alpha where
  faceMax := K.faceMax
  switchMax := K.switchMax
  sectorMax := K.sectorMax
  balance := K.balance
  edge_nonnegative := K.edge_nonnegative
  eta_nonnegative := K.eta_nonnegative
  bracket := K.bracket
  bounds := K.bounds.toCanonical
  strict := K.strict

theorem ClosureCertificate.total_lt_pi {F : Finset (Finset (Fin 11))}
    {D : CanonicalCoeffQ F} {kap : Finset (Fin 11) → ℚ} {ear : Fin 9}
    {eta alpha : ℚ} {S : ClosureSectorCoordinates}
    (K : ClosureCertificate D kap ear eta alpha S) :
    closureTotalUpper D kap eta alpha K.faceMax K.switchMax K.sectorMax < Real.pi :=
  closureTotalUpper_lt_pi D kap eta alpha K.faceMax K.switchMax K.sectorMax K.strict

theorem constantTerm_nonpositive : constantTerm closure ≤ 0 := by
  have hs : 0 ≤ ∑ i : Fin 9, (closure i : ℝ) :=
    Finset.sum_nonneg fun i _ => by exact_mod_cast closure_nonnegative i
  unfold constantTerm
  nlinarith [mul_nonneg Real.pi_pos.le hs]

theorem closureTotalUpper_lt_pi {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ)
    (faceMax : F → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (h : canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax < RatInterval.piLo) :
    closureTotalUpper D kap eta alpha faceMax switchMax sectorMax < Real.pi := by
  have hh : (canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax : ℝ) <
      (RatInterval.piLo : ℝ) := Rat.cast_lt.mpr h
  have hp := hh.trans RatInterval.piLo_lt_pi
  have hc := constantTerm_nonpositive
  unfold closureTotalUpper
  linarith

end N11Formalization.Q0Degree5ClosureExtension
#check @N11Formalization.Q0Degree5ClosureExtension.closure_nonnegative
#check @N11Formalization.Q0Degree5ClosureExtension.closure_sum_pos
#check @N11Formalization.Q0Degree5ClosureExtension.degree5_sectorTerm_formula
#check @N11Formalization.Q0Degree5ClosureExtension.degree5_switchTerm_formula
#check @N11Formalization.Q0Degree5ClosureExtension.degree5_constantTerm_formula
#check @N11Formalization.Q0Degree5ClosureExtension.leftBaseAngle_nonnegative
#check @N11Formalization.Q0Degree5ClosureExtension.rightBaseAngle_nonnegative
#check @N11Formalization.Q0Degree5ClosureExtension.switchTerm_nonnegative
#check @N11Formalization.Q0Degree5ClosureExtension.sectorTerm_nonnegative
#check @N11Formalization.Q0Degree5ClosureExtension.switchObjective_le_of_augmented
#check @N11Formalization.Q0Degree5ClosureExtension.sectorObjective_le_of_augmented
#check @N11Formalization.Q0Degree5ClosureExtension.ClosureFactorBounds
#check @N11Formalization.Q0Degree5ClosureExtension.ClosureFactorBounds.toCanonical
#check @N11Formalization.Q0Degree5ClosureExtension.ClosureCertificate
#check @N11Formalization.Q0Degree5ClosureExtension.ClosureCertificate.toCanonical
#check @N11Formalization.Q0Degree5ClosureExtension.ClosureCertificate.total_lt_pi
#check @N11Formalization.Q0Degree5ClosureExtension.constantTerm_nonpositive
#check @N11Formalization.Q0Degree5ClosureExtension.closureTotalUpper_lt_pi
