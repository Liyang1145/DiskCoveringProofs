import N11Formalization.SourceRefinedFanCoefficientBounds
import N11Formalization.SourceBoundaryMultiplierIntervals

/-! Higher-resolution source geometry/true-LENGTH numerator intervals.
Rounding grid10^8 instead of10^5, and sharper actual fan coefficients.
Every interval still contains SAME genuine source derivative/velocity. No
replacement of sourceRoot, stress or multiplier by a rounded centre. -/
set_option autoImplicit false
namespace N11Formalization.SourceRefinedBoundaryIntervals
open N11Formalization RatInterval SourceFrameVelocity SourceBoundaryMultiplierFormula
noncomputable section

def fine (I : RatInterval) : RatInterval :=
  ⟨(⌊I.lo*100000000⌋ : ℚ)/100000000,
    (⌈I.hi*100000000⌉ : ℚ)/100000000⟩

theorem fine_contains (I : RatInterval) : Contains (fine I) I := by
  constructor
  · change (⌊I.lo*100000000⌋ : ℚ)/100000000≤I.lo
    exact (div_le_iff₀ (by norm_num : (0 : ℚ)<100000000)).mpr (Int.floor_le _)
  · change I.hi≤(⌈I.hi*100000000⌉ : ℚ)/100000000
    exact (le_div_iff₀ (by norm_num : (0 : ℚ)<100000000)).mpr (Int.le_ceil _)

theorem fine_mem {I : RatInterval} {x : ℝ} (h : I.Mem x) : (fine I).Mem x :=
  mem_of_contains (fine_contains I) h

def ringBox (k : Fin 9) (q : Fin 2) := fine (ndRingBox ndBox k q)
def pinBox (k : Fin 9) (q : Fin 2) := fine (ndUvecBox ndBox k q)
def wBox (q : Fin 2) := fine (ndWPointBox ndBox q)
def slopeDen : RatInterval :=
  fine (sqrt (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 4)))))

theorem slopeDen_pos : 0<slopeDen.lo := by
  unfold slopeDen fine
  nd_eval

def slopeBox : RatInterval :=
  fine (div (mul (fine (sinTotLag (ndAngleBox ndBox 4)))
    (fine (ndRhoBox ndBox 4))) slopeDen (Or.inr slopeDen_pos))

theorem slopeBox_mem : slopeBox.Mem (SourceFrameVelocity.slopeA 4) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hden := fine_mem (sqrt_mem
    (sub_mem (sq_mem_pow (hb 6)) (sq_mem_pow (sinTotLag_mem (ndAngleBox_mem hb 4)))))
  have h := fine_mem (div_mem
    (mul_mem (fine_mem (sinTotLag_mem (ndAngleBox_mem hb 4)))
      (fine_mem (ndRhoBox_mem hb 4))) hden (Or.inr slopeDen_pos))
  change slopeBox.Mem
    (Real.sin (angleVec SourceExactRoot.sourceRoot 4)*rhoK SourceExactRoot.sourceRoot 4/
      Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-
        Real.sin (angleVec SourceExactRoot.sourceRoot 4)^2)) at h
  exact h

def velocityBox (j : Fin 5) (k : Fin 9) (q : Fin 2) : RatInterval :=
  if k=4 then if q=0 then
      mul slopeBox (ofRat (SourceBoundaryMultiplierIntervals.widthQ j)) else ofRat 0
  else if q=0 then mul (neg (ringBox k 1))
      (ofRat (SourceBoundaryMultiplierIntervals.directionQ j k))
    else mul (ringBox k 0) (ofRat (SourceBoundaryMultiplierIntervals.directionQ j k))

theorem velocityBox_mem (j : Fin 5) (k : Fin 9) (q : Fin 2) :
    (velocityBox j k q).Mem ((velocity k (testDirection j)) q) := by
  rw [SourceBoundaryMultiplierIntervals.velocity_test]
  unfold velocityBox
  by_cases hk : k=4
  · rw [if_pos hk,if_pos hk]
    fin_cases q
    · exact mul_mem slopeBox_mem (ofRat_mem _)
    · rw [if_neg (by decide)]
      change (ofRat 0).Mem (0 : ℝ)
      simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
  · rw [if_neg hk,if_neg hk]
    have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
    fin_cases q
    · exact mul_mem (neg_mem (fine_mem (ndRingBox_mem hb k 1))) (ofRat_mem _)
    · exact mul_mem (fine_mem (ndRingBox_mem hb k 0)) (ofRat_mem _)

def normalPBox (k : Fin 9) (q : Fin 2) := sub (pinBox k q) (ringBox k q)
def normalQBox (k : Fin 9) (q : Fin 2) := sub (pinBox k q) (ringBox (k+1) q)
def normalCBox (q : Fin 2) := sub (wBox q) (ringBox 6 q)

def fanBox (i : Fin 4) (j : Fin 5) : RatInterval :=
  add (mul (SourceRefinedFanCoefficientBounds.ABox i)
    (SourceBoundaryMultiplierIntervals.innerBox
      (normalPBox (SourceBoundarySignBounds.contact i))
      (velocityBox j (SourceBoundarySignBounds.contact i))))
    (mul (SourceRefinedFanCoefficientBounds.BBox i)
      (SourceBoundaryMultiplierIntervals.innerBox
        (normalQBox (SourceBoundarySignBounds.contact i))
        (velocityBox j (SourceBoundarySignBounds.contact i+1))))

theorem fanBox_mem (i : Fin 4) (j : Fin 5) :
    (fanBox i j).Mem (fanNumerator (SourceBoundarySignBounds.contact i) j) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hp (k : Fin 9) (q : Fin 2) :
      (normalPBox k q).Mem (SourceFanLengthCovector.normalP k q) :=
    sub_mem (fine_mem (ndUvecBox_mem hb k q)) (fine_mem (ndRingBox_mem hb k q))
  have hq (k : Fin 9) (q : Fin 2) :
      (normalQBox k q).Mem (SourceFanLengthCovector.normalQ k q) :=
    sub_mem (fine_mem (ndUvecBox_mem hb k q)) (fine_mem (ndRingBox_mem hb (k+1) q))
  exact add_mem
    (mul_mem (SourceRefinedFanCoefficientBounds.refined_membership i).1
      (SourceBoundaryMultiplierIntervals.innerBox_mem (hp _) (velocityBox_mem j _)))
    (mul_mem (SourceRefinedFanCoefficientBounds.refined_membership i).2
      (SourceBoundaryMultiplierIntervals.innerBox_mem (hq _) (velocityBox_mem j _)))

def centralBox (j : Fin 5) : RatInterval :=
  SourceBoundaryMultiplierIntervals.innerBox normalCBox (velocityBox j 6)

theorem centralBox_mem (j : Fin 5) :
    (centralBox j).Mem (inner ℝ SourceCentralGeometry.nH (velocity 6 (testDirection j))) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact SourceBoundaryMultiplierIntervals.innerBox_mem
    (fun q => sub_mem (fine_mem (ndWPointBox_mem hb q)) (fine_mem (ndRingBox_mem hb 6 q)))
    (velocityBox_mem j 6)

def numeratorBox (j : Fin 5) : RatInterval :=
  add (neg (add (add (add
    (mul (ndBox 7) (fanBox 0 j)) (mul (ndBox 8) (fanBox 1 j)))
    (mul (ndBox 9) (fanBox 2 j))) (mul (ndBox 10) (fanBox 3 j))))
    (mul (ndBox 11) (centralBox j))

/-- All5 higher-resolution boxes contain the actual genuine LENGTH numerator.
No finite readout, narrower H20 error or coercivity is inferred by membership. -/
theorem numeratorBox_mem (j : Fin 5) : (numeratorBox j).Mem (numerator j) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact add_mem (neg_mem (add_mem (add_mem (add_mem
    (mul_mem (hb 7) (fanBox_mem 0 j)) (mul_mem (hb 8) (fanBox_mem 1 j)))
    (mul_mem (hb 9) (fanBox_mem 2 j))) (mul_mem (hb 10) (fanBox_mem 3 j))))
    (mul_mem (hb 11) (centralBox_mem j))

end
end N11Formalization.SourceRefinedBoundaryIntervals
#check @N11Formalization.SourceRefinedBoundaryIntervals.numeratorBox_mem
#print axioms N11Formalization.SourceRefinedBoundaryIntervals.numeratorBox_mem
