import N11Formalization.SourceBoundaryMultiplierFormula

/-! Sound rational interval expressions for the ACTUAL boundary multiplier
numerators. Rounding only widens expression-tree boxes; no endpoint replaces
the source root. Final strict sign readouts are separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryMultiplierIntervals
open N11Formalization RatInterval SourceFrameVelocity SourceBoundaryMultiplierFormula
noncomputable section

def rounded (I : RatInterval) : RatInterval :=
  ⟨(⌊I.lo*100000⌋ : ℚ)/100000, (⌈I.hi*100000⌉ : ℚ)/100000⟩

theorem rounded_contains (I : RatInterval) : Contains (rounded I) I := by
  constructor
  · change (⌊I.lo*100000⌋ : ℚ)/100000 ≤ I.lo
    exact (div_le_iff₀ (by norm_num : (0 : ℚ)<100000)).mpr (Int.floor_le _)
  · change I.hi ≤ (⌈I.hi*100000⌉ : ℚ)/100000
    exact (le_div_iff₀ (by norm_num : (0 : ℚ)<100000)).mpr (Int.le_ceil _)

theorem rounded_mem {I : RatInterval} {x : ℝ} (h : I.Mem x) :
    (rounded I).Mem x := mem_of_contains (rounded_contains I) h

def ringBox (k : Fin 9) (q : Fin 2) := rounded (ndRingBox ndBox k q)
def pinBox (k : Fin 9) (q : Fin 2) := rounded (ndUvecBox ndBox k q)
def wBox (q : Fin 2) := rounded (ndWPointBox ndBox q)
def slopeDen : RatInterval :=
  rounded (sqrt (sub (sq (ndBox 6)) (sq (sinTotLag (ndAngleBox ndBox 4)))))

theorem slopeDen_pos : 0<slopeDen.lo := by
  unfold slopeDen rounded
  nd_eval

def slopeBox : RatInterval :=
  rounded (div (mul (rounded (sinTotLag (ndAngleBox ndBox 4)))
    (rounded (ndRhoBox ndBox 4))) slopeDen (Or.inr slopeDen_pos))

theorem slopeBox_mem : slopeBox.Mem (SourceFrameVelocity.slopeA 4) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hden := rounded_mem (sqrt_mem
    (sub_mem (sq_mem_pow (hb 6)) (sq_mem_pow (sinTotLag_mem (ndAngleBox_mem hb 4)))))
  have h := rounded_mem (div_mem
    (mul_mem (rounded_mem (sinTotLag_mem (ndAngleBox_mem hb 4)))
      (rounded_mem (ndRhoBox_mem hb 4))) hden (Or.inr slopeDen_pos))
  change slopeBox.Mem
    (Real.sin (angleVec SourceExactRoot.sourceRoot 4)*rhoK SourceExactRoot.sourceRoot 4/
      Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-
        Real.sin (angleVec SourceExactRoot.sourceRoot 4)^2)) at h
  exact h

def widthQ (j : Fin 5) : ℚ := if j=4 then -1/2 else -1
def directionQ (j : Fin 5) (k : Fin 9) : ℚ :=
  ![![0,1,1,1,0,-1,-1,-1,0],
    ![0,0,1,1,0,-1,-1,0,0],
    ![0,0,0,1,0,-1,0,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![1/2,1/2,1/2,1/2,0,-1/2,-1/2,-1/2,-1/2]] j k

theorem widths_test (j : Fin 5) (k : Fin 9) :
    PhysicalResidualFrame.widths (testDirection j) k=
      if k=4 then (widthQ j : ℝ) else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [testDirection,BoundaryChartLinear.rightInverse,PhysicalResidualFrame.widths,
      widthQ,Pi.single_apply,Fin.ext_iff] <;> norm_num

theorem directions_test (j : Fin 5) (k : Fin 9) :
    PhysicalResidualFrame.directions (testDirection j) k=(directionQ j k : ℝ) := by
  fin_cases j <;> fin_cases k <;>
    simp [testDirection,BoundaryChartLinear.rightInverse,PhysicalResidualFrame.directions,
      directionQ,Pi.single_apply,Fin.ext_iff] <;> norm_num

theorem velocity_test (j : Fin 5) (k : Fin 9) :
    velocity k (testDirection j)=
      if k=4 then !₂[SourceFrameVelocity.slopeA 4*(widthQ j : ℝ),0]
      else !₂[-(ringCenter SourceExactRoot.sourceRoot k) 1*(directionQ j k : ℝ),
        (ringCenter SourceExactRoot.sourceRoot k) 0*(directionQ j k : ℝ)] := by
  unfold velocity radialVelocity
  rw [widths_test,directions_test,testDirection_radius]
  by_cases hk : k=4
  · subst k
    fin_cases j <;> simp [thetaOf_four,Fin.ext_iff,directionQ]
  · simp only [if_neg hk,mul_zero,add_zero,zero_mul,zero_sub,
      ringCenter_coord0,ringCenter_coord1]
    ext q
    fin_cases q <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] <;> ring

def velocityBox (j : Fin 5) (k : Fin 9) (q : Fin 2) : RatInterval :=
  if k=4 then if q=0 then mul slopeBox (ofRat (widthQ j)) else ofRat 0
  else if q=0 then mul (neg (ringBox k 1)) (ofRat (directionQ j k))
    else mul (ringBox k 0) (ofRat (directionQ j k))

theorem velocityBox_mem (j : Fin 5) (k : Fin 9) (q : Fin 2) :
    (velocityBox j k q).Mem ((velocity k (testDirection j)) q) := by
  rw [velocity_test]
  unfold velocityBox
  by_cases hk : k=4
  · rw [if_pos hk,if_pos hk]
    fin_cases q
    · exact mul_mem slopeBox_mem (ofRat_mem _)
    · simpa using ofRat_mem (0 : ℚ)
  · rw [if_neg hk,if_neg hk]
    have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
    fin_cases q
    · exact mul_mem (neg_mem (rounded_mem (ndRingBox_mem hb k 1))) (ofRat_mem _)
    · exact mul_mem (rounded_mem (ndRingBox_mem hb k 0)) (ofRat_mem _)

def normalPBox (k : Fin 9) (q : Fin 2) := sub (pinBox k q) (ringBox k q)
def normalQBox (k : Fin 9) (q : Fin 2) := sub (pinBox k q) (ringBox (k+1) q)
def normalCBox (q : Fin 2) := sub (wBox q) (ringBox 6 q)

def innerBox (A B : Fin 2 → RatInterval) : RatInterval :=
  add (mul (A 0) (B 0)) (mul (A 1) (B 1))

theorem innerBox_mem {p q : Point} {A B : Fin 2 → RatInterval}
    (hA : ∀ i,(A i).Mem (p i)) (hB : ∀ i,(B i).Mem (q i)) :
    (innerBox A B).Mem (inner ℝ p q) := by
  rw [PinTangentGeometry.inner_coords]
  exact add_mem (mul_mem (hA 0) (hB 0)) (mul_mem (hA 1) (hB 1))

def fanBox (i : Fin 4) (j : Fin 5) : RatInterval :=
  add (mul (SourceBoundarySignBounds.compactA i)
    (innerBox (normalPBox (SourceBoundarySignBounds.contact i))
      (velocityBox j (SourceBoundarySignBounds.contact i))))
    (mul (SourceBoundarySignBounds.compactB i)
      (innerBox (normalQBox (SourceBoundarySignBounds.contact i))
        (velocityBox j (SourceBoundarySignBounds.contact i+1))))

theorem fanBox_mem (i : Fin 4) (j : Fin 5) :
    (fanBox i j).Mem (fanNumerator (SourceBoundarySignBounds.contact i) j) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hP (k : Fin 9) (q : Fin 2) :
      (normalPBox k q).Mem (SourceFanLengthCovector.normalP k q) :=
    sub_mem (rounded_mem (ndUvecBox_mem hb k q)) (rounded_mem (ndRingBox_mem hb k q))
  have hQ (k : Fin 9) (q : Fin 2) :
      (normalQBox k q).Mem (SourceFanLengthCovector.normalQ k q) :=
    sub_mem (rounded_mem (ndUvecBox_mem hb k q)) (rounded_mem (ndRingBox_mem hb (k+1) q))
  exact add_mem
    (mul_mem (SourceBoundarySignBounds.compact_membership i).1
      (innerBox_mem (hP _) (velocityBox_mem j _)))
    (mul_mem (SourceBoundarySignBounds.compact_membership i).2
      (innerBox_mem (hQ _) (velocityBox_mem j _)))

def centralBox (j : Fin 5) : RatInterval := innerBox normalCBox (velocityBox j 6)

theorem centralBox_mem (j : Fin 5) :
    (centralBox j).Mem (inner ℝ SourceCentralGeometry.nH (velocity 6 (testDirection j))) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact innerBox_mem (fun q => sub_mem (rounded_mem (ndWPointBox_mem hb q))
    (rounded_mem (ndRingBox_mem hb 6 q))) (velocityBox_mem j 6)

def numeratorBox (j : Fin 5) : RatInterval :=
  add (neg (add (add (add
    (mul (ndBox 7) (fanBox 0 j)) (mul (ndBox 8) (fanBox 1 j)))
    (mul (ndBox 9) (fanBox 2 j))) (mul (ndBox 10) (fanBox 3 j))))
    (mul (ndBox 11) (centralBox j))

theorem numeratorBox_mem (j : Fin 5) : (numeratorBox j).Mem (numerator j) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact add_mem (neg_mem (add_mem (add_mem (add_mem
    (mul_mem (hb 7) (fanBox_mem 0 j)) (mul_mem (hb 8) (fanBox_mem 1 j)))
    (mul_mem (hb 9) (fanBox_mem 2 j))) (mul_mem (hb 10) (fanBox_mem 3 j))))
    (mul_mem (hb 11) (centralBox_mem j))

end
end N11Formalization.SourceBoundaryMultiplierIntervals
#check @N11Formalization.SourceBoundaryMultiplierIntervals.numeratorBox_mem
#print axioms N11Formalization.SourceBoundaryMultiplierIntervals.numeratorBox_mem
