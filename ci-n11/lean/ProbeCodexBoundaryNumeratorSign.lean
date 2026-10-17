import N11Formalization.SourceBoundaryMultiplierIntervals
open N11Formalization
open N11Formalization.SourceBoundaryMultiplierIntervals

-- Diagnostic evaluation is NOT a proof input; the exact closed inequalities
-- below must be checked by Lean's kernel, with no native_decide.
macro "sign_eval" : tactic =>
  `(tactic|
    (simp only [numeratorBox,fanBox,normalPBox,normalQBox,normalCBox,innerBox,
      centralBox,velocityBox,widthQ,directionQ,ringBox,pinBox,wBox,slopeBox,
      slopeDen,rounded,N11Formalization.SourceBoundarySignBounds.contact,
      N11Formalization.SourceBoundarySignBounds.compactA,
      N11Formalization.SourceBoundarySignBounds.compactB,
      N11Formalization.RatInterval.div,N11Formalization.RatInterval.inv,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     nd_eval))
theorem sign0 : (numeratorBox 0).hi < 0 := by sign_eval
theorem sign1 : (numeratorBox 1).hi < 0 := by sign_eval
theorem sign2 : (numeratorBox 2).hi < 0 := by sign_eval
theorem sign3 : (numeratorBox 3).hi < 0 := by sign_eval
theorem sign4 : (numeratorBox 4).hi < 0 := by sign_eval
#print axioms sign0
#print axioms sign4
