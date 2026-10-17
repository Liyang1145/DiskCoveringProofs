import N11Formalization.SourceRefinedBoundaryIntervals
import N11Formalization.SourceStressIntervals
set_option autoImplicit false
open N11Formalization RatInterval

-- Diagnostic evaluation only; no norm/sign/source theorem follows from #eval.
#eval (List.finRange 5).map (fun j =>
  let I := SourceRefinedBoundaryIntervals.fine
    (SourceRefinedBoundaryIntervals.numeratorBox j)
  (j.val,I.lo,I.hi))

#eval (List.finRange 5).map (fun k =>
  let I := SourceRefinedBoundaryIntervals.fine
    (mul (sinTotLag (ndAngleBox ndBox ⟨k.val,by omega⟩))
      (ndRhoBox ndBox ⟨k.val,by omega⟩))
  (k.val,I.lo,I.hi))
