import N11Formalization.SevenClassQ0Deg3StrictTotal

/-! Lane A: the first seven-class exclusion, conditional only on the exact
canonical-table arithmetic already constructed by `StrictTotal`.

This module adds no analytic or arithmetic premise: it is the thin consumer
`q0_degree3_of_areaInput`.  Its kernel status is exactly the status of
`SevenClassQ0Deg3StrictTotal.q0Degree3AreaInput`; it is not proof credit until
CI builds that dependency and this module. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3Q0Exclusion

open N11Formalization.ActualMetricClassReduction
open N11Formalization.SevenClassQ0Deg3

/-- The q0 degree-three run exclusion. -/
theorem q0_degree3 : Q0RunExclusion 1 :=
  q0_degree3_of_areaInput SevenClassQ0Deg3StrictTotal.q0Degree3AreaInput

end N11Formalization.SevenClassQ0Deg3Q0Exclusion
#check @N11Formalization.SevenClassQ0Deg3Q0Exclusion.q0_degree3
#print axioms N11Formalization.SevenClassQ0Deg3Q0Exclusion.q0_degree3
