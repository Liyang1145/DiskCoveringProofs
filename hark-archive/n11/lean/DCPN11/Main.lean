/-
DCPN11/Main.lean  —  the n = 11 theorem  r_D(11) = R*  (C924).

STATUS: NOT YET COMPILED (see STATUS.md). The assembly below is a complete draft; it
inherits every `sorry` of `UpperBound.lean`, `LowerBound.lean` and `Candidate.lean`.
`#print axioms DCP.N11.rD_eleven` must list `sorryAx` until those are discharged.
-/
import DCPN11.UpperBound
import DCPN11.LowerBound

namespace DCP.N11

/-- **Theorem (C924).** `r_D(11) = R*`, where `R*` is the R-coordinate of the unique root of
the 12-equation contact/KKT system in the exact C891 dyadic box. -/
theorem rD_eleven : rD 11 = Rstar := by
  obtain ⟨c, hc⟩ := upper_bound
  exact rD_eq_of_bounds (by norm_num) c hc lower_bound

end DCP.N11

#print axioms DCP.N11.rD_eleven
