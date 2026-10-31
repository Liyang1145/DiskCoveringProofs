import N11Formalization.FrozenCapRowCap2337

/-! Thin lane-B alias for the CI-green frozen node 2337 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap2337
open N11Formalization.FrozenCapRowCap2337
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, y_2337 q * rowA i j q) ≤ db i j :=
  N11Formalization.FrozenCapRowCap2337.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap2337
#check @N11Formalization.LaneBFrozenCapRowCap2337.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap2337.row_cap
