import N11Formalization.FrozenCapRowCap2368

/-! Thin lane-B alias for the CI-green frozen node 2368 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap2368
open N11Formalization.FrozenCapRowCap2368
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, y_2368 q * rowA i j q) ≤ db i j :=
  N11Formalization.FrozenCapRowCap2368.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap2368
#check @N11Formalization.LaneBFrozenCapRowCap2368.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap2368.row_cap
