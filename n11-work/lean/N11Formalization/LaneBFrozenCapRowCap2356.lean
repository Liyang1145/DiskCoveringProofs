import N11Formalization.FrozenCapRowCap2356

/-! Thin lane-B alias for the CI-green frozen node 2356 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap2356
open N11Formalization.FrozenCapRowCap2356
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, y_2356 q * rowA i j q) ≤ db i j :=
  N11Formalization.FrozenCapRowCap2356.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap2356
#check @N11Formalization.LaneBFrozenCapRowCap2356.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap2356.row_cap
