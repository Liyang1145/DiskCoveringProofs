import N11Formalization.FrozenCapRowCap2360

/-! Thin lane-B alias for the CI-green frozen node 2360 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap2360
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_2360 q *
      N11Formalization.FrozenCapRowCap2360.rowA i j q) ≤
      N11Formalization.FrozenCapRowCap2360.db i j :=
  N11Formalization.FrozenCapRowCap2360.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap2360
#check @N11Formalization.LaneBFrozenCapRowCap2360.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap2360.row_cap
