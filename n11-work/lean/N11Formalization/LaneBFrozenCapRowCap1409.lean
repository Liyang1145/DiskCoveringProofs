import N11Formalization.FrozenCapRowCap1409

/-! Thin lane-B alias for the CI-green frozen node 1409 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap1409
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_1409 q *
      N11Formalization.FrozenCapRowCap1409.rowA i j q) ≤
      N11Formalization.FrozenCapRowCap1409.db i j :=
  N11Formalization.FrozenCapRowCap1409.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap1409
#check @N11Formalization.LaneBFrozenCapRowCap1409.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap1409.row_cap
