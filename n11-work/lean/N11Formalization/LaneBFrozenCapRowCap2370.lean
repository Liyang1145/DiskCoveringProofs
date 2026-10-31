import N11Formalization.FrozenCapRowCap2370

/-! Thin lane-B alias for the CI-green frozen node 2370 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap2370
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_2370 q *
      N11Formalization.FrozenCapRowCap2370.rowA i j q) ≤
      N11Formalization.FrozenCapRowCap2370.db i j :=
  N11Formalization.FrozenCapRowCap2370.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap2370
#check @N11Formalization.LaneBFrozenCapRowCap2370.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap2370.row_cap
