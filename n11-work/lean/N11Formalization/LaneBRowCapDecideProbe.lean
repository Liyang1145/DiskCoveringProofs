import N11Formalization.FrozenCapRowCap1409

/-! Representative lane-B aliases for the frozen node 1409 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBRowCapDecideProbe
noncomputable section

theorem row_0_1 :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_1409 q *
      N11Formalization.FrozenCapRowCap1409.rowA 0 1 q) ≤
      N11Formalization.FrozenCapRowCap1409.db 0 1 :=
  N11Formalization.FrozenCapRowCap1409.row_cap 0 1

theorem row_4_5 :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_1409 q *
      N11Formalization.FrozenCapRowCap1409.rowA 4 5 q) ≤
      N11Formalization.FrozenCapRowCap1409.db 4 5 :=
  N11Formalization.FrozenCapRowCap1409.row_cap 4 5

theorem row_9_9 :
    (∑ q : Fin 9, N11Formalization.FrozenCapRationalCore.y_1409 q *
      N11Formalization.FrozenCapRowCap1409.rowA 9 9 q) ≤
      N11Formalization.FrozenCapRowCap1409.db 9 9 :=
  N11Formalization.FrozenCapRowCap1409.row_cap 9 9

end
end N11Formalization.LaneBRowCapDecideProbe
#print axioms N11Formalization.LaneBRowCapDecideProbe.row_4_5
