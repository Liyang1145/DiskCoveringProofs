import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapRowCap1409
import N11Formalization.FrozenCapRowCap2337
import N11Formalization.FrozenCapRowCap2341
import N11Formalization.FrozenCapRowCap2356
import N11Formalization.FrozenCapRowCap2360
import N11Formalization.FrozenCapRowCap2368
import N11Formalization.FrozenCapRowCap2370

/-! Kernel bridges from the seven copied row-cap matrices to the frozen source tree. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapRowCapTreeBridges

theorem db_eq_tree_1409 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (1409 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap1409.db i j := by
  decide +kernel

theorem db_eq_tree_2337 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2337 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2337.db i j := by
  decide +kernel

theorem db_eq_tree_2341 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2341 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2341.db i j := by
  decide +kernel

theorem db_eq_tree_2356 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2356 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2356.db i j := by
  decide +kernel

theorem db_eq_tree_2360 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2360 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2360.db i j := by
  decide +kernel

theorem db_eq_tree_2368 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2368 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2368.db i j := by
  decide +kernel

theorem db_eq_tree_2370 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2370 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapRowCap2370.db i j := by
  decide +kernel

end
end N11Formalization.FrozenCapRowCapTreeBridges

#check @N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_1409
#print axioms N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_1409
#check @N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2370
#print axioms N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2370
