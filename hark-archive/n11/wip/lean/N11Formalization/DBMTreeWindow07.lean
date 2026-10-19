import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 3584..3647; scale-independent integer Valid. -/
theorem window056 : ∀ k : Fin 64,
    Valid data (⟨3584 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3648..3711; scale-independent integer Valid. -/
theorem window057 : ∀ k : Fin 64,
    Valid data (⟨3648 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3712..3775; scale-independent integer Valid. -/
theorem window058 : ∀ k : Fin 64,
    Valid data (⟨3712 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3776..3839; scale-independent integer Valid. -/
theorem window059 : ∀ k : Fin 64,
    Valid data (⟨3776 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3840..3903; scale-independent integer Valid. -/
theorem window060 : ∀ k : Fin 64,
    Valid data (⟨3840 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3904..3967; scale-independent integer Valid. -/
theorem window061 : ∀ k : Fin 64,
    Valid data (⟨3904 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3968..4031; scale-independent integer Valid. -/
theorem window062 : ∀ k : Fin 64,
    Valid data (⟨3968 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4032..4095; scale-independent integer Valid. -/
theorem window063 : ∀ k : Fin 64,
    Valid data (⟨4032 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window056
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window056
#check @N11Formalization.DBMSourceTree.ValidWindows.window057
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window057
#check @N11Formalization.DBMSourceTree.ValidWindows.window058
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window058
#check @N11Formalization.DBMSourceTree.ValidWindows.window059
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window059
#check @N11Formalization.DBMSourceTree.ValidWindows.window060
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window060
#check @N11Formalization.DBMSourceTree.ValidWindows.window061
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window061
#check @N11Formalization.DBMSourceTree.ValidWindows.window062
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window062
#check @N11Formalization.DBMSourceTree.ValidWindows.window063
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window063
