import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 1024..1087; scale-independent integer Valid. -/
theorem window016 : ∀ k : Fin 64,
    Valid data (⟨1024 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1088..1151; scale-independent integer Valid. -/
theorem window017 : ∀ k : Fin 64,
    Valid data (⟨1088 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1152..1215; scale-independent integer Valid. -/
theorem window018 : ∀ k : Fin 64,
    Valid data (⟨1152 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1216..1279; scale-independent integer Valid. -/
theorem window019 : ∀ k : Fin 64,
    Valid data (⟨1216 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1280..1343; scale-independent integer Valid. -/
theorem window020 : ∀ k : Fin 64,
    Valid data (⟨1280 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1344..1407; scale-independent integer Valid. -/
theorem window021 : ∀ k : Fin 64,
    Valid data (⟨1344 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1408..1471; scale-independent integer Valid. -/
theorem window022 : ∀ k : Fin 64,
    Valid data (⟨1408 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1472..1535; scale-independent integer Valid. -/
theorem window023 : ∀ k : Fin 64,
    Valid data (⟨1472 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window016
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window016
#check @N11Formalization.DBMSourceTree.ValidWindows.window017
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window017
#check @N11Formalization.DBMSourceTree.ValidWindows.window018
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window018
#check @N11Formalization.DBMSourceTree.ValidWindows.window019
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window019
#check @N11Formalization.DBMSourceTree.ValidWindows.window020
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window020
#check @N11Formalization.DBMSourceTree.ValidWindows.window021
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window021
#check @N11Formalization.DBMSourceTree.ValidWindows.window022
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window022
#check @N11Formalization.DBMSourceTree.ValidWindows.window023
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window023
