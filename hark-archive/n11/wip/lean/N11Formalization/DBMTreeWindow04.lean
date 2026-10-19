import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 2048..2111; scale-independent integer Valid. -/
theorem window032 : ∀ k : Fin 64,
    Valid data (⟨2048 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2112..2175; scale-independent integer Valid. -/
theorem window033 : ∀ k : Fin 64,
    Valid data (⟨2112 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2176..2239; scale-independent integer Valid. -/
theorem window034 : ∀ k : Fin 64,
    Valid data (⟨2176 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2240..2303; scale-independent integer Valid. -/
theorem window035 : ∀ k : Fin 64,
    Valid data (⟨2240 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2304..2367; scale-independent integer Valid. -/
theorem window036 : ∀ k : Fin 64,
    Valid data (⟨2304 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2368..2431; scale-independent integer Valid. -/
theorem window037 : ∀ k : Fin 64,
    Valid data (⟨2368 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2432..2495; scale-independent integer Valid. -/
theorem window038 : ∀ k : Fin 64,
    Valid data (⟨2432 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2496..2559; scale-independent integer Valid. -/
theorem window039 : ∀ k : Fin 64,
    Valid data (⟨2496 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window032
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window032
#check @N11Formalization.DBMSourceTree.ValidWindows.window033
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window033
#check @N11Formalization.DBMSourceTree.ValidWindows.window034
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window034
#check @N11Formalization.DBMSourceTree.ValidWindows.window035
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window035
#check @N11Formalization.DBMSourceTree.ValidWindows.window036
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window036
#check @N11Formalization.DBMSourceTree.ValidWindows.window037
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window037
#check @N11Formalization.DBMSourceTree.ValidWindows.window038
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window038
#check @N11Formalization.DBMSourceTree.ValidWindows.window039
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window039
