import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 4096..4159; scale-independent integer Valid. -/
theorem window064 : ∀ k : Fin 64,
    Valid data (⟨4096 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4160..4223; scale-independent integer Valid. -/
theorem window065 : ∀ k : Fin 64,
    Valid data (⟨4160 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4224..4287; scale-independent integer Valid. -/
theorem window066 : ∀ k : Fin 64,
    Valid data (⟨4224 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4288..4351; scale-independent integer Valid. -/
theorem window067 : ∀ k : Fin 64,
    Valid data (⟨4288 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4352..4415; scale-independent integer Valid. -/
theorem window068 : ∀ k : Fin 64,
    Valid data (⟨4352 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4416..4479; scale-independent integer Valid. -/
theorem window069 : ∀ k : Fin 64,
    Valid data (⟨4416 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4480..4543; scale-independent integer Valid. -/
theorem window070 : ∀ k : Fin 64,
    Valid data (⟨4480 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4544..4607; scale-independent integer Valid. -/
theorem window071 : ∀ k : Fin 64,
    Valid data (⟨4544 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window064
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window064
#check @N11Formalization.DBMSourceTree.ValidWindows.window065
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window065
#check @N11Formalization.DBMSourceTree.ValidWindows.window066
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window066
#check @N11Formalization.DBMSourceTree.ValidWindows.window067
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window067
#check @N11Formalization.DBMSourceTree.ValidWindows.window068
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window068
#check @N11Formalization.DBMSourceTree.ValidWindows.window069
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window069
#check @N11Formalization.DBMSourceTree.ValidWindows.window070
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window070
#check @N11Formalization.DBMSourceTree.ValidWindows.window071
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window071
