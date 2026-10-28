import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 3072..3135; scale-independent integer Valid. -/
theorem window048 : ∀ k : Fin 64,
    Valid data (⟨3072 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3136..3199; scale-independent integer Valid. -/
theorem window049 : ∀ k : Fin 64,
    Valid data (⟨3136 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3200..3263; scale-independent integer Valid. -/
theorem window050 : ∀ k : Fin 64,
    Valid data (⟨3200 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3264..3327; scale-independent integer Valid. -/
theorem window051 : ∀ k : Fin 64,
    Valid data (⟨3264 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3328..3391; scale-independent integer Valid. -/
theorem window052 : ∀ k : Fin 64,
    Valid data (⟨3328 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3392..3455; scale-independent integer Valid. -/
theorem window053 : ∀ k : Fin 64,
    Valid data (⟨3392 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3456..3519; scale-independent integer Valid. -/
theorem window054 : ∀ k : Fin 64,
    Valid data (⟨3456 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3520..3583; scale-independent integer Valid. -/
theorem window055 : ∀ k : Fin 64,
    Valid data (⟨3520 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window048
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window048
#check @N11Formalization.DBMSourceTree.ValidWindows.window049
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window049
#check @N11Formalization.DBMSourceTree.ValidWindows.window050
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window050
#check @N11Formalization.DBMSourceTree.ValidWindows.window051
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window051
#check @N11Formalization.DBMSourceTree.ValidWindows.window052
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window052
#check @N11Formalization.DBMSourceTree.ValidWindows.window053
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window053
#check @N11Formalization.DBMSourceTree.ValidWindows.window054
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window054
#check @N11Formalization.DBMSourceTree.ValidWindows.window055
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window055
