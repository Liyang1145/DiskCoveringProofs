import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 4608..4671; scale-independent integer Valid. -/
theorem window072 : ∀ k : Fin 64,
    Valid data (⟨4608 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4672..4735; scale-independent integer Valid. -/
theorem window073 : ∀ k : Fin 64,
    Valid data (⟨4672 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4736..4799; scale-independent integer Valid. -/
theorem window074 : ∀ k : Fin 64,
    Valid data (⟨4736 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4800..4863; scale-independent integer Valid. -/
theorem window075 : ∀ k : Fin 64,
    Valid data (⟨4800 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4864..4927; scale-independent integer Valid. -/
theorem window076 : ∀ k : Fin 64,
    Valid data (⟨4864 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4928..4991; scale-independent integer Valid. -/
theorem window077 : ∀ k : Fin 64,
    Valid data (⟨4928 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 4992..5010; scale-independent integer Valid. -/
theorem window078 : ∀ k : Fin 19,
    Valid data (⟨4992 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window072
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window072
#check @N11Formalization.DBMSourceTree.ValidWindows.window073
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window073
#check @N11Formalization.DBMSourceTree.ValidWindows.window074
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window074
#check @N11Formalization.DBMSourceTree.ValidWindows.window075
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window075
#check @N11Formalization.DBMSourceTree.ValidWindows.window076
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window076
#check @N11Formalization.DBMSourceTree.ValidWindows.window077
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window077
#check @N11Formalization.DBMSourceTree.ValidWindows.window078
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window078
