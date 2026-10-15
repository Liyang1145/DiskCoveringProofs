import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 1536..1599; scale-independent integer Valid. -/
theorem window024 : ∀ k : Fin 64,
    Valid data (⟨1536 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1600..1663; scale-independent integer Valid. -/
theorem window025 : ∀ k : Fin 64,
    Valid data (⟨1600 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1664..1727; scale-independent integer Valid. -/
theorem window026 : ∀ k : Fin 64,
    Valid data (⟨1664 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1728..1791; scale-independent integer Valid. -/
theorem window027 : ∀ k : Fin 64,
    Valid data (⟨1728 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1792..1855; scale-independent integer Valid. -/
theorem window028 : ∀ k : Fin 64,
    Valid data (⟨1792 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1856..1919; scale-independent integer Valid. -/
theorem window029 : ∀ k : Fin 64,
    Valid data (⟨1856 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1920..1983; scale-independent integer Valid. -/
theorem window030 : ∀ k : Fin 64,
    Valid data (⟨1920 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 1984..2047; scale-independent integer Valid. -/
theorem window031 : ∀ k : Fin 64,
    Valid data (⟨1984 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window024
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window024
#check @N11Formalization.DBMSourceTree.ValidWindows.window025
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window025
#check @N11Formalization.DBMSourceTree.ValidWindows.window026
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window026
#check @N11Formalization.DBMSourceTree.ValidWindows.window027
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window027
#check @N11Formalization.DBMSourceTree.ValidWindows.window028
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window028
#check @N11Formalization.DBMSourceTree.ValidWindows.window029
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window029
#check @N11Formalization.DBMSourceTree.ValidWindows.window030
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window030
#check @N11Formalization.DBMSourceTree.ValidWindows.window031
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window031
