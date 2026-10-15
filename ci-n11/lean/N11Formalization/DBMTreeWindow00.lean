import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 0..63; scale-independent integer Valid. -/
theorem window000 : ∀ k : Fin 64,
    Valid data (⟨0 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 64..127; scale-independent integer Valid. -/
theorem window001 : ∀ k : Fin 64,
    Valid data (⟨64 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 128..191; scale-independent integer Valid. -/
theorem window002 : ∀ k : Fin 64,
    Valid data (⟨128 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 192..255; scale-independent integer Valid. -/
theorem window003 : ∀ k : Fin 64,
    Valid data (⟨192 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 256..319; scale-independent integer Valid. -/
theorem window004 : ∀ k : Fin 64,
    Valid data (⟨256 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 320..383; scale-independent integer Valid. -/
theorem window005 : ∀ k : Fin 64,
    Valid data (⟨320 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 384..447; scale-independent integer Valid. -/
theorem window006 : ∀ k : Fin 64,
    Valid data (⟨384 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 448..511; scale-independent integer Valid. -/
theorem window007 : ∀ k : Fin 64,
    Valid data (⟨448 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window000
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window000
#check @N11Formalization.DBMSourceTree.ValidWindows.window001
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window001
#check @N11Formalization.DBMSourceTree.ValidWindows.window002
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window002
#check @N11Formalization.DBMSourceTree.ValidWindows.window003
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window003
#check @N11Formalization.DBMSourceTree.ValidWindows.window004
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window004
#check @N11Formalization.DBMSourceTree.ValidWindows.window005
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window005
#check @N11Formalization.DBMSourceTree.ValidWindows.window006
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window006
#check @N11Formalization.DBMSourceTree.ValidWindows.window007
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window007
