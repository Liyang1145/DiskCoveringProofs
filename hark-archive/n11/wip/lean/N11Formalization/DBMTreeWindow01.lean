import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 512..575; scale-independent integer Valid. -/
theorem window008 : ∀ k : Fin 64,
    Valid data (⟨512 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 576..639; scale-independent integer Valid. -/
theorem window009 : ∀ k : Fin 64,
    Valid data (⟨576 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 640..703; scale-independent integer Valid. -/
theorem window010 : ∀ k : Fin 64,
    Valid data (⟨640 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 704..767; scale-independent integer Valid. -/
theorem window011 : ∀ k : Fin 64,
    Valid data (⟨704 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 768..831; scale-independent integer Valid. -/
theorem window012 : ∀ k : Fin 64,
    Valid data (⟨768 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 832..895; scale-independent integer Valid. -/
theorem window013 : ∀ k : Fin 64,
    Valid data (⟨832 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 896..959; scale-independent integer Valid. -/
theorem window014 : ∀ k : Fin 64,
    Valid data (⟨896 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 960..1023; scale-independent integer Valid. -/
theorem window015 : ∀ k : Fin 64,
    Valid data (⟨960 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window008
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window008
#check @N11Formalization.DBMSourceTree.ValidWindows.window009
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window009
#check @N11Formalization.DBMSourceTree.ValidWindows.window010
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window010
#check @N11Formalization.DBMSourceTree.ValidWindows.window011
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window011
#check @N11Formalization.DBMSourceTree.ValidWindows.window012
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window012
#check @N11Formalization.DBMSourceTree.ValidWindows.window013
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window013
#check @N11Formalization.DBMSourceTree.ValidWindows.window014
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window014
#check @N11Formalization.DBMSourceTree.ValidWindows.window015
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window015
