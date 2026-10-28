import N11Formalization.DBMSourceTreeData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-! Fixed source node validity, not energy semantics. Each declaration is a separate
kernel reduction (maximum 64 ids); total domain requires all ten modules. -/
namespace N11Formalization.DBMSourceTree.ValidWindows
open DBMTreeKernel

/-- ids 2560..2623; scale-independent integer Valid. -/
theorem window040 : ∀ k : Fin 64,
    Valid data (⟨2560 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2624..2687; scale-independent integer Valid. -/
theorem window041 : ∀ k : Fin 64,
    Valid data (⟨2624 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2688..2751; scale-independent integer Valid. -/
theorem window042 : ∀ k : Fin 64,
    Valid data (⟨2688 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2752..2815; scale-independent integer Valid. -/
theorem window043 : ∀ k : Fin 64,
    Valid data (⟨2752 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2816..2879; scale-independent integer Valid. -/
theorem window044 : ∀ k : Fin 64,
    Valid data (⟨2816 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2880..2943; scale-independent integer Valid. -/
theorem window045 : ∀ k : Fin 64,
    Valid data (⟨2880 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 2944..3007; scale-independent integer Valid. -/
theorem window046 : ∀ k : Fin 64,
    Valid data (⟨2944 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

/-- ids 3008..3071; scale-independent integer Valid. -/
theorem window047 : ∀ k : Fin 64,
    Valid data (⟨3008 + k.val, by omega⟩ : Fin 5011) := by
  decide +kernel

end N11Formalization.DBMSourceTree.ValidWindows
#check @N11Formalization.DBMSourceTree.ValidWindows.window040
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window040
#check @N11Formalization.DBMSourceTree.ValidWindows.window041
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window041
#check @N11Formalization.DBMSourceTree.ValidWindows.window042
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window042
#check @N11Formalization.DBMSourceTree.ValidWindows.window043
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window043
#check @N11Formalization.DBMSourceTree.ValidWindows.window044
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window044
#check @N11Formalization.DBMSourceTree.ValidWindows.window045
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window045
#check @N11Formalization.DBMSourceTree.ValidWindows.window046
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window046
#check @N11Formalization.DBMSourceTree.ValidWindows.window047
#print axioms N11Formalization.DBMSourceTree.ValidWindows.window047
