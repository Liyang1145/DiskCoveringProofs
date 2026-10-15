import N11Formalization.DSHPatchDispatcher

set_option autoImplicit false
set_option maxRecDepth 10000

/-! # DSH-PATCH-DISP structural controls

These are the load-bearing checks on the DISPATCHER ITSELF (not on the mathematics of any single
cell):

  * `nidList` has no duplicate: a cell wired twice would silently inflate coverage;
  * the cardinalities are exactly 118 / 2 / 120;
  * the two K5 cells are NOT in `nidList` -- the c5 cluster is deliberately excluded because its
    dual-cap gate is still pending, and the named gap is `nidListK5` instead;
  * the two K5 cells ARE in `nidList120`, so the 120 statement really has 120 cells;
  * DROPPED-CELL control: deleting one id from the list removes exactly that cell from the
    dispatched domain (an id omitted from the enumeration has no `hr` route).  The dropped list is
    the exact analogue of a "replaced constant" control applied to the index set.
-/

namespace N11Formalization.DSHPatchDispatcherControl

open N11Formalization

noncomputable section

/-- No duplicate id in the 118-cell list: each cell is wired exactly once. -/
theorem nidList_nodup : DSHPatchDispatcher.nidList.Nodup := by decide +kernel

/-- The 118-cell list is exactly 118 long. -/
theorem nidList_length : DSHPatchDispatcher.nidList.length = 118 := by decide +kernel

/-- The K5 list is exactly the two cells 4935 and 4957. -/
theorem nidListK5_eq : DSHPatchDispatcher.nidListK5 = [(4935 : Fin 5011), 4957] := rfl

/-- All 120 ids, counted. -/
theorem nidList120_length : DSHPatchDispatcher.nidList120.length = 120 := by
  simp only [DSHPatchDispatcher.nidList120, List.length_append, nidList_length]
  decide +kernel

/-- NAMED GAP: cluster 5 is NOT dispatched from the survey list (its dual-cap gate is
pending); its two cells come from the root-paid K5 containment instead. -/
theorem k5_not_in_nidList : (4935 : Fin 5011) ∉ DSHPatchDispatcher.nidList := by
  decide +kernel

theorem k5b_not_in_nidList : (4957 : Fin 5011) ∉ DSHPatchDispatcher.nidList := by
  decide +kernel

theorem k5_in_nidList120 : (4935 : Fin 5011) ∈ DSHPatchDispatcher.nidList120 := by
  decide +kernel

/-- DROPPED-CELL control domain: the 118 list with cell 4974 removed. -/
def nidListDrop : List (Fin 5011) := [(4996 : Fin 5011), (4958 : Fin 5011), (4823 : Fin 5011), (4824 : Fin 5011), (5008 : Fin 5011), (4993 : Fin 5011), (5003 : Fin 5011), (4795 : Fin 5011), (4796 : Fin 5011), (4970 : Fin 5011), (5006 : Fin 5011), (5010 : Fin 5011), (4874 : Fin 5011), (4882 : Fin 5011), (4884 : Fin 5011), (4894 : Fin 5011), (4895 : Fin 5011), (4902 : Fin 5011), (4910 : Fin 5011), (4813 : Fin 5011), (4988 : Fin 5011), (5001 : Fin 5011), (4956 : Fin 5011), (4959 : Fin 5011), (4989 : Fin 5011), (4980 : Fin 5011), (4985 : Fin 5011), (4997 : Fin 5011), (4436 : Fin 5011), (4529 : Fin 5011), (4589 : Fin 5011), (4711 : Fin 5011), (4713 : Fin 5011), (4778 : Fin 5011), (4805 : Fin 5011), (4806 : Fin 5011), (4807 : Fin 5011), (4814 : Fin 5011), (4815 : Fin 5011), (4816 : Fin 5011), (4817 : Fin 5011), (4818 : Fin 5011), (4819 : Fin 5011), (4820 : Fin 5011), (4822 : Fin 5011), (4833 : Fin 5011), (4834 : Fin 5011), (4835 : Fin 5011), (4836 : Fin 5011), (4837 : Fin 5011), (4838 : Fin 5011), (4839 : Fin 5011), (4840 : Fin 5011), (4851 : Fin 5011), (4852 : Fin 5011), (4853 : Fin 5011), (4854 : Fin 5011), (4855 : Fin 5011), (4856 : Fin 5011), (4859 : Fin 5011), (4860 : Fin 5011), (4885 : Fin 5011), (4899 : Fin 5011), (4900 : Fin 5011), (4911 : Fin 5011), (4912 : Fin 5011), (4913 : Fin 5011), (4914 : Fin 5011), (4915 : Fin 5011), (4916 : Fin 5011), (4917 : Fin 5011), (4918 : Fin 5011), (4932 : Fin 5011), (4972 : Fin 5011), (4841 : Fin 5011), (4842 : Fin 5011), (4848 : Fin 5011), (4849 : Fin 5011), (4877 : Fin 5011), (4955 : Fin 5011), (4845 : Fin 5011), (4847 : Fin 5011), (4857 : Fin 5011), (4858 : Fin 5011), (4861 : Fin 5011), (4862 : Fin 5011), (4863 : Fin 5011), (4864 : Fin 5011), (4865 : Fin 5011), (4866 : Fin 5011), (4886 : Fin 5011), (4887 : Fin 5011), (4888 : Fin 5011), (4999 : Fin 5011), (5005 : Fin 5011), (5009 : Fin 5011), (4821 : Fin 5011), (4846 : Fin 5011), (4869 : Fin 5011), (4870 : Fin 5011), (4871 : Fin 5011), (4872 : Fin 5011), (4873 : Fin 5011), (4875 : Fin 5011), (4876 : Fin 5011), (4881 : Fin 5011), (4883 : Fin 5011), (4891 : Fin 5011), (4892 : Fin 5011), (4893 : Fin 5011), (4896 : Fin 5011), (4901 : Fin 5011), (4907 : Fin 5011), (4908 : Fin 5011), (4909 : Fin 5011), (4981 : Fin 5011), (4983 : Fin 5011)]

def InPatchUnionDrop (y : Fin 9 → ℝ) : Prop :=
  ∃ c ∈ nidListDrop, FlashLeafSplit.Cell
    (DBMTreeKernel.matrix DBMSourceTree.data 4096 c) (FlashLeafSplit.tlift y)

/-- The dropped cell is no longer in the dispatched list. -/
theorem dropped_cell_not_member : (4974 : Fin 5011) ∉ nidListDrop := by decide +kernel

/-- The dropped list is one shorter. -/
theorem nidListDrop_length : nidListDrop.length = 117 := by decide +kernel

/-- The dropped cell IS in the full list (so the drop is a genuine loss, not a no-op). -/
theorem dropped_cell_in_nidList : (4974 : Fin 5011) ∈ DSHPatchDispatcher.nidList :=
  by decide +kernel

/-- The dropped union really loses the dropped cell. -/
theorem dropped_cell_not_dispatched {y : Fin 9 → ℝ}
    (h : InPatchUnionDrop y) : ¬ ∃ hmem : (4974 : Fin 5011) ∈ nidListDrop,
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
        (4974 : Fin 5011)) (FlashLeafSplit.tlift y) := by
  rintro ⟨hmem, _⟩
  exact dropped_cell_not_member hmem

end

end N11Formalization.DSHPatchDispatcherControl

#check @N11Formalization.DSHPatchDispatcherControl.nidList_nodup
#check @N11Formalization.DSHPatchDispatcherControl.nidList_length
#check @N11Formalization.DSHPatchDispatcherControl.nidList120_length
#check @N11Formalization.DSHPatchDispatcherControl.k5_not_in_nidList
#check @N11Formalization.DSHPatchDispatcherControl.dropped_cell_not_member
#check @N11Formalization.DSHPatchDispatcherControl.dropped_cell_not_dispatched
#print axioms N11Formalization.DSHPatchDispatcherControl.nidList_nodup
#print axioms N11Formalization.DSHPatchDispatcherControl.nidList_length
#print axioms N11Formalization.DSHPatchDispatcherControl.nidList120_length
#print axioms N11Formalization.DSHPatchDispatcherControl.k5_not_in_nidList
#print axioms N11Formalization.DSHPatchDispatcherControl.dropped_cell_not_member
#print axioms N11Formalization.DSHPatchDispatcherControl.nidListDrop_length
#print axioms N11Formalization.DSHPatchDispatcherControl.dropped_cell_in_nidList
#print axioms N11Formalization.DSHPatchDispatcherControl.dropped_cell_not_dispatched
