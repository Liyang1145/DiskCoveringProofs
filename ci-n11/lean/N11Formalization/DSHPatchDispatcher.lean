import N11Formalization.DSHPatchBridge
import N11Formalization.DSHPatchSurveyC0
import N11Formalization.DSHPatchSurveyC1
import N11Formalization.DSHPatchSurveyC2
import N11Formalization.DSHPatchSurveyC3
import N11Formalization.DSHPatchSurveyC4
import N11Formalization.DSHPatchSurveyC6
import N11Formalization.DSHPatchSurveyC7
import N11Formalization.DSHPatchSurveyC8
import N11Formalization.DSHPatchSurveyC9
import N11Formalization.DSHPatchSurveyC10
import N11Formalization.DSHPatchSurveyC11
import N11Formalization.DSHPatchSurveyC12
import N11Formalization.DSHPatchSurveyC13
import N11Formalization.DSHPatchSurveyC14
import N11Formalization.DSHPatchSurveyC15
import N11Formalization.DSHPatchTemplateK5
set_option autoImplicit false
set_option maxRecDepth 10000

namespace N11Formalization.DSHPatchDispatcher

open Finset
open N11Formalization

noncomputable section

/-! ## Cell id lists (parsed from the cluster sources, never hand-typed)

`nidList` is the 118 non-K5 cells; `nidListK5` is cluster k=5 (cells 4935/4957), whose
containment is ROOT-PAID (`Patch120K5Actual`, C1719, root-imported 2026-09-30) and therefore does
NOT depend on patch-survey's still-pending c5 dual-cap gate.

The two lists together are all 120 patch cells; `nidList120` is their concatenation.
-/

/-- Cluster 0: 2 cells. -/
def nidListC0 : List (Fin 5011) := [(4974 : Fin 5011), (4996 : Fin 5011)]

/-- Cluster 1: 1 cells. -/
def nidListC1 : List (Fin 5011) := [(4958 : Fin 5011)]

/-- Cluster 2: 2 cells. -/
def nidListC2 : List (Fin 5011) := [(4823 : Fin 5011), (4824 : Fin 5011)]

/-- Cluster 3: 1 cells. -/
def nidListC3 : List (Fin 5011) := [(5008 : Fin 5011)]

/-- Cluster 4: 2 cells. -/
def nidListC4 : List (Fin 5011) := [(4993 : Fin 5011), (5003 : Fin 5011)]

/-- Cluster 6: 2 cells. -/
def nidListC6 : List (Fin 5011) := [(4795 : Fin 5011), (4796 : Fin 5011)]

/-- Cluster 7: 3 cells. -/
def nidListC7 : List (Fin 5011) := [(4970 : Fin 5011), (5006 : Fin 5011), (5010 : Fin 5011)]

/-- Cluster 8: 7 cells. -/
def nidListC8 : List (Fin 5011) := [(4874 : Fin 5011), (4882 : Fin 5011), (4884 : Fin 5011), (4894 : Fin 5011), (4895 : Fin 5011), (4902 : Fin 5011), (4910 : Fin 5011)]

/-- Cluster 9: 3 cells. -/
def nidListC9 : List (Fin 5011) := [(4813 : Fin 5011), (4988 : Fin 5011), (5001 : Fin 5011)]

/-- Cluster 10: 3 cells. -/
def nidListC10 : List (Fin 5011) := [(4956 : Fin 5011), (4959 : Fin 5011), (4989 : Fin 5011)]

/-- Cluster 11: 3 cells. -/
def nidListC11 : List (Fin 5011) := [(4980 : Fin 5011), (4985 : Fin 5011), (4997 : Fin 5011)]

/-- Cluster 12: 46 cells. -/
def nidListC12 : List (Fin 5011) := [(4436 : Fin 5011), (4529 : Fin 5011), (4589 : Fin 5011), (4711 : Fin 5011), (4713 : Fin 5011), (4778 : Fin 5011), (4805 : Fin 5011), (4806 : Fin 5011), (4807 : Fin 5011), (4814 : Fin 5011), (4815 : Fin 5011), (4816 : Fin 5011), (4817 : Fin 5011), (4818 : Fin 5011), (4819 : Fin 5011), (4820 : Fin 5011), (4822 : Fin 5011), (4833 : Fin 5011), (4834 : Fin 5011), (4835 : Fin 5011), (4836 : Fin 5011), (4837 : Fin 5011), (4838 : Fin 5011), (4839 : Fin 5011), (4840 : Fin 5011), (4851 : Fin 5011), (4852 : Fin 5011), (4853 : Fin 5011), (4854 : Fin 5011), (4855 : Fin 5011), (4856 : Fin 5011), (4859 : Fin 5011), (4860 : Fin 5011), (4885 : Fin 5011), (4899 : Fin 5011), (4900 : Fin 5011), (4911 : Fin 5011), (4912 : Fin 5011), (4913 : Fin 5011), (4914 : Fin 5011), (4915 : Fin 5011), (4916 : Fin 5011), (4917 : Fin 5011), (4918 : Fin 5011), (4932 : Fin 5011), (4972 : Fin 5011)]

/-- Cluster 13: 6 cells. -/
def nidListC13 : List (Fin 5011) := [(4841 : Fin 5011), (4842 : Fin 5011), (4848 : Fin 5011), (4849 : Fin 5011), (4877 : Fin 5011), (4955 : Fin 5011)]

/-- Cluster 14: 16 cells. -/
def nidListC14 : List (Fin 5011) := [(4845 : Fin 5011), (4847 : Fin 5011), (4857 : Fin 5011), (4858 : Fin 5011), (4861 : Fin 5011), (4862 : Fin 5011), (4863 : Fin 5011), (4864 : Fin 5011), (4865 : Fin 5011), (4866 : Fin 5011), (4886 : Fin 5011), (4887 : Fin 5011), (4888 : Fin 5011), (4999 : Fin 5011), (5005 : Fin 5011), (5009 : Fin 5011)]

/-- Cluster 15: 21 cells. -/
def nidListC15 : List (Fin 5011) := [(4821 : Fin 5011), (4846 : Fin 5011), (4869 : Fin 5011), (4870 : Fin 5011), (4871 : Fin 5011), (4872 : Fin 5011), (4873 : Fin 5011), (4875 : Fin 5011), (4876 : Fin 5011), (4881 : Fin 5011), (4883 : Fin 5011), (4891 : Fin 5011), (4892 : Fin 5011), (4893 : Fin 5011), (4896 : Fin 5011), (4901 : Fin 5011), (4907 : Fin 5011), (4908 : Fin 5011), (4909 : Fin 5011), (4981 : Fin 5011), (4983 : Fin 5011)]

/-- Cluster k=5 (root-paid containment; NOT from the pending c5 gate). -/
def nidListK5 : List (Fin 5011) := [(4935 : Fin 5011), (4957 : Fin 5011)]

/-- The 118 non-K5 cell ids. -/
def nidList : List (Fin 5011) := nidListC0 ++ nidListC1 ++ nidListC2 ++ nidListC3 ++ nidListC4 ++ nidListC6 ++ nidListC7 ++ nidListC8 ++ nidListC9 ++ nidListC10 ++ nidListC11 ++ nidListC12 ++ nidListC13 ++ nidListC14 ++ nidListC15

/-- All 120 patch cell ids (118 non-K5 ++ the two root-paid K5 cells). -/
def nidList120 : List (Fin 5011) := nidList ++ nidListK5

/-- The patch-union domain used by the dispatcher: `y` lies in one of the listed cells. -/
def InPatchUnion (y : Fin 9 → ℝ) : Prop :=
  ∃ c ∈ nidList, FlashLeafSplit.Cell
    (DBMTreeKernel.matrix DBMSourceTree.data 4096 c) (FlashLeafSplit.tlift y)

/-- The same over all 120 cells. -/
def InPatchUnion120 (y : Fin 9 → ℝ) : Prop :=
  ∃ c ∈ nidList120, FlashLeafSplit.Cell
    (DBMTreeKernel.matrix DBMSourceTree.data 4096 c) (FlashLeafSplit.tlift y)

/-! ## Per-cell `hr` lemmas: the bridge instantiated on each cluster's containment

Each line is `leaf_hr_of_q2` applied to that cell's kernel-checked L2 containment.
One named theorem per cell, so downstream code names a cell, not a tactic.
-/

theorem disp_hr_4974 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4974 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C0.q2_le_4974 hu hc)

theorem disp_hr_4996 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4996 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C0.q2_le_4996 hu hc)

theorem disp_hr_4958 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4958 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C1.q2_le_4958 hu hc)

theorem disp_hr_4823 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4823 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C2.q2_le_4823 hu hc)

theorem disp_hr_4824 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4824 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C2.q2_le_4824 hu hc)

theorem disp_hr_5008 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5008 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C3.q2_le_5008 hu hc)

theorem disp_hr_4993 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4993 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C4.q2_le_4993 hu hc)

theorem disp_hr_5003 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5003 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C4.q2_le_5003 hu hc)

theorem disp_hr_4795 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4795 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C6.q2_le_4795 hu hc)

theorem disp_hr_4796 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4796 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C6.q2_le_4796 hu hc)

theorem disp_hr_4970 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4970 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C7.q2_le_4970 hu hc)

theorem disp_hr_5006 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5006 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C7.q2_le_5006 hu hc)

theorem disp_hr_5010 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5010 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C7.q2_le_5010 hu hc)

theorem disp_hr_4874 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4874 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4874 hu hc)

theorem disp_hr_4882 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4882 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4882 hu hc)

theorem disp_hr_4884 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4884 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4884 hu hc)

theorem disp_hr_4894 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4894 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4894 hu hc)

theorem disp_hr_4895 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4895 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4895 hu hc)

theorem disp_hr_4902 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4902 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4902 hu hc)

theorem disp_hr_4910 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4910 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C8.q2_le_4910 hu hc)

theorem disp_hr_4813 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4813 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C9.q2_le_4813 hu hc)

theorem disp_hr_4988 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4988 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C9.q2_le_4988 hu hc)

theorem disp_hr_5001 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5001 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C9.q2_le_5001 hu hc)

theorem disp_hr_4956 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4956 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C10.q2_le_4956 hu hc)

theorem disp_hr_4959 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4959 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C10.q2_le_4959 hu hc)

theorem disp_hr_4989 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4989 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C10.q2_le_4989 hu hc)

theorem disp_hr_4980 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4980 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C11.q2_le_4980 hu hc)

theorem disp_hr_4985 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4985 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C11.q2_le_4985 hu hc)

theorem disp_hr_4997 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4997 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C11.q2_le_4997 hu hc)

theorem disp_hr_4436 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4436 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4436 hu hc)

theorem disp_hr_4529 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4529 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4529 hu hc)

theorem disp_hr_4589 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4589 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4589 hu hc)

theorem disp_hr_4711 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4711 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4711 hu hc)

theorem disp_hr_4713 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4713 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4713 hu hc)

theorem disp_hr_4778 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4778 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4778 hu hc)

theorem disp_hr_4805 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4805 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4805 hu hc)

theorem disp_hr_4806 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4806 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4806 hu hc)

theorem disp_hr_4807 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4807 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4807 hu hc)

theorem disp_hr_4814 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4814 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4814 hu hc)

theorem disp_hr_4815 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4815 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4815 hu hc)

theorem disp_hr_4816 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4816 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4816 hu hc)

theorem disp_hr_4817 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4817 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4817 hu hc)

theorem disp_hr_4818 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4818 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4818 hu hc)

theorem disp_hr_4819 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4819 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4819 hu hc)

theorem disp_hr_4820 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4820 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4820 hu hc)

theorem disp_hr_4822 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4822 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4822 hu hc)

theorem disp_hr_4833 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4833 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4833 hu hc)

theorem disp_hr_4834 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4834 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4834 hu hc)

theorem disp_hr_4835 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4835 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4835 hu hc)

theorem disp_hr_4836 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4836 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4836 hu hc)

theorem disp_hr_4837 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4837 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4837 hu hc)

theorem disp_hr_4838 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4838 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4838 hu hc)

theorem disp_hr_4839 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4839 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4839 hu hc)

theorem disp_hr_4840 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4840 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4840 hu hc)

theorem disp_hr_4851 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4851 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4851 hu hc)

theorem disp_hr_4852 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4852 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4852 hu hc)

theorem disp_hr_4853 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4853 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4853 hu hc)

theorem disp_hr_4854 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4854 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4854 hu hc)

theorem disp_hr_4855 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4855 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4855 hu hc)

theorem disp_hr_4856 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4856 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4856 hu hc)

theorem disp_hr_4859 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4859 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4859 hu hc)

theorem disp_hr_4860 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4860 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4860 hu hc)

theorem disp_hr_4885 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4885 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4885 hu hc)

theorem disp_hr_4899 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4899 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4899 hu hc)

theorem disp_hr_4900 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4900 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4900 hu hc)

theorem disp_hr_4911 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4911 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4911 hu hc)

theorem disp_hr_4912 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4912 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4912 hu hc)

theorem disp_hr_4913 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4913 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4913 hu hc)

theorem disp_hr_4914 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4914 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4914 hu hc)

theorem disp_hr_4915 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4915 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4915 hu hc)

theorem disp_hr_4916 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4916 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4916 hu hc)

theorem disp_hr_4917 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4917 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4917 hu hc)

theorem disp_hr_4918 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4918 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4918 hu hc)

theorem disp_hr_4932 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4932 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4932 hu hc)

theorem disp_hr_4972 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4972 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C12.q2_le_4972 hu hc)

theorem disp_hr_4841 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4841 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4841 hu hc)

theorem disp_hr_4842 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4842 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4842 hu hc)

theorem disp_hr_4848 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4848 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4848 hu hc)

theorem disp_hr_4849 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4849 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4849 hu hc)

theorem disp_hr_4877 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4877 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4877 hu hc)

theorem disp_hr_4955 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4955 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C13.q2_le_4955 hu hc)

theorem disp_hr_4845 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4845 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4845 hu hc)

theorem disp_hr_4847 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4847 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4847 hu hc)

theorem disp_hr_4857 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4857 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4857 hu hc)

theorem disp_hr_4858 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4858 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4858 hu hc)

theorem disp_hr_4861 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4861 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4861 hu hc)

theorem disp_hr_4862 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4862 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4862 hu hc)

theorem disp_hr_4863 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4863 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4863 hu hc)

theorem disp_hr_4864 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4864 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4864 hu hc)

theorem disp_hr_4865 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4865 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4865 hu hc)

theorem disp_hr_4866 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4866 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4866 hu hc)

theorem disp_hr_4886 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4886 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4886 hu hc)

theorem disp_hr_4887 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4887 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4887 hu hc)

theorem disp_hr_4888 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4888 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4888 hu hc)

theorem disp_hr_4999 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4999 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_4999 hu hc)

theorem disp_hr_5005 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5005 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_5005 hu hc)

theorem disp_hr_5009 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (5009 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C14.q2_le_5009 hu hc)

theorem disp_hr_4821 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4821 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4821 hu hc)

theorem disp_hr_4846 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4846 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4846 hu hc)

theorem disp_hr_4869 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4869 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4869 hu hc)

theorem disp_hr_4870 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4870 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4870 hu hc)

theorem disp_hr_4871 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4871 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4871 hu hc)

theorem disp_hr_4872 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4872 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4872 hu hc)

theorem disp_hr_4873 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4873 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4873 hu hc)

theorem disp_hr_4875 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4875 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4875 hu hc)

theorem disp_hr_4876 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4876 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4876 hu hc)

theorem disp_hr_4881 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4881 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4881 hu hc)

theorem disp_hr_4883 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4883 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4883 hu hc)

theorem disp_hr_4891 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4891 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4891 hu hc)

theorem disp_hr_4892 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4892 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4892 hu hc)

theorem disp_hr_4893 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4893 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4893 hu hc)

theorem disp_hr_4896 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4896 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4896 hu hc)

theorem disp_hr_4901 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4901 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4901 hu hc)

theorem disp_hr_4907 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4907 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4907 hu hc)

theorem disp_hr_4908 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4908 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4908 hu hc)

theorem disp_hr_4909 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4909 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4909 hu hc)

theorem disp_hr_4981 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4981 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4981 hu hc)

theorem disp_hr_4983 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4983 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2 (N11Formalization.DSHPatchSurvey.C15.q2_le_4983 hu hc)

/-! ## The two K5 cells (cluster k=5), from the ROOT-PAID containment
-/

theorem disp_hr_4935 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4935 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2
    (DSHPatchTemplate.K5.containment_sq_of_domain ⟨hu, Or.inl hc⟩)

theorem disp_hr_4957 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096
      (4957 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) :=
  DSHPatchBridge.leaf_hr_of_q2
    (DSHPatchTemplate.K5.containment_sq_of_domain ⟨hu, Or.inr hc⟩)

/-! ## Per-cluster membership dispatch (small disjunctions, one per cluster)
-/

theorem hr_of_mem_C0 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC0) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC0, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact disp_hr_4974 hu hc
  · exact disp_hr_4996 hu hc

theorem hr_of_mem_C1 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC1) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC1, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl
  · exact disp_hr_4958 hu hc

theorem hr_of_mem_C2 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC2) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact disp_hr_4823 hu hc
  · exact disp_hr_4824 hu hc

theorem hr_of_mem_C3 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC3) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC3, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl
  · exact disp_hr_5008 hu hc

theorem hr_of_mem_C4 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC4) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC4, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact disp_hr_4993 hu hc
  · exact disp_hr_5003 hu hc

theorem hr_of_mem_C6 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC6) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC6, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact disp_hr_4795 hu hc
  · exact disp_hr_4796 hu hc

theorem hr_of_mem_C7 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC7) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC7, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact disp_hr_4970 hu hc
  · exact disp_hr_5006 hu hc
  · exact disp_hr_5010 hu hc

theorem hr_of_mem_C8 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC8) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC8, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact disp_hr_4874 hu hc
  · exact disp_hr_4882 hu hc
  · exact disp_hr_4884 hu hc
  · exact disp_hr_4894 hu hc
  · exact disp_hr_4895 hu hc
  · exact disp_hr_4902 hu hc
  · exact disp_hr_4910 hu hc

theorem hr_of_mem_C9 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC9) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC9, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact disp_hr_4813 hu hc
  · exact disp_hr_4988 hu hc
  · exact disp_hr_5001 hu hc

theorem hr_of_mem_C10 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC10) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC10, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact disp_hr_4956 hu hc
  · exact disp_hr_4959 hu hc
  · exact disp_hr_4989 hu hc

theorem hr_of_mem_C11 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC11) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC11, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact disp_hr_4980 hu hc
  · exact disp_hr_4985 hu hc
  · exact disp_hr_4997 hu hc

theorem hr_of_mem_C12 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC12) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC12, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact disp_hr_4436 hu hc
  · exact disp_hr_4529 hu hc
  · exact disp_hr_4589 hu hc
  · exact disp_hr_4711 hu hc
  · exact disp_hr_4713 hu hc
  · exact disp_hr_4778 hu hc
  · exact disp_hr_4805 hu hc
  · exact disp_hr_4806 hu hc
  · exact disp_hr_4807 hu hc
  · exact disp_hr_4814 hu hc
  · exact disp_hr_4815 hu hc
  · exact disp_hr_4816 hu hc
  · exact disp_hr_4817 hu hc
  · exact disp_hr_4818 hu hc
  · exact disp_hr_4819 hu hc
  · exact disp_hr_4820 hu hc
  · exact disp_hr_4822 hu hc
  · exact disp_hr_4833 hu hc
  · exact disp_hr_4834 hu hc
  · exact disp_hr_4835 hu hc
  · exact disp_hr_4836 hu hc
  · exact disp_hr_4837 hu hc
  · exact disp_hr_4838 hu hc
  · exact disp_hr_4839 hu hc
  · exact disp_hr_4840 hu hc
  · exact disp_hr_4851 hu hc
  · exact disp_hr_4852 hu hc
  · exact disp_hr_4853 hu hc
  · exact disp_hr_4854 hu hc
  · exact disp_hr_4855 hu hc
  · exact disp_hr_4856 hu hc
  · exact disp_hr_4859 hu hc
  · exact disp_hr_4860 hu hc
  · exact disp_hr_4885 hu hc
  · exact disp_hr_4899 hu hc
  · exact disp_hr_4900 hu hc
  · exact disp_hr_4911 hu hc
  · exact disp_hr_4912 hu hc
  · exact disp_hr_4913 hu hc
  · exact disp_hr_4914 hu hc
  · exact disp_hr_4915 hu hc
  · exact disp_hr_4916 hu hc
  · exact disp_hr_4917 hu hc
  · exact disp_hr_4918 hu hc
  · exact disp_hr_4932 hu hc
  · exact disp_hr_4972 hu hc

theorem hr_of_mem_C13 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC13) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC13, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact disp_hr_4841 hu hc
  · exact disp_hr_4842 hu hc
  · exact disp_hr_4848 hu hc
  · exact disp_hr_4849 hu hc
  · exact disp_hr_4877 hu hc
  · exact disp_hr_4955 hu hc

theorem hr_of_mem_C14 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC14) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC14, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact disp_hr_4845 hu hc
  · exact disp_hr_4847 hu hc
  · exact disp_hr_4857 hu hc
  · exact disp_hr_4858 hu hc
  · exact disp_hr_4861 hu hc
  · exact disp_hr_4862 hu hc
  · exact disp_hr_4863 hu hc
  · exact disp_hr_4864 hu hc
  · exact disp_hr_4865 hu hc
  · exact disp_hr_4866 hu hc
  · exact disp_hr_4886 hu hc
  · exact disp_hr_4887 hu hc
  · exact disp_hr_4888 hu hc
  · exact disp_hr_4999 hu hc
  · exact disp_hr_5005 hu hc
  · exact disp_hr_5009 hu hc

theorem hr_of_mem_C15 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListC15) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListC15, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact disp_hr_4821 hu hc
  · exact disp_hr_4846 hu hc
  · exact disp_hr_4869 hu hc
  · exact disp_hr_4870 hu hc
  · exact disp_hr_4871 hu hc
  · exact disp_hr_4872 hu hc
  · exact disp_hr_4873 hu hc
  · exact disp_hr_4875 hu hc
  · exact disp_hr_4876 hu hc
  · exact disp_hr_4881 hu hc
  · exact disp_hr_4883 hu hc
  · exact disp_hr_4891 hu hc
  · exact disp_hr_4892 hu hc
  · exact disp_hr_4893 hu hc
  · exact disp_hr_4896 hu hc
  · exact disp_hr_4901 hu hc
  · exact disp_hr_4907 hu hc
  · exact disp_hr_4908 hu hc
  · exact disp_hr_4909 hu hc
  · exact disp_hr_4981 hu hc
  · exact disp_hr_4983 hu hc

theorem hr_of_mem_K5 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ} {c : Fin 5011}
    (hmem : c ∈ nidListK5) (hu : RootRangeBoxFull.InCertBox u)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 c)
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [nidListK5, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact disp_hr_4935 hu hc
  · exact disp_hr_4957 hu hc

/-! ## The single quantifier-rich dispatcher statements

Both are unconditional given the cell hypothesis: every case is a kernel-checked cluster
containment composed with the bridge.  No cluster-side lemma is assumed; the case split is by
enumeration, so a cell whose containment is missing would have to be deleted from the list
explicitly (see `DSHPatchDispatcherControl.lean` and the named gap in `nidListK5`).
-/

/-- **The 118 non-K5 cells**: any patch cell of the 16-cluster cover other than cluster 5 gets the leaf's `hr` premise (#7) unconditionally. -/
theorem dispatcher_hr_118 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : InPatchUnion y) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [InPatchUnion] at hc
  obtain ⟨c, hmem, hcell⟩ := hc
  simp only [nidList, List.mem_append] at hmem
  rcases hmem with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · exact hr_of_mem_C0 h0 hu hcell
  · exact hr_of_mem_C1 h1 hu hcell
  · exact hr_of_mem_C2 h2 hu hcell
  · exact hr_of_mem_C3 h3 hu hcell
  · exact hr_of_mem_C4 h4 hu hcell
  · exact hr_of_mem_C6 h5 hu hcell
  · exact hr_of_mem_C7 h6 hu hcell
  · exact hr_of_mem_C8 h7 hu hcell
  · exact hr_of_mem_C9 h8 hu hcell
  · exact hr_of_mem_C10 h9 hu hcell
  · exact hr_of_mem_C11 h10 hu hcell
  · exact hr_of_mem_C12 h11 hu hcell
  · exact hr_of_mem_C13 h12 hu hcell
  · exact hr_of_mem_C14 h13 hu hcell
  · exact hr_of_mem_C15 h14 hu hcell

/-- **All 120 patch cells**: the 118 non-K5 cells plus the two root-paid K5 cells.  The K5 case is sourced from `Patch120K5Actual` (root-imported 2026-09-30), NOT from patch-survey's still-pending c5 dual-cap gate. -/
theorem dispatcher_hr_all120 {u : Fin 12 → ℝ} {y : Fin 9 → ℝ}
    (hu : RootRangeBoxFull.InCertBox u)
    (hc : InPatchUnion120 y) :
    Real.sqrt (∑ i, (DSHPatchBridge.pinnedVec u y i) ^ 2) ≤ (729 / 50000 : ℝ) := by
  simp only [InPatchUnion120] at hc
  obtain ⟨c, hmem, hcell⟩ := hc
  simp only [nidList120, List.mem_append] at hmem
  rcases hmem with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact hr_of_mem_C0 h0 hu hcell
  · exact hr_of_mem_C1 h1 hu hcell
  · exact hr_of_mem_C2 h2 hu hcell
  · exact hr_of_mem_C3 h3 hu hcell
  · exact hr_of_mem_C4 h4 hu hcell
  · exact hr_of_mem_C6 h5 hu hcell
  · exact hr_of_mem_C7 h6 hu hcell
  · exact hr_of_mem_C8 h7 hu hcell
  · exact hr_of_mem_C9 h8 hu hcell
  · exact hr_of_mem_C10 h9 hu hcell
  · exact hr_of_mem_C11 h10 hu hcell
  · exact hr_of_mem_C12 h11 hu hcell
  · exact hr_of_mem_C13 h12 hu hcell
  · exact hr_of_mem_C14 h13 hu hcell
  · exact hr_of_mem_C15 h14 hu hcell
  · exact hr_of_mem_K5 h15 hu hcell

end

end N11Formalization.DSHPatchDispatcher

#check @N11Formalization.DSHPatchDispatcher.nidList
#check @N11Formalization.DSHPatchDispatcher.InPatchUnion
#check @N11Formalization.DSHPatchDispatcher.hr_of_mem_C0
#check @N11Formalization.DSHPatchDispatcher.hr_of_mem_C12
#check @N11Formalization.DSHPatchDispatcher.hr_of_mem_K5
#check @N11Formalization.DSHPatchDispatcher.dispatcher_hr_118
#check @N11Formalization.DSHPatchDispatcher.dispatcher_hr_all120
#print axioms N11Formalization.DSHPatchDispatcher.disp_hr_4974
#print axioms N11Formalization.DSHPatchDispatcher.disp_hr_5001
#print axioms N11Formalization.DSHPatchDispatcher.disp_hr_4935
#print axioms N11Formalization.DSHPatchDispatcher.hr_of_mem_C12
#print axioms N11Formalization.DSHPatchDispatcher.hr_of_mem_K5
#print axioms N11Formalization.DSHPatchDispatcher.dispatcher_hr_118
#print axioms N11Formalization.DSHPatchDispatcher.dispatcher_hr_all120
