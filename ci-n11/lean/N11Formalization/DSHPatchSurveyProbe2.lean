/-
DSH-PATCH-SURVEY probe 2 — the EXACT premise signatures an L3/L4 instance needs.

Purpose (lead request, task-9 auxiliary): give patch-template the real signatures of
  (a) the box types and operations (RatInterval / Mem / abs / sqrtHi / congruenceBox / augmentedBox),
  (b) every box-consuming lemma that turns membership into the leaf's premises
      (hrow, hdiag, hFsq, hCfrob, hgFrob, coercivity/Cq/hrowBox),
  (c) the tree-cell / hull / q interface used by the K5 paid patch,
so that its instance theorem is written against the kernel's actual argument order and types.

This file only #checks; it proves nothing.
-/
import Mathlib
import N11Formalization.FlashLocalFrobeniusLeafAllBox
import N11Formalization.FlashLocalFrobeniusLeafBoxNorm
import N11Formalization.ResumeIntervalMatrix
import N11Formalization.ResumeIntervalAugmented
import N11Formalization.ResumeIntervalCoercivity
import N11Formalization.ResumePinnedCoercivity
import N11Formalization.Patch120K5Actual
import N11Formalization.DBMTreeKernel
import N11Formalization.FlashLeafSplit
import N11Formalization.DBMSourceTreeData
import N11Formalization.ResumeNetworkIsometry

set_option autoImplicit false

namespace N11Formalization.DSHPatchSurvey

noncomputable section

/-! ## 1. interval kit -/

#check @RatInterval
#check @RatInterval.Mem
#check @RatInterval.abs
#check @RatInterval.abs_mem
#check @RatInterval.mem_le_hi
#check @RatInterval.mem_lo_le
#check @RatInterval.sqrtHi
#check @RatInterval.add
#check @RatInterval.sub
#check @RatInterval.mul
#check @RatInterval.ofRat
#check @RatInterval.ofRat_mem
#check @ResumeIntervalMatrix.isum
#check @ResumeIntervalMatrix.congruenceBox
#check @ResumeIntervalAugmented.augmentedBox
#check @ResumeIntervalAugmented.augmented_mem
#check @ResumeIntervalAugmented.coercivity_of_boxes
#check @ResumeIntervalCoercivity.nonneg_of_intervals
#check @ResumeIntervalCoercivity.dominance_of_intervals

/-! ## 2. the six membership→premise lemmas (what each box must satisfy) -/

#check @FlashLocal.hrow_of_boxes
#check @FlashLocal.hdiag_of_boxes
#check @FlashLocal.hFsq_of_boxes
#check @FlashLocal.hCfrob_of_boxes
#check @FlashLocal.hgFrob_of_boxes
#check @ResumeCoercivityCertificate.coercivity
#check @ResumePinnedCoercivity.pinned_coercivity
#check @FlashLocal.actualGram

/-! ## 3. the leaf consumer and the network/cover consumers (argument order) -/

#check @FlashLocal.local_gain_actual_frobenius_leaf_all_box
#check @FlashLocal.local_gain_actual_frobenius_leaf_box_norm
#check @FlashLocal.local_gain_actual_frobenius_leaf
#check @ResumeNetwork.stress_lower_bound
#check @ResumeNetwork.oracle_le_of_geometric_witnesses
#check @ResumeNetworkIsometry.oracle_isometry
#check @FlashLocal.disp

/-! ## 4. the tree-cell and hull interface (the paid K5 pattern to copy) -/

#check @DBMTreeKernel.matrix
#check @DBMSourceTree.data
#check @FlashLeafSplit.Cell
#check @FlashLeafSplit.tlift
#check @RootRangeBoxFull.InCertBox
#check @Patch120K5.k5lo
#check @Patch120K5.k5hi
#check @Patch120K5.memberOK
#check @Patch120K5.cell_in_hull
#check @Patch120K5.k5_q_le
#check @Patch120K5.k5_q_sqrt_le
#check @Patch120K5.sq_le_sq_of_abs_le
#check @Patch120K5.sum_sq_le_sum_sq_filter
#check @Patch120K5.linear_le_endpoints
#check @Patch120K5.coordU_0
#check @Patch120K5.coordL_0
#check @Patch120K5.Dq_pos
#check @Patch120K5.db4935
#check @Patch120K5Consumer.rows_of_tree_cell_4935
#check @Patch120K5Consumer.k5_hull_of_cell_4935
#check @Patch120K5Consumer.k5_q_of_cell_4935
#check @Patch120K5Consumer.k5_q_of_cell_4935_of_inCertBox
#check @Patch120K5Consumer.inCertBox_L
#check @Patch120K5Consumer.db4935_eq_tree
#check @Patch120K5Actual.q2_le_4935
#check @Patch120K5Actual.q_le
#check @Patch120K5Actual.local_gain_of_geometric_bound

end
end N11Formalization.DSHPatchSurvey
