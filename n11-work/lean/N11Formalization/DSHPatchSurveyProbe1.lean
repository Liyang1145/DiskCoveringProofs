/-
DSH-PATCH-SURVEY probe 1 — constant provenance for the 120 sharp patches.

Purpose (line B groundwork, handoff §2B): print the ACTUAL Lean types/definitions of
the constants H0 / α / G / N / H / Cmat and of the layer-3 consumers, so the
inventory does not rely on names or numeric output.
No theorem is proved here; this is a signature/#print probe only.
-/
import Mathlib
import N11Formalization.FlashLocalH0
import N11Formalization.FlashLocalAdaptive
import N11Formalization.FlashLocalMixedPinned
import N11Formalization.FlashLocalDirectionalActual
import N11Formalization.ResumeCoercivityCertificate
import N11Formalization.ResumePinnedCoercivity
import N11Formalization.ResumeIntervalAugmented
import N11Formalization.ResumeIntervalCoercivity
import N11Formalization.ResumeRelativeScalar
import N11Formalization.FlashLocalFrobeniusLeafAllBox
import N11Formalization.FlashLocalFrobeniusLeafBoxNorm
import N11Formalization.FlashLocalFrobeniusGate
import N11Formalization.FlashLocalFrobeniusPinGate
import N11Formalization.Patch120K5Actual
import N11Formalization.SourceResponseKernelConsumer
import N11Formalization.SourceResponsePSDConsumer
import N11Formalization.SourceResponseFluxIdentity
import N11Formalization.SourceSchurResponseBinding
import N11Formalization.SourcePositiveHarmonicConsumer
import N11Formalization.SourceBoundaryStressPositive
import N11Formalization.SourceRadialFluxConsumer
import N11Formalization.SourceAlphaOf
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeStressComparison
import N11Formalization.FlashLeafSplit
import N11Formalization.DBMTreeKernel

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace N11Formalization.DSHPatchSurvey

noncomputable section

/-! ## A. constant definitions (the objects named in the obligation) -/

-- H0 (generic) and the mixed/adaptive coefficient matrices
#print N11Formalization.FlashLocal.H0mat
#print N11Formalization.FlashLocal.Cmat
#print N11Formalization.FlashLocal.Jx
#print N11Formalization.FlashLocal.Rad
#print N11Formalization.FlashLocal.Eform
#print N11Formalization.FlashLocal.frob
#print N11Formalization.FlashLocal.Tmat
#print N11Formalization.FlashLocal.Gmat
#print N11Formalization.FlashLocal.GtX
#print N11Formalization.FlashLocal.Qx

-- the coercivity carrier: augmented H + 2t G Gᵀ − μ I
#print N11Formalization.ResumeCoercivityCertificate.augmented
#print N11Formalization.ResumeIntervalAugmented.augmentedBox

-- network / cell objects (the patch cell geometry domain)
#print N11Formalization.ResumeNetwork.V2
#print N11Formalization.ResumeNetwork.Feasible
#print N11Formalization.ResumeNetwork.edgeLength
#print N11Formalization.FlashLeafSplit.Cell
#print N11Formalization.FlashLeafSplit.tlift
#print N11Formalization.ResumeStressComparison.anchorWeight

-- ACTUAL source objects (paid, non-generic)
#print N11Formalization.SourceResponseKernelConsumer.H0
#print N11Formalization.SourceResponseFluxIdentity.sourceResponse
#print N11Formalization.SourceSchurResponseBinding.sourceY
#print N11Formalization.SourcePositiveHarmonicConsumer.sourceH
#print N11Formalization.SourceRadialFluxConsumer.sourceLoad
#print N11Formalization.SourceAlphaOf.alphaOf
#print N11Formalization.SourceAlphaOf.alphaEdge

/-! ## B. full types of the layer-3 / layer-4 consumers -/

#check @N11Formalization.FlashLocal.directional_lower_actual
#check @N11Formalization.FlashLocal.mixed_cross_lower_pinned
#check @N11Formalization.FlashLocal.h0_quadratic_mixed_lower
#check @N11Formalization.FlashLocal.h0_energy_quadratic_lower
#check @N11Formalization.ResumeCoercivityCertificate.coercivity
#check @N11Formalization.ResumeCoercivityCertificate.directional_to_local_gain
#check @N11Formalization.ResumePinnedCoercivity.pinned_coercivity
#check @N11Formalization.ResumeIntervalAugmented.coercivity_of_boxes
#check @N11Formalization.ResumeIntervalCoercivity.nonneg_of_intervals
#check @N11Formalization.ResumeRelativeScalar.local_gain
#check @N11Formalization.ResumeRelativeScalar.stress_gate
#check @N11Formalization.FlashLocal.hgFrob_of_boxes
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box_norm
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_all_box
#check @N11Formalization.FlashLocal.hrow_of_boxes
#check @N11Formalization.FlashLocal.hdiag_of_boxes
#check @N11Formalization.FlashLocal.hFsq_of_boxes
#check @N11Formalization.FlashLocal.hCfrob_of_boxes
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_box

-- intended terminal / cover consumers (layer 4)
#check @N11Formalization.ResumeNetwork.stress_lower_bound
#check @N11Formalization.ResumeNetwork.oracle_le_of_geometric_witnesses
#check @N11Formalization.ResumeNetwork.oracle_le_feasible
#check @N11Formalization.ResumeNetwork.dirichlet_le_oracle

-- the only two kernel-proved patch containments (K5 cluster: cells 4935, 4957)
#check @N11Formalization.Patch120K5Actual.q2_le_4935
#check @N11Formalization.Patch120K5Actual.q2_le_4957
#check @N11Formalization.Patch120K5Actual.q_le
#check @N11Formalization.Patch120K5Actual.actual_pinned_norm_le
#check @N11Formalization.Patch120K5Actual.local_gain_of_geometric_bound
#check @N11Formalization.Patch120K5Actual.wrong_orientation_rejected
#check @N11Formalization.DBMTreeKernel.matrix

/-! ## C. actual source response/kernel facts (what is paid for H0/Λ) -/

#check @N11Formalization.SourceResponseKernelConsumer.H0_rowsum
#check @N11Formalization.SourceResponseKernelConsumer.H0_constant_kernel
#check @N11Formalization.SourceResponseKernelConsumer.H0_symmetric
#check @N11Formalization.SourceResponsePSDConsumer.Λ_psd
#check @N11Formalization.SourceResponsePSDConsumer.Λ_energy_eq_source
#check @N11Formalization.SourceResponseFluxIdentity.sourceResponse_rowsum
#check @N11Formalization.SourceResponseFluxIdentity.sourceResponse_rowsum_pos
#check @N11Formalization.SourceResponseFluxIdentity.actual_hsrc_eq_H0mat
#check @N11Formalization.SourceSchurResponseBinding.schur_eq_response
#check @N11Formalization.SourcePositiveHarmonicConsumer.sourceH_minimizes
#check @N11Formalization.SourceBoundaryStressPositive.stress_pos
#check @N11Formalization.SourceBoundaryStressPositive.canonical_nonneg

/-! ## D. axioms of the load-bearing consumers -/

#print axioms N11Formalization.FlashLocal.directional_lower_actual
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf_all_box
#print axioms N11Formalization.ResumeCoercivityCertificate.coercivity
#print axioms N11Formalization.ResumePinnedCoercivity.pinned_coercivity
#print axioms N11Formalization.ResumeIntervalAugmented.coercivity_of_boxes
#print axioms N11Formalization.Patch120K5Actual.q_le
#print axioms N11Formalization.Patch120K5Actual.local_gain_of_geometric_bound
#print axioms N11Formalization.SourceResponseFluxIdentity.actual_hsrc_eq_H0mat

end
end N11Formalization.DSHPatchSurvey
