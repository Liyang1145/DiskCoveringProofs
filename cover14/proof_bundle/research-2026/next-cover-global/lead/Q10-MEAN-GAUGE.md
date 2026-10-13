# Affine mean-angle gauge for adaptive flow bounds

Existing certificates set anchor0 angle=0. This is valid but can retain an artificial common-rotation contribution in interval angle widths. For each normalized deficit vector d with sum D define s_j=sum_{i<j} d_i and m=(sum_j s_j)/10. Replace angles theta_j=jL-s_j by theta'_j=jL-s_j+m. This is a common rotation separately for each configuration; it preserves every incidence feasibility and ordering, and does NOT impose symmetry on configurations. The angle map remains affine in d; vertices and all completeness proofs are unchanged. Sum theta'_j=45L exactly, removing the mean varying angle.

Each fixed balanced flow yields r>=sum g_j dot exp(i theta'_j)/sum||z||. The same concavity minorant proof applies on the affine image of a complete deficit polytope. A new kernel must explicitly record/verify this gauge and apply it at every vertex; old certificates remain in anchor0 gauge. Optimizer anchor proposals, endpoint-sign checks, and Fraction replay must use the SAME gauge and unwrapped branch. No gauge benefit assumed until a bounded old/new comparison.

Decision experiment: one previously inconclusive saved exterior cell, same polytope, compare anchor0 and mean gauge bounds, independently Fraction replay; no new global exclusion without original coverage provenance. A successful result can justify using the new gauge on remaining trees; failure only says this representation did not improve that test.

## Analytic audit clarification
Mean and anchor0 gauges produce different valid real-valued lower-bound functionals, not merely different interval widths for one unchanged functional. All sites and witnesses rotate with anchors; each balanced fixedflow applies to every representative. Comparisons are better/worse valid certificates, not an asserted monotone gauge improvement.

For h_j(theta)=g_j dot exp(i theta), if the whole vertexanglehull has length<pi AND its endpoints have h_j>=0, it lies in one closed positive semicircle (or g_j=0), so h_j is concave there. Otherwise eta>=||g_j|| ensures h_j(theta)-eta(theta-t0)^2/2 is concave globally. Affine composition preserves concavity, so completevertices suffice. t0 can mathematically be ANY fixed real number; any fixed per-index2pi lift is valid. Same-gauge t0 improves numerical quality/provenance but is not a soundness premise. Gauge tag assertions enforce intended dispatch.

The call to old fr.replay in mean mode is NOT removable dead code: its OLD scalar bound is unused, but it rebuilds sourcefaces/owners/incidence and proves exactflow balance. This is currently the mean kernel's balance verifier. Keep that validation if refactoring. Dyadic companion relies on Fraction wrapper for balance; its independent role is directaffineangle arithmetic, not a standalone fullvalidator.

Mean roundauditor takes min of Fraction anddyadic bounds of the SAME mean certificate. Automorphism transport is a proved permutation of wholeincidence systems carrying inequalities, not merely relabeling metadata. Completedclosedexteriorcoverage is still required before transportingcuts.
