import N11Formalization.SevenClassQ0Deg3UpperReduction

/-! Lane A: the right-endpoint monotonicity premise for `edgeUpper` is false.

The multiplier on edge 12 is positive, so `edgeUpper` decreases near the
origin.  The first bin already gives a kernel-checkable rational
counterexample; consequently the 21 edge endpoint checks cannot replace the
original all-grid edge obligations in this form. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3UpperReduction

open MetricAreaRationalCertificate
open SevenClassQ0Deg3UpperTables

theorem edgeBinMono_false : ¬ EdgeBinMono := by
  intro h
  have hh := h 12 0
  norm_num [edgeUpper, tableEdges, mu, nodeQ, binHi, binIndex,
    sinHiNLag, sinTQ, Finset.sum_range_succ, RatInterval.piHi] at hh

end N11Formalization.SevenClassQ0Deg3UpperReduction
