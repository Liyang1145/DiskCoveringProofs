import Mathlib
import N11Formalization.Conditional.RootSpec
import N11Formalization.FlashLeafRootChart
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashLeafSplit

/-!
# FlashLeafChartConsume -- instantiating the chart identity at the C891 root

The chart identity (`FlashLeafRootChart.chart_identity`) holds for every `u` in the certificate
box.  This file wires it to the concrete tree-root split:

* `FlashLeafSplit.split_cover` covers the CHART POINT in cumulative-`t` space:
  for `y ≥ 0`, `∑ y = 1`, the min-plus cell `Cell L1 (tlift y)` or `Cell R2 (tlift y)` holds,
  where `Cell d t := ∀ i j, t j - t i ≤ d i j` and `tlift y k = ∑_{q<k} y_q`.
  This is a POINT cover of the chart simplex in `t`-coordinates (the DBM side), NOT a cover of
  the nine geometric anchor arcs -- recorded as the shape difference of this step.
* `chart_consume_root` instantiates it at `S.root` (the C891 root): the certificate
  identifications `boxLo/boxHi = boxLoCert/boxHiCert` give `InCertBox S.root`, whose chart point
  is a nonnegative simplex point by `chart_identity`, so the split applies verbatim.
* The `t`-side is bridged to the anchor-angle side: `tlift y k` is the normalised cumulative
  anchor angle `((k:ℝ)*L - anchorAngle L D y k) / D`, and consecutive `t`-differences are the
  chart slots (`tlift_step`).  Together with `anchorAngle_chart_nine` (the accumulated angle
  closes at `2π` after nine slots) this is the plank on which the arc-side transport will walk.
-/

namespace N11Formalization.FlashLeafChartConsume

open N11Formalization N11Formalization.ResumeGlobal N11Formalization.FlashLeafSplit
  N11Formalization.FlashLeafRootChart

/-! ## The `t`-side to anchor-angle-side bridge -/

/-- **The bridge**: the `t`-lift is the normalised cumulative anchor angle.  Both sides sum the
SAME filter set (`Fin 9` slots below `k`), so this is division bookkeeping only (`D ≠ 0`). -/
theorem tlift_eq_anchorAngle {L D : ℝ} (hD0 : D ≠ 0) (y : Fin 9 → ℝ) (k : Fin 10) :
    tlift y k = (((k : ℕ) : ℝ) * L - anchorAngle L D y (k : ℕ)) / D := by
  unfold tlift anchorAngle
  field_simp
  ring

/-- **Consecutive `t`-differences are the chart slots**: `t_{i+1} - t_i = y_i`. -/
theorem tlift_step (y : Fin 9 → ℝ) (i : Fin 9) :
    tlift y (⟨(i : ℕ) + 1, by omega⟩ : Fin 10)
      - tlift y (⟨(i : ℕ), by omega⟩ : Fin 10) = y i := by
  unfold tlift
  rw [filter_succ i, Finset.sum_insert (by simp)]
  ring

/-- **The chart's accumulated anchor angle closes at `2π` after nine slots** (the circleMap
lift is globally consistent on the chart). -/
theorem anchorAngle_chart_nine (u : Fin 12 → ℝ) {L D : ℝ} (hD : D = 9 * L - 2 * Real.pi)
    (hD0 : D ≠ 0) :
    anchorAngle L D (chartY u L D) 9 = 2 * Real.pi :=
  anchor_nine L D (chartY u L D) (chartY_sum_one u hD hD0) hD

/-! ## The root instantiation -/

/-- **The concrete root split covers the C891 root's chart point.**  Under the certificate
identifications `boxLo/boxHi = boxLoCert/boxHiCert`, `S.root` lies in the certificate box
(`FlashRootNetwork.inCertBox_root`), so `chart_identity` makes its chart point a nonnegative
simplex point -- exactly `split_cover`'s premises.  (No `sys`/`residual` hypothesis: the
`split_cover` premises do not involve the TC system; that side is the oracle/Covers consumer,
already carried by `FlashRootNetwork.oracle_le_sq_root`.) -/
theorem chart_consume_root (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) :
    Cell L1 (tlift (chartY S.root L D)) ∨ Cell R2 (tlift (chartY S.root L D)) := by
  have hu : RootRangeBoxFull.InCertBox S.root := FlashRootNetwork.inCertBox_root S hlo hhi
  have hy0 : ∀ q : Fin 9, 0 ≤ chartY S.root L D q := fun q => (chart_identity S.root hu hL hD q).1
  have hy1 := (chart_identity S.root hu hL hD (⟨0, by omega⟩ : Fin 9)).2.1
  exact split_cover hy0 hy1

end N11Formalization.FlashLeafChartConsume

#print axioms N11Formalization.FlashLeafChartConsume.tlift_eq_anchorAngle
#print axioms N11Formalization.FlashLeafChartConsume.tlift_step
#print axioms N11Formalization.FlashLeafChartConsume.anchorAngle_chart_nine
#print axioms N11Formalization.FlashLeafChartConsume.chart_consume_root
