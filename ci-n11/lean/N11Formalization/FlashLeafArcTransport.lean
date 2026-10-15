import Mathlib
import N11Formalization.FlashLeafChartConsume

/-!
# FlashLeafArcTransport -- the Cell-to-arc transport probe (first probe after C1548)

The point cover `FlashLeafSplit.split_cover` lives in cumulative-`t` space: `Cell d (tlift y)`
bounds `t_j - t_i` by `d i j`.  This file TRANSPORTS those bounds into geometric arc
containments on the unit circle, via the chart identity C1546 (`canonAnchors u j =
circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) j)`).

**Dead-end discipline (DEAD.md B7)**: no `arcWidth` functional is defined or used anywhere.
Everything is the DIRECTED-INTERVAL image `circleMap '' Set.Icc a b`; `circleMap` is 2pi-periodic
(`circleMap_add_two_pi`), so the wrap is harmless -- all statements are plain real intervals and
no branch analysis on `circleAngle` is ever needed.

## What Cell actually constrains (the step-3 answer)

Cell gives bounds for ALL pairs, in particular for every ADJACENT slot pair `(j, j+1)`:
* `L1` branch: `d j (j+1) = 1/2` for `j <= 3`, `= 1` for `j >= 4`;
* `R2` branch: `d j (j+1) = 1` for `j <= 3`, `= 1/2` for `j >= 4`.
So the transport is SLOT-WISE where the branch bound is `1/2`, and trivial (`y_j <= 1`,
from the simplex alone) elsewhere; the all-pairs form (`cell_anchorBounds`, below) is available
too and gives the same transport for MULTI-slot arcs.  Both shapes are provided.

## Main results

* `arc_of_cell_bound`: a Cell bound `d j (j+1) <= c` forces the segment-`j` anchor arc to
  CONTAIN the standard sub-arc of angle width `L - D * c` at the slot-`j` endpoint.
  (Orientation note: the Cell bound is an UPPER bound on `y_j = t_{j+1} - t_j`, hence a LOWER
  bound `L - D * c <= width_j` on the geometric width -- the guaranteed arc sits INSIDE the
  segment, not vice versa.)
* `arc_of_cell_bound_multi`: same for a multi-slot arc `i -> j` with width
  `(j-i)*L - D * d i j` (all-pairs Cell shape).
* `chart_arcs_bounded`: at the C891 root, in the `L1` branch the four slots `j <= 3` carry a
  certified sub-arc of width `L - D/2`; in the `R2` branch the five slots `j >= 4` do.
* `chart_arcs_bounded_full`: EVERY slot of EVERY branch carries a certified sub-arc of width
  `L - D` (this uses only `y_j <= 1`, i.e. no branch information).
* `cert_width_pos`: for the actual chart both certified widths are positive
  (`L - D = 2pi - 8L > 0`, `L - D/2 = pi - 7L/2 > 0`), via `arcsin (19/50) < pi / 8`.
* `anchorArc_far_eq_canon`: the far endpoint of the segment-`j` arc is exactly the canonical
  anchor `canonAnchors u (j+1)`, with the `j = 8` wrap absorbed by `circleMap_add_two_pi`.
-/

namespace N11Formalization.FlashLeafArcTransport

open N11Formalization N11Formalization.ResumeGlobal N11Formalization.FlashLeafSplit
  N11Formalization.FlashLeafRootChart N11Formalization.FlashLeafChartConsume

noncomputable section

/-! ## 1. Generic directed-interval image containment -/

/-- Widening the parameter interval widens the image arc (monotonicity of the image; the
2pi-periodicity of `circleMap` makes the directed-interval reading consistent globally). -/
theorem image_arc_sub_of_le {a w w' : ℝ} (h : w ≤ w') :
    circleMap '' Set.Icc a (a + w) ⊆ circleMap '' Set.Icc a (a + w') :=
  Set.image_mono (Set.Icc_subset_Icc le_rfl (by linarith))

/-- **Angle parameter along the interval**: every point of the directed arc
`circleMap '' Set.Icc a b` has a parameter representative `t` INSIDE `[a, b]`, hence its
angle parameter along the interval differs from the left endpoint by at most `b - a <= δ`.
(The `δ < 2pi` hypothesis is what makes "along the interval" the correct circular reading;
the parameter statement itself does not need it.  DEADED B7's `arcWidth` is not used:
this is a plain image-membership statement.) -/
theorem image_mem_param_close {a b δ : ℝ} (hab : b - a ≤ δ) (_hδ : δ < 2 * Real.pi) {x : Point}
    (hx : x ∈ circleMap '' Set.Icc a b) :
    ∃ t ∈ Set.Icc a b, circleMap t = x ∧ t - a ≤ δ := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, rfl, by linarith [ht.1, ht.2, hab]⟩

/-! ## 2. The anchorAngle / tlift bridge (all indices) -/

/-- **The bridge** (same filter set on both sides, pure division bookkeeping): the anchor angle
at any `Fin 10` index is the lift of `tlift`. -/
theorem anchorAngle_eq_tlift (L D : ℝ) (y : Fin 9 → ℝ) (k : Fin 10) :
    anchorAngle L D y (k : ℕ) = ((k : ℕ) : ℝ) * L - D * tlift y k := by
  unfold anchorAngle tlift
  ring

/-! ## 3. What Cell constrains (all pairs, two-sided) -/

/-- **Cell gives two-sided bounds on ALL-pairs anchor-angle differences** (for `i <= j`):
the arc from anchor `i` to anchor `j` has angle between `(j-i)*L - D * d i j` and
`(j-i)*L`.  The upper side only uses `tlift` monotonicity (`y >= 0`); the lower side is
exactly the Cell bound. -/
theorem cell_anchorBounds {L D : ℝ} (hD0 : 0 ≤ D) {y : Fin 9 → ℝ} (hy0 : ∀ q, 0 ≤ y q)
    {d : M} (hcell : Cell d (tlift y)) {i j : Fin 10} (hij : (i : ℕ) ≤ (j : ℕ)) :
    (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * L - D * d i j
        ≤ anchorAngle L D y (j : ℕ) - anchorAngle L D y (i : ℕ)
      ∧ anchorAngle L D y (j : ℕ) - anchorAngle L D y (i : ℕ)
        ≤ (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * L := by
  have eA := anchorAngle_eq_tlift L D y
  have hmono : tlift y i ≤ tlift y j := tlift_mono hy0 (Fin.le_iff_val_le_val.mpr hij)
  have hnn : 0 ≤ tlift y i := tlift_nonneg hy0 i
  have hd : tlift y j - tlift y i ≤ d i j := hcell i j
  have hjic : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) = ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) :=
    Nat.cast_sub hij
  have h1 : D * (tlift y j - tlift y i) ≤ D * d i j :=
    mul_le_mul_of_nonneg_left hd hD0
  rw [mul_sub] at h1
  have h3 : D * tlift y i ≤ D * tlift y j := mul_le_mul_of_nonneg_left hmono hD0
  -- expand the `(j-i)*L` product BEFORE linarith (it does no distributivity; the difference
  -- is the LEFT factor here, so this is `sub_mul`, not `mul_sub`)
  rw [eA i, eA j, hjic, sub_mul]
  constructor <;> linarith [h1, h3]

/-! ## 4. Adjacent-slot entries of the two branch matrices -/

/-- The `L1` entry at the adjacent slot pair `(j, j+1)`: `1/2` up to slot 3, `1` from slot 4. -/
theorem L1_adj_eq (j : Fin 9) :
    L1 (⟨(j : ℕ), by omega⟩ : Fin 10) (⟨(j : ℕ) + 1, by omega⟩ : Fin 10)
      = if (j : ℕ) ≤ 3 then (1 / 2 : ℝ) else 1 := by
  fin_cases j <;> simp [L1]

/-- The `R2` entry at the adjacent slot pair `(j, j+1)`: `1` up to slot 3, `1/2` from slot 4. -/
theorem R2_adj_eq (j : Fin 9) :
    R2 (⟨(j : ℕ), by omega⟩ : Fin 10) (⟨(j : ℕ) + 1, by omega⟩ : Fin 10)
      = if (j : ℕ) ≤ 3 then (1 : ℝ) else 1 / 2 := by
  fin_cases j <;> simp [R2]

/-! ## 5. The transport lemma -/

/-- **The arc transport** (the probe): a Cell bound `d j (j+1) <= c` on the adjacent slot
forces the segment-`j` anchor arc
`circleMap '' Set.Icc (a + θ_j) (a + θ_{j+1})` (with `θ` = `anchorAngle L D y`)
to CONTAIN the standard sub-arc of angle width `L - D * c` anchored at the slot-`j` endpoint.
The hypothesis shapes of `tlift_step` are restated verbatim so that `linarith` sees identical
`⟨↑j⟩`/`⟨↑j+1⟩` atoms (proof terms are irrelevant by proof irrelevance). -/
theorem arc_of_cell_bound {L D : ℝ} (hD0 : 0 ≤ D) {y : Fin 9 → ℝ} {d : M}
    (hcell : Cell d (tlift y)) (a : ℝ) (j : Fin 9) {c : ℝ}
    (hdc : d (⟨(j : ℕ), by omega⟩ : Fin 10) (⟨(j : ℕ) + 1, by omega⟩ : Fin 10) ≤ c) :
    circleMap '' Set.Icc (a + anchorAngle L D y (j : ℕ))
        (a + anchorAngle L D y (j : ℕ) + (L - D * c))
      ⊆ circleMap '' Set.Icc (a + anchorAngle L D y (j : ℕ))
          (a + anchorAngle L D y (j : ℕ) + width L D y j) := by
  have hstep : tlift y (⟨(j : ℕ) + 1, by omega⟩ : Fin 10)
      - tlift y (⟨(j : ℕ), by omega⟩ : Fin 10) = y j := tlift_step y j
  have hcell' : tlift y (⟨(j : ℕ) + 1, by omega⟩ : Fin 10)
      - tlift y (⟨(j : ℕ), by omega⟩ : Fin 10)
        ≤ d (⟨(j : ℕ), by omega⟩ : Fin 10) (⟨(j : ℕ) + 1, by omega⟩ : Fin 10) :=
    hcell (⟨(j : ℕ), by omega⟩ : Fin 10) (⟨(j : ℕ) + 1, by omega⟩ : Fin 10)
  have hyc : y j ≤ c := by linarith
  have hw : L - D * c ≤ width L D y j := by
    show L - D * c ≤ L - D * y j
    have h1 : D * y j ≤ D * c := mul_le_mul_of_nonneg_left hyc hD0
    linarith
  exact image_arc_sub_of_le hw

/-- **Multi-slot transport** (the all-pairs shape): for `i <= j` the arc from anchor `i` to
anchor `j` contains the standard sub-arc of width `(j-i)*L - D * d i j` at the `i`-endpoint. -/
theorem arc_of_cell_bound_multi {L D : ℝ} (hD0 : 0 ≤ D) {y : Fin 9 → ℝ} (hy0 : ∀ q, 0 ≤ y q)
    {d : M} (hcell : Cell d (tlift y)) (a : ℝ) {i j : Fin 10} (hij : (i : ℕ) ≤ (j : ℕ)) :
    circleMap '' Set.Icc (a + anchorAngle L D y (i : ℕ))
        (a + anchorAngle L D y (i : ℕ)
          + ((((j : ℕ) - (i : ℕ) : ℕ) : ℝ) * L - D * d i j))
      ⊆ circleMap '' Set.Icc (a + anchorAngle L D y (i : ℕ))
          (a + anchorAngle L D y (j : ℕ)) := by
  have hb := cell_anchorBounds (L := L) hD0 hy0 hcell hij
  exact Set.image_mono (Set.Icc_subset_Icc le_rfl (by linarith [hb.1]))

/-! ## 6. The root instantiation -/

/-- The chart parameter of canonical anchor `j` at the C891 root. -/
def rootParam (S : C891RootSpec) (L D : ℝ) (j : Fin 9) : ℝ :=
  rawAnchorAngle S.root 2 + anchorAngle L D (chartY S.root L D) (j : ℕ)

/-- The root chart point is a nonnegative simplex point (extracted from C1546). -/
theorem chart_root_simplex (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) :
    (∀ q : Fin 9, 0 ≤ chartY S.root L D q) ∧ ∑ q : Fin 9, chartY S.root L D q = 1 := by
  have hu : RootRangeBoxFull.InCertBox S.root := FlashRootNetwork.inCertBox_root S hlo hhi
  exact ⟨fun q => (chart_identity S.root hu hL hD q).1,
    (chart_identity S.root hu hL hD (⟨0, by omega⟩ : Fin 9)).2.1⟩

/-- **Branch-wise certified arcs at the root** (the assembly): `L1` branch bounds the four
adjacent slots `j <= 3` by `1/2`, `R2` branch bounds the five slots `j >= 4` by `1/2`; in each
branch the corresponding segments contain the standard sub-arc of width `L - D/2`. -/
theorem chart_arcs_bounded (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) :
    (∀ j : Fin 9, (j : ℕ) ≤ 3 →
        circleMap '' Set.Icc (rootParam S L D j) (rootParam S L D j + (L - D * (1 / 2 : ℝ)))
          ⊆ circleMap '' Set.Icc (rootParam S L D j)
              (rootParam S L D j + width L D (chartY S.root L D) j)) ∨
      (∀ j : Fin 9, 4 ≤ (j : ℕ) →
        circleMap '' Set.Icc (rootParam S L D j) (rootParam S L D j + (L - D * (1 / 2 : ℝ)))
          ⊆ circleMap '' Set.Icc (rootParam S L D j)
              (rootParam S L D j + width L D (chartY S.root L D) j)) := by
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  rcases chart_consume_root S hlo hhi hL hD with h | h
  · exact Or.inl fun j hj =>
      arc_of_cell_bound hDpos.le h (rawAnchorAngle S.root 2) j (by rw [L1_adj_eq j, if_pos hj])
  · exact Or.inr fun j hj =>
      arc_of_cell_bound hDpos.le h (rawAnchorAngle S.root 2) j (by rw [R2_adj_eq j, if_neg (by omega)])

/-- **Every slot, every branch** (no Cell information needed): since `0 <= y_j <= 1` on the
chart simplex, EVERY segment contains the standard sub-arc of width `L - D` at its slot-`j`
endpoint.  By `cert_width_pos` this width is positive for the actual chart, so no segment is
degenerate. -/
theorem chart_arcs_bounded_full (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) (j : Fin 9) :
    circleMap '' Set.Icc (rootParam S L D j) (rootParam S L D j + (L - D))
      ⊆ circleMap '' Set.Icc (rootParam S L D j)
          (rootParam S L D j + width L D (chartY S.root L D) j) := by
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  obtain ⟨hy0, _hy1⟩ := chart_root_simplex S hlo hhi hL hD
  have hyj : chartY S.root L D j ≤ 1 := by
    have h1 := Finset.single_le_sum (f := fun q : Fin 9 => chartY S.root L D q)
      (fun i _ => hy0 i) (Finset.mem_univ j)
    linarith
  have hw : L - D ≤ width L D (chartY S.root L D) j := by
    show L - D ≤ L - D * chartY S.root L D j
    have h1 : D * chartY S.root L D j ≤ D :=
      le_trans (mul_le_mul_of_nonneg_left hyj hDpos.le) (mul_one D).le
    linarith
  exact image_arc_sub_of_le hw

/-! ## 7. Width positivity and the far endpoint -/

/-- **Both certified widths are positive for the actual chart**: `L - D = 2pi - 8L` and
`L - D/2 = pi - 7L/2` are positive because `L = 2 arcsin (19/50) < pi/4`. -/
theorem cert_width_pos {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) : 0 < L - D ∧ 0 < L - (1 / 2 : ℝ) * D := by
  have hlt : L < Real.pi / 4 := by
    rw [hL]
    linarith [arcsin_R0_lt_pi_div_eight]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have e1 : L - D = 2 * Real.pi - 8 * L := by rw [hD]; ring
  have e2 : L - (1 / 2 : ℝ) * D = Real.pi - 7 * L / 2 := by rw [hD]; ring
  refine ⟨by rw [e1]; linarith, by rw [e2]; linarith⟩

/-- **The far endpoint of the segment-`j` arc is the canonical anchor `j+1`** (no wrap case,
`(j : ℕ) <= 7`).  Together with C1546 (`canonAnchors u j = circleMap (rootParam j)` at
parameter level) this says the segment arcs are exactly the arcs between consecutive
canonical anchors. -/
theorem anchorArc_far_eq_canon (u : Fin 12 → ℝ) (L D : ℝ) (hD0 : D ≠ 0)
    (_hD : D = 9 * L - 2 * Real.pi) {j : Fin 9} (hj : (j : ℕ) ≤ 7) :
    circleMap (rawAnchorAngle u 2
        + (anchorAngle L D (chartY u L D) (j : ℕ) + width L D (chartY u L D) j))
      = FlashRootNetwork.canonAnchors u (j + 1) := by
  rw [FlashLeafRootChart.canonAnchors_eq_circleMap_chart u L D hD0 (j + 1)]
  have hval : ((j + 1 : Fin 9) : ℕ) = (j : ℕ) + 1 := by
    rw [Fin.val_add]
    exact Nat.mod_eq_of_lt (by have := j.isLt; omega)
  have hstep : anchorAngle L D (chartY u L D) ((j : ℕ) + 1)
      = anchorAngle L D (chartY u L D) (j : ℕ) + width L D (chartY u L D) j := by
    linarith [anchor_succ_sub L D (chartY u L D) j]
  rw [hval]
  exact congrArg circleMap (by linarith)

/-- **The wrap case `j = 8`** (all atoms literal, per the `⟨↑k+1⟩` linarith-atom pitfall):
the far endpoint of segment 8 is the canonical anchor `0`; the equality walks over
`anchorAngle 9 = 2pi` (via the all-index bridge `anchorAngle_eq_tlift` and `tlift_step`)
and `circleMap_add_two_pi` is NOT even needed -- it is absorbed by `anchor_nine`-style
closure (`anchorAngle 9 = 2pi` is already the lifted identity). -/
theorem anchorArc_far_eq_canon_wrap (u : Fin 12 → ℝ) (L D : ℝ) (hD0 : D ≠ 0)
    (hD : D = 9 * L - 2 * Real.pi) :
    circleMap (rawAnchorAngle u 2
        + (anchorAngle L D (chartY u L D) 8
          + width L D (chartY u L D) (⟨8, by omega⟩ : Fin 9)))
      = FlashRootNetwork.canonAnchors u 0 := by
  rw [FlashLeafRootChart.canonAnchors_eq_circleMap_chart u L D hD0 0]
  show circleMap (rawAnchorAngle u 2
      + (anchorAngle L D (chartY u L D) 8
        + width L D (chartY u L D) (⟨8, by omega⟩ : Fin 9)))
    = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 0)
  have a8 : anchorAngle L D (chartY u L D) 8
      = 8 * L - D * tlift (chartY u L D) (⟨8, by omega⟩ : Fin 10) :=
    anchorAngle_eq_tlift L D (chartY u L D) (⟨8, by omega⟩ : Fin 10)
  have a9 : anchorAngle L D (chartY u L D) 9
      = 9 * L - D * tlift (chartY u L D) (⟨9, by omega⟩ : Fin 10) :=
    anchorAngle_eq_tlift L D (chartY u L D) (⟨9, by omega⟩ : Fin 10)
  have hdiff : tlift (chartY u L D) (⟨9, by omega⟩ : Fin 10)
      - tlift (chartY u L D) (⟨8, by omega⟩ : Fin 10)
      = chartY u L D (⟨8, by omega⟩ : Fin 9) :=
    tlift_step (chartY u L D) (⟨8, by omega⟩ : Fin 9)
  have hw8 : width L D (chartY u L D) (⟨8, by omega⟩ : Fin 9)
      = L - D * chartY u L D (⟨8, by omega⟩ : Fin 9) := rfl
  have hD1 : D * tlift (chartY u L D) (⟨9, by omega⟩ : Fin 10)
      - D * tlift (chartY u L D) (⟨8, by omega⟩ : Fin 10)
      = D * chartY u L D (⟨8, by omega⟩ : Fin 9) := by
    rw [← mul_sub, hdiff]
  have a0 : anchorAngle L D (chartY u L D) 0 = 0 := anchor_zero L D (chartY u L D)
  have e9 : anchorAngle L D (chartY u L D) 9 = 2 * Real.pi :=
    FlashLeafChartConsume.anchorAngle_chart_nine u hD hD0
  have harg : rawAnchorAngle u 2
      + (anchorAngle L D (chartY u L D) 8
        + width L D (chartY u L D) (⟨8, by omega⟩ : Fin 9))
      = rawAnchorAngle u 2 + 2 * Real.pi := by
    linarith [a8, a9, hD1, hw8, e9]
  rw [a0, harg, circleMap_add_two_pi]
  exact congrArg circleMap (by ring)

end

/-! ## Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.FlashLeafArcTransport.image_arc_sub_of_le
#print axioms N11Formalization.FlashLeafArcTransport.image_mem_param_close
#print axioms N11Formalization.FlashLeafArcTransport.anchorAngle_eq_tlift
#print axioms N11Formalization.FlashLeafArcTransport.cell_anchorBounds
#print axioms N11Formalization.FlashLeafArcTransport.L1_adj_eq
#print axioms N11Formalization.FlashLeafArcTransport.R2_adj_eq
#print axioms N11Formalization.FlashLeafArcTransport.arc_of_cell_bound
#print axioms N11Formalization.FlashLeafArcTransport.arc_of_cell_bound_multi
#print axioms N11Formalization.FlashLeafArcTransport.chart_root_simplex
#print axioms N11Formalization.FlashLeafArcTransport.chart_arcs_bounded
#print axioms N11Formalization.FlashLeafArcTransport.chart_arcs_bounded_full
#print axioms N11Formalization.FlashLeafArcTransport.cert_width_pos
#print axioms N11Formalization.FlashLeafArcTransport.anchorArc_far_eq_canon
#print axioms N11Formalization.FlashLeafArcTransport.anchorArc_far_eq_canon_wrap

end N11Formalization.FlashLeafArcTransport
