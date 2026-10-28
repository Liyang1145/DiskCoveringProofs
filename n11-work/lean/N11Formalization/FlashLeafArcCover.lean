import Mathlib
import N11Formalization.FlashLeafArcTransport
import N11Formalization.Assembly.G2Unified

/-!
# FlashLeafArcCover -- closing the two arc-side gaps (union + per-segment disk criterion)

Two pieces on top of `FlashLeafArcTransport` (the Cell→arc transport probe):

## 1. The nine segment arcs tile the full parameter interval

`chain_cover` is the abstract monotone-chain bisection (the `arc_chain_cover` pattern of
`Assembly/ArcCover`, written ONCE at the abstract level, no rational endpoints).  With the
anchor-angle step identity (`anchor_succ_sub`) and width nonnegativity (`width_mem_box` +
`0 ≤ L - D`), the nine segment arcs are exactly the chain cells of
`f k = rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) k`, so

    segment_arcs_union:  ⋃ j, (segment-j arc) = circleMap '' Icc raw2 (raw2 + anchorAngle .. 9)

and `anchorAngle .. 9 = 2π` (`anchor_nine` via C1546's `chartY_sum_one`) turns the right side
into the full `2π` image at the root (`chart_arcs_union`).  The wrap slot needs no special
treatment HERE: everything stays at parameter level inside one monotone real interval.

## 2. Every certified sub-arc point is covered by its own segment's ring disk

`disk_covers_arc` lifts the point-level inner-product criterion of
`ArcCover.dist_le_radius_of_inner` to arc level, in the chart's own coordinates: the disk is
centered on the segment's mid-direction `P + a` at the radial root
`ρ = cos a - sqrt(R² - sin² a)`, and every parameter point within `a` of the mid-direction is
within `R` of that center.  For the chart, `width_j / 2 = angleVec u (shift3 j)` (C1546's
`width_chartY`), so the disk center is exactly `rhoK u (shift3 j) • circleMap (P_j + width_j/2)`
and all premises are supplied by `RootRange` (`hR`, `hsin`, `hrho`) — no `thetaOf` alignment,
no mod-9 case analysis, no 2π shift bookkeeping (they are all absorbed into the segment's own
parameters).

**Consumer (lead question 3, answered)**: this serves (b), the C450 / `FlashLeafCover` tree
side.  The root attainment side already carries two independent proofs
(`ArcCover.circle_covered` for the fixed rational `uCert`, and `FlashRootNetwork.oracle_le_sq_root`
for the actual root via the 51-edge oracle) — a third derivation would be redundant.  The
`FlashLeafCover` tree has NO geometry at all (its own header: "No cover theorem for the tree"),
and its leaves need exactly this hypothesis-complete, arbitrary-`u` form.
-/

namespace N11Formalization.FlashLeafArcCover

open N11Formalization N11Formalization.ResumeGlobal N11Formalization.FlashLeafSplit
  N11Formalization.FlashLeafRootChart N11Formalization.FlashLeafChartConsume
  N11Formalization.FlashLeafArcTransport

noncomputable section

/-! ## 1. Abstract chain bisection (written once; no monotonicity needed) -/

/-- **Chain cover**: if `t` lies between `f 0` and `f 9`, it lies in one of the nine chain
cells `[f j, f (j+1)]`.  Abstract form of `ArcCover.arc_chain_cover` (no rational data). -/
theorem chain_cover {f : Fin 10 → ℝ} {t : ℝ} (h0 : f 0 ≤ t) (h9 : t ≤ f 9) :
    ∃ j : Fin 9, f ⟨(j : ℕ), by omega⟩ ≤ t ∧ t ≤ f ⟨(j : ℕ) + 1, by omega⟩ := by
  by_cases h1 : t ≤ f (⟨1, by omega⟩ : Fin 10)
  · exact ⟨⟨0, by omega⟩, h0, h1⟩
  · rw [not_le] at h1
    by_cases h2 : t ≤ f (⟨2, by omega⟩ : Fin 10)
    · exact ⟨⟨1, by omega⟩, le_of_lt h1, h2⟩
    · rw [not_le] at h2
      by_cases h3 : t ≤ f (⟨3, by omega⟩ : Fin 10)
      · exact ⟨⟨2, by omega⟩, le_of_lt h2, h3⟩
      · rw [not_le] at h3
        by_cases h4 : t ≤ f (⟨4, by omega⟩ : Fin 10)
        · exact ⟨⟨3, by omega⟩, le_of_lt h3, h4⟩
        · rw [not_le] at h4
          by_cases h5 : t ≤ f (⟨5, by omega⟩ : Fin 10)
          · exact ⟨⟨4, by omega⟩, le_of_lt h4, h5⟩
          · rw [not_le] at h5
            by_cases h6 : t ≤ f (⟨6, by omega⟩ : Fin 10)
            · exact ⟨⟨5, by omega⟩, le_of_lt h5, h6⟩
            · rw [not_le] at h6
              by_cases h7 : t ≤ f (⟨7, by omega⟩ : Fin 10)
              · exact ⟨⟨6, by omega⟩, le_of_lt h6, h7⟩
              · rw [not_le] at h7
                by_cases h8 : t ≤ f (⟨8, by omega⟩ : Fin 10)
                · exact ⟨⟨7, by omega⟩, le_of_lt h7, h8⟩
                · rw [not_le] at h8
                  exact ⟨⟨8, by omega⟩, le_of_lt h8, h9⟩

/-! ## 2. Anchor-angle chain facts -/

/-- Step monotonicity of the anchor angle (widths nonnegative). -/
theorem anchorAngle_succ {L D : ℝ} {y : Fin 9 → ℝ} (hw0 : ∀ i : Fin 9, 0 ≤ width L D y i)
    (n : ℕ) (hn : n < 9) :
    anchorAngle L D y n ≤ anchorAngle L D y (n + 1) := by
  have hs : anchorAngle L D y (n + 1) - anchorAngle L D y n
      = width L D y (⟨n, by omega⟩ : Fin 9) := anchor_succ_sub L D y (⟨n, by omega⟩ : Fin 9)
  linarith [hw0 (⟨n, by omega⟩ : Fin 9)]

/-- Monotonicity of the anchor angle along the chain (both indices in `[0, 9]`). -/
theorem anchorAngle_mono {L D : ℝ} {y : Fin 9 → ℝ} (hw0 : ∀ i : Fin 9, 0 ≤ width L D y i)
    {j : ℕ} (hj : j < 9) :
    ∀ {k : ℕ}, j ≤ k → k ≤ 9 → anchorAngle L D y j ≤ anchorAngle L D y k := by
  intro k
  induction k with
  | zero =>
      intro h _
      have hj0 : j = 0 := by omega
      rw [hj0]
  | succ n ih =>
      intro h hk
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_refl _
      · exact le_trans (ih (by omega) (by omega))
          (anchorAngle_succ hw0 n (by omega))

/-! ## 3. The nine segment arcs tile the chart parameter interval -/

/-- **The nine segment arcs tile the parameter interval** (item 1): the union of the nine
segment images is the image of the whole chain interval `[raw 2, raw 2 + θ₉]`, with
`θ₉ = 2π` on the chart (`anchor_nine`).  The wrap slot needs no case split: the whole union
lives at parameter level inside one real interval. -/
theorem segment_arcs_union (u : Fin 12 → ℝ) (L D : ℝ) (hD0 : 0 ≤ D) (hLD : 0 ≤ L - D)
    (hy0 : ∀ q, 0 ≤ chartY u L D q) (hy1 : ∑ q, chartY u L D q = 1) :
    ⋃ j : Fin 9, circleMap '' Set.Icc (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ))
        (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ)
          + width L D (chartY u L D) j)
      = circleMap '' Set.Icc (rawAnchorAngle u 2)
          (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 9) := by
  have hw0 : ∀ i : Fin 9, 0 ≤ width L D (chartY u L D) i :=
    fun i => le_trans hLD ((width_mem_box L D (chartY u L D) hy0 hy1 hD0 i).1)
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨j, t, ⟨ht1, ht2⟩, rfl⟩ := hx
    refine Set.mem_image_of_mem _ ⟨?_, ?_⟩
    · have hge : anchorAngle L D (chartY u L D) 0
        ≤ anchorAngle L D (chartY u L D) (j : ℕ) :=
        anchorAngle_mono hw0 (by norm_num) (by omega) (by have := j.isLt; omega)
      rw [anchor_zero] at hge
      linarith [hge, ht1]
    · have hstep : anchorAngle L D (chartY u L D) ((j : ℕ) + 1)
        = anchorAngle L D (chartY u L D) (j : ℕ) + width L D (chartY u L D) j := by
        linarith [anchor_succ_sub L D (chartY u L D) j]
      have hup : anchorAngle L D (chartY u L D) ((j : ℕ) + 1)
        ≤ anchorAngle L D (chartY u L D) 9 := by
        by_cases hjeq : (j : ℕ) + 1 = 9
        · rw [hjeq]
        · have hlt : (j : ℕ) + 1 < 9 := by omega
          exact anchorAngle_mono (j := (j : ℕ) + 1) (k := 9) hw0 hlt hlt.le (by norm_num)
      linarith [ht1, ht2, hstep, hup]
  · intro t ht
    simp only [Set.mem_image] at ht
    obtain ⟨s, ⟨ht1, ht2⟩, rfl⟩ := ht
    obtain ⟨j, hjlo, hjhi⟩ :=
      chain_cover (f := fun k : Fin 10 =>
        rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (k : ℕ))
      (by
        show rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 0 ≤ s
        rw [anchor_zero]
        linarith)
      ht2
    refine Set.mem_iUnion.mpr ⟨j, s, ⟨hjlo, ?_⟩, rfl⟩
    have hstep : anchorAngle L D (chartY u L D) ((j : ℕ) + 1)
        = anchorAngle L D (chartY u L D) (j : ℕ) + width L D (chartY u L D) j := by
      linarith [anchor_succ_sub L D (chartY u L D) j]
    linarith

/-- **Root form of the tiling** (item 1, the single statement): the nine segment arcs at the
C891 root tile the full `2π` image `circleMap '' Icc raw2 (raw2 + 2π)`. -/
theorem chart_arcs_union (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) :
    ⋃ j : Fin 9, circleMap '' Set.Icc (rootParam S L D j)
        (rootParam S L D j + width L D (chartY S.root L D) j)
      = circleMap '' Set.Icc (rawAnchorAngle S.root 2)
          (rawAnchorAngle S.root 2 + 2 * Real.pi) := by
  obtain ⟨hy0, hy1⟩ := chart_root_simplex S hlo hhi hL hD
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  have hLD := (cert_width_pos hL hD).1.le
  have h9 : anchorAngle L D (chartY S.root L D) 9 = 2 * Real.pi :=
    anchorAngle_chart_nine S.root hD hDpos.ne'
  have hmain := segment_arcs_union S.root L D hDpos.le hLD hy0 hy1
  rw [h9] at hmain
  exact hmain

/-! ## 4. Arc-level disk criterion (item 2) -/

/-- **Arc-level disk criterion** (the lift of `ArcCover.dist_le_radius_of_inner` to a whole
parameter window, in the chart's own coordinates): every unit-circle point whose parameter is
within half-width `a` of the mid-direction `P + a` is within `R` of the disk centered at the
radial root `ρ = cos a - sqrt(R² - sin² a)` on that mid-direction. -/
theorem disk_covers_arc {P a R : ℝ} (hπ : a ≤ Real.pi) (hR : 0 ≤ R)
    (hs : Real.sin a ^ 2 ≤ R ^ 2)
    (hρ0 : 0 ≤ Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2))
    {t : ℝ} (ht : |t - (P + a)| ≤ a) :
    dist (circleMap t)
        ((Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) • circleMap (P + a)) ≤ R := by
  have hroot := radial_root_relation (a := a) (R := R) hs
  have hnorm2 : ‖((Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) • circleMap (P + a) : Point)‖ ^ 2
      = (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) ^ 2 := by
    rw [norm_smul, circleMap_norm, mul_one, Real.norm_eq_abs, sq_abs]
  have hinner : inner ℝ (circleMap t)
        ((Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) • circleMap (P + a))
      = (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) * Real.cos (t - (P + a)) := by
    rw [real_inner_smul_right, inner_circleMap]
  have hcos : Real.cos a ≤ Real.cos (t - (P + a)) := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hπ ht
    rwa [Real.cos_abs] at h1
  have hkey : 1 + ‖((Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) • circleMap (P + a) : Point)‖ ^ 2
      - R ^ 2 ≤ 2 * inner ℝ (circleMap t)
        ((Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) • circleMap (P + a)) := by
    rw [hnorm2, hinner]
    have h2 : 1 + (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) ^ 2 - R ^ 2
        = 2 * (Real.cos a - Real.sqrt (R ^ 2 - Real.sin a ^ 2)) * Real.cos a := by
      linarith
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left hcos hρ0
    linarith
  exact (mem_sphere_closedBall_iff hR (circleMap_norm t)).mpr hkey

/-- **Certified sub-arcs are disk-covered** (item 2, root instantiation): every point of the
slot-`j` certified sub-arc (width `L - D`, no Cell information needed) is within `R*` of the
segment-`j` ring disk, whose center is the radial root `rhoK S.root (shift3 j)` on the
segment's own mid-direction `P_j + width_j / 2`.  All disk premises come from `RootRange`
(`hR`, `hsin`, `hrho`) — the same radial-root data the root oracle consumes. -/
theorem chart_subArc_disk_covered (S : C891RootSpec) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50))
    (hD : D = 9 * L - 2 * Real.pi) (hu : RootRangeBoxFull.InCertBox S.root)
    (HR : RootRange S.root) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Set.Icc (rootParam S L D j) (rootParam S L D j + (L - D))) :
    dist (circleMap t) (rhoK S.root (shift3 j)
        • circleMap (rootParam S L D j + width L D (chartY S.root L D) j / 2))
      ≤ S.root 6 := by
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  have hDne : D ≠ 0 := hDpos.ne'
  obtain ⟨hy0, hy1⟩ := chart_root_simplex S hlo hhi hL hD
  have ha : width L D (chartY S.root L D) j / 2 = angleVec S.root (shift3 j) := by
    rw [width_chartY S.root hDne j]
    ring
  have hyj : chartY S.root L D j ≤ 1 := by
    have h1 := Finset.single_le_sum (f := fun q : Fin 9 => chartY S.root L D q)
      (fun i _ => hy0 i) (Finset.mem_univ j)
    linarith
  have hwidth : L - D ≤ width L D (chartY S.root L D) j := by
    show L - D ≤ L - D * chartY S.root L D j
    have h2 : D * chartY S.root L D j ≤ D * 1 :=
      mul_le_mul_of_nonneg_left hyj hDpos.le
    rw [mul_one] at h2
    linarith
  have h2a : width L D (chartY S.root L D) j = 2 * angleVec S.root (shift3 j) :=
    width_chartY S.root hDne j
  rw [ha]
  refine disk_covers_arc (a := angleVec S.root (shift3 j)) (R := S.root 6) ?_ HR.hR
    (HR.hsin (shift3 j)) (HR.hrho (shift3 j)) ?_
  · have hle := angleVec_le_arcsin S.root hu (shift3 j)
    linarith [hle, arcsin_R0_lt_pi_div_eight, Real.pi_pos]
  · rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hwidth, h2a]

/-! ## 5. The Covers sentence (general u) -/

/-- `circleMap` is invariant under integer multiples of `2π`. -/
theorem circleMap_add_int_two_pi (t : ℝ) (k : ℤ) :
    circleMap (t + (k : ℝ) * (2 * Real.pi)) = circleMap t := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;>
    simp [circleMap, Real.cos_add_int_mul_two_pi t k, Real.sin_add_int_mul_two_pi t k]

/-- **Fundamental window**: any real `t` can be shifted by an integer multiple of `2π` into
the half-open window `[c, c + 2π)`. -/
theorem exists_shift_int_two_pi (c t : ℝ) :
    ∃ k : ℤ, c < t + (k : ℝ) * (2 * Real.pi) ∧ t + (k : ℝ) * (2 * Real.pi) ≤ c + 2 * Real.pi := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hcast : ((Int.floor ((c - t) / (2 * Real.pi)) + 1 : ℤ) : ℝ)
      = (Int.floor ((c - t) / (2 * Real.pi)) : ℝ) + 1 := by norm_cast
  refine ⟨Int.floor ((c - t) / (2 * Real.pi)) + 1, ?_, ?_⟩
  · have hA : (c - t) / (2 * Real.pi)
        < ((Int.floor ((c - t) / (2 * Real.pi)) : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hAlt : (c - t) / (2 * Real.pi)
        < ((Int.floor ((c - t) / (2 * Real.pi)) + 1 : ℤ) : ℝ) := by
      linarith [hA, hcast]
    have h1 := mul_lt_mul_of_pos_right hAlt h2π
    rw [div_mul_cancel₀ _ (ne_of_gt h2π)] at h1
    linarith
  · have hB : (Int.floor ((c - t) / (2 * Real.pi)) : ℝ) ≤ (c - t) / (2 * Real.pi) :=
      Int.floor_le _
    have hBle : ((Int.floor ((c - t) / (2 * Real.pi)) + 1 : ℤ) : ℝ)
        ≤ (c - t) / (2 * Real.pi) + 1 := by
      linarith [hB, hcast]
    have h2 := mul_le_mul_of_nonneg_right hBle (le_of_lt h2π)
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h2π)] at h2
    linarith

/-- **Segment points are disk-covered** (general u): every parameter point of the FULL
segment-`j` arc is within `u 6` of the segment-`j` ring disk, whose center is the radial root
`rhoK u (shift3 j)` on the segment's own mid-direction.  All disk premises come from
`RootRange u` (`hR`, `hapi`, `hsin`, `hrho`) — not root-exclusive. -/
theorem segment_point_disk_covered (u : Fin 12 → ℝ) (L D : ℝ) (hDne : D ≠ 0)
    (HR : RootRange u) (j : Fin 9) {s : ℝ}
    (hs : s ∈ Set.Icc (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ))
        (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ)
          + width L D (chartY u L D) j)) :
    dist (circleMap s) (rhoK u (shift3 j)
        • circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ)
          + width L D (chartY u L D) j / 2)) ≤ u 6 := by
  have ha : width L D (chartY u L D) j / 2 = angleVec u (shift3 j) := by
    rw [width_chartY u hDne j]
    ring
  rw [ha]
  refine disk_covers_arc (a := angleVec u (shift3 j)) (R := u 6) (HR.hapi (shift3 j)) HR.hR
    (HR.hsin (shift3 j)) (HR.hrho (shift3 j)) ?_
  rw [abs_le]
  have h2a : width L D (chartY u L D) j = 2 * angleVec u (shift3 j) :=
    width_chartY u hDne j
  constructor
  · linarith [hs.1]
  · linarith [hs.2, h2a]

/-- **THE COVERS SENTENCE** (general u, complete form): for ANY `u` whose chart point is a
nonnegative simplex point and which satisfies `RootRange u`, every unit-circle point is within
`u 6` of one of the nine chart ring disks (radius = `u 6`, centers at the radial roots
`rhoK u (shift3 j)` on the segment mid-directions).

Premises, honestly labeled for leaf instantiation:
* `_hy0`/`hy1` — the chart point is a nonnegative simplex point.  `_hy0` is stated as part of
  the contract (it is what C1546's chart identity certifies) but the tiling + disk argument
  itself consumes only `hy1`;
* `hL`/`hD` — the actual chart parameters (`D = 9L − 2π > 0` derived internally);
* `HR : RootRange u` — the radial-root data; NOT root-exclusive, but the leaf must PAY it
  (same data the root oracle consumes).  Note the conclusion is about the chart's OWN nine
  ring disks (`rhoK u (shift3 j)`), not `ringCenter u k` — the two coincide modulo the
  canonical reindexing, which the leaf consumer inherits from C1546. -/
theorem boundary_cover_sentence (u : Fin 12 → ℝ) (L D : ℝ)
    (hL : L = 2 * Real.arcsin (19 / 50)) (hD : D = 9 * L - 2 * Real.pi)
    (_hy0 : ∀ q, 0 ≤ chartY u L D q) (hy1 : ∑ q, chartY u L D q = 1)
    (HR : RootRange u) (x : Point) (hx : ‖x‖ = 1) :
    ∃ j : Fin 9, dist x (rhoK u (shift3 j)
        • circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (j : ℕ)
          + width L D (chartY u L D) j / 2)) ≤ u 6 := by
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  have hDne : D ≠ 0 := hDpos.ne'
  have h9 : anchorAngle L D (chartY u L D) 9 = 2 * Real.pi :=
    anchor_nine L D (chartY u L D) hy1 hD
  -- shift x's circle angle into the chart window [raw2, raw2 + θ₉]
  obtain ⟨k, hk1, hk2⟩ :=
    exists_shift_int_two_pi (rawAnchorAngle u 2) (circleAngle x)
  have hcshift : circleMap (circleAngle x + (k : ℝ) * (2 * Real.pi)) = x := by
    rw [circleMap_add_int_two_pi, circleMap_circleAngle x hx]
  -- the shifted parameter falls in one of the nine chain cells
  obtain ⟨j, hjlo, hjhi⟩ :=
    chain_cover (f := fun m : Fin 10 =>
      rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) (m : ℕ))
      (by
        show rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 0
          ≤ circleAngle x + (k : ℝ) * (2 * Real.pi)
        rw [anchor_zero]
        linarith)
      (by
        show circleAngle x + (k : ℝ) * (2 * Real.pi)
          ≤ rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 9
        rw [h9]
        linarith)
  refine ⟨j, ?_⟩
  rw [← hcshift]
  have hstep : anchorAngle L D (chartY u L D) ((j : ℕ) + 1)
      = anchorAngle L D (chartY u L D) (j : ℕ) + width L D (chartY u L D) j := by
    linarith [anchor_succ_sub L D (chartY u L D) j]
  exact segment_point_disk_covered u L D hDne HR j ⟨hjlo, by linarith [hjhi, hstep]⟩

end

/-! ## Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.FlashLeafArcCover.chain_cover
#print axioms N11Formalization.FlashLeafArcCover.anchorAngle_succ
#print axioms N11Formalization.FlashLeafArcCover.anchorAngle_mono
#print axioms N11Formalization.FlashLeafArcCover.segment_arcs_union
#print axioms N11Formalization.FlashLeafArcCover.chart_arcs_union
#print axioms N11Formalization.FlashLeafArcCover.disk_covers_arc
#print axioms N11Formalization.FlashLeafArcCover.chart_subArc_disk_covered
#print axioms N11Formalization.FlashLeafArcCover.circleMap_add_int_two_pi
#print axioms N11Formalization.FlashLeafArcCover.exists_shift_int_two_pi
#print axioms N11Formalization.FlashLeafArcCover.segment_point_disk_covered
#print axioms N11Formalization.FlashLeafArcCover.boundary_cover_sentence

end N11Formalization.FlashLeafArcCover
