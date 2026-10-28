import Mathlib
import N11Formalization.TCSystem
import N11Formalization.Geometry.ArcCovering
import N11Formalization.ResumeAnchorAngles
import N11Formalization.ResumeGlobalAnchor
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.Interval.ArcsinBracket

/-!
# FlashLeafRootChart -- the actual chart identity for the canonical anchors

The lead-pinned canonical indexing (raw ring k <-> canonical k-2 mod 9, hubs 9/10 fixed) says the
canonical anchor at label j is the RAW anchor at label j+2, whose own angle is

    rawAnchorAngle u k = thetaOf (angleVec u) k + angleVec u k       (ResumeAnchorAngles)

with anchor-to-anchor gap `2 * a_{k+1}` -- NOT `a_k + a_{k+1}` (that is the CENTRE-angle increment;
`Uvec` is the FACE witness, not the circle anchor).

So the canonical anchor network is the rotated `circleMap` accumulating the widths

    width L D y i = L - D * y i          (ResumeGlobal.width)

for the chart point read off the ORIGINAL angles at the +3 shift:

    y i = (L - 2 * a_{(i+3) mod 9}) / D .

This file proves the exact algebraic core: the chart width is the raw anchor gap, the chart
point is a point of the CLOSED 9-simplex (`sum y = 1`) as soon as `D = 9L - 2*pi` and `D > 0`,
it is NONNEGATIVE for every `u` in the certificate box (obligation (a): every box angle is
`<= arcsin (19/50) = L/2`), and the canonical anchors ARE the accumulating rotated circle
(obligation (b): the lifted nine-slot telescope with exactly one wrap, `k = 8`).
`sum y = 1` is EXACT (from `sum_angleVec u : sum a = pi`).
-/

namespace N11Formalization.FlashLeafRootChart

open N11Formalization N11Formalization.ResumeGlobal

/-- The +3 shift of a Fin 9 label. -/
def shift3 (i : Fin 9) : Fin 9 := ⟨((i : ℕ) + 3) % 9, by omega⟩

/-- The chart point read off the original angles at the +3 shift (lead-pinned canonical index). -/
noncomputable def chartY (u : Fin 12 → ℝ) (L D : ℝ) : Fin 9 → ℝ :=
  fun i => (L - 2 * angleVec u (shift3 i)) / D

/-- The +3 shift is a permutation of `Fin 9` (used for the exact sum identity). -/
theorem sum_shift3 (u : Fin 12 → ℝ) : ∑ i : Fin 9, angleVec u (shift3 i) = Real.pi := by
  have hfun : shift3 = fun i : Fin 9 => i + 3 := by
    funext i; ext; simp [shift3, Fin.val_add]
  rw [hfun]
  have hperm : (∑ i : Fin 9, angleVec u (i + 3)) = ∑ k : Fin 9, angleVec u k :=
    Equiv.sum_comp (Equiv.addRight (3 : Fin 9)) (fun k => angleVec u k)
  rw [hperm]
  exact sum_angleVec u

/-- **The chart width is the raw anchor gap**: `width L D y i = 2 * a_{i+3}`. -/
theorem width_chartY (u : Fin 12 → ℝ) {L D : ℝ} (hD0 : D ≠ 0) (i : Fin 9) :
    width L D (chartY u L D) i = 2 * angleVec u (shift3 i) := by
  unfold width chartY
  field_simp
  ring

/-- **The chart point is a simplex point**: `sum y = 1`, exact, from `sum a = pi` and
`D = 9L - 2*pi`. -/
theorem chartY_sum_one (u : Fin 12 → ℝ) {L D : ℝ} (hD : D = 9 * L - 2 * Real.pi) (hD0 : D ≠ 0) :
    ∑ i : Fin 9, chartY u L D i = 1 := by
  have hnum : (∑ i : Fin 9, (L - 2 * angleVec u (shift3 i))) = 9 * L - 2 * Real.pi := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_shift3 u]
    ring
  calc ∑ i : Fin 9, chartY u L D i
      = (∑ i : Fin 9, (L - 2 * angleVec u (shift3 i))) / D := by
        simp only [chartY, Finset.sum_div]
    _ = 1 := by
        rw [hnum, hD]
        exact div_self (by rw [← hD]; exact hD0)

/-- **Elementary bound behind `D > 0`**: `sin(π/9) < 19/50`, from `sin x < x` and `π < 3.15`. -/
theorem sin_pi_div_nine_lt : Real.sin (Real.pi / 9) < 19 / 50 := by
  have h9 : 0 < Real.pi / 9 := by positivity
  have h1 : Real.sin (Real.pi / 9) < Real.pi / 9 := Real.sin_lt h9
  have h2 : Real.pi / 9 < 19 / 50 := by
    have := Real.pi_lt_d20
    linarith
  linarith

/-- **`D > 0`**: with `L = 2 * arcsin (19/50)`, `D = 9L - 2π > 0` (equivalently
`arcsin (19/50) > π/9`).  This is what upgrades `D ≠ 0` to a definite sign, so that the chart
`y i = (L - 2 a_{i+3})/D` is a genuine convex combination. -/
theorem D_pos : 0 < 9 * (2 * Real.arcsin (19 / 50)) - 2 * Real.pi := by
  have hx : Real.pi / 9 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨by have := Real.pi_pos; linarith, by have := Real.pi_pos; linarith⟩
  have harc : Real.arcsin (19 / 50) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.arcsin_mem_Icc _
  have hsin : Real.sin (Real.pi / 9) < Real.sin (Real.arcsin (19 / 50)) := by
    rw [Real.sin_arcsin (by norm_num : (-1 : ℝ) ≤ 19 / 50) (by norm_num : (19 : ℝ) / 50 ≤ 1)]
    exact sin_pi_div_nine_lt
  have hlt : Real.pi / 9 < Real.arcsin (19 / 50) :=
    (StrictMonoOn.lt_iff_lt Real.strictMonoOn_sin hx harc).mp hsin
  linarith

/-! ## Obligation (a): the chart point is nonnegative on the certificate box -/

/-- **Every certified-box angle is below the arc half-parameter** `arcsin (19/50)`.
Ring slots are bounded by the box tops (max `boxHiCert 3 ≈ 0.38303`); the centre slot
`a₄ = π − 2(a₀+a₁+a₂+a₃)` by `π < 3.1416` and the box bottoms (`3.1416 − 2·Σlo ≈ 0.38823`).
Both chains close on the rational lower endpoint of `ArcsinBracket.arcsin_19_50_mem`
(`asinLo ≈ 0.38979`). -/
theorem angleVec_le_arcsin (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) (k : Fin 9) :
    angleVec u k ≤ Real.arcsin (19 / 50) := by
  have hmem := ArcsinBracket.arcsin_19_50_mem
  have hcast : (((19 : ℚ) / 50 : ℚ) : ℝ) = (19 : ℝ) / 50 := by norm_num
  rw [hcast] at hmem
  have hlo := hmem.1
  have e0 : boxHiCert 0 = 1798923308088748990191253 / 2 ^ 82 := rfl
  have e1 : boxHiCert 1 = 1648215931906157556717205 / 2 ^ 82 := rfl
  have e2 : boxHiCert 2 = 1357971491037010555491989 / 2 ^ 82 := rfl
  have e3 : boxHiCert 3 = 1852132492922469008987797 / 2 ^ 82 := rfl
  have g0 : boxLoCert 0 = 1798923298417342433274219 / 2 ^ 82 := rfl
  have g1 : boxLoCert 1 = 1648215922234750999800171 / 2 ^ 82 := rfl
  have g2 : boxLoCert 2 = 1357971481365603998574955 / 2 ^ 82 := rfl
  have g3 : boxLoCert 3 = 1852132483251062452070763 / 2 ^ 82 := rfl
  have hi0 : ((boxHiCert 0 : ℚ) : ℝ)
      ≤ (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by
    rw [e0]; norm_num
  have hi1 : ((boxHiCert 1 : ℚ) : ℝ)
      ≤ (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by
    rw [e1]; norm_num
  have hi2 : ((boxHiCert 2 : ℚ) : ℝ)
      ≤ (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by
    rw [e2]; norm_num
  have hi3 : ((boxHiCert 3 : ℚ) : ℝ)
      ≤ (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by
    rw [e3]; norm_num
  have lo0 : (1798923298417342433274219 : ℝ) / 2 ^ 82 ≤ ((boxLoCert 0 : ℚ) : ℝ) := by
    rw [g0]; norm_num
  have lo1 : (1648215922234750999800171 : ℝ) / 2 ^ 82 ≤ ((boxLoCert 1 : ℚ) : ℝ) := by
    rw [g1]; norm_num
  have lo2 : (1357971481365603998574955 : ℝ) / 2 ^ 82 ≤ ((boxLoCert 2 : ℚ) : ℝ) := by
    rw [g2]; norm_num
  have lo3 : (1852132483251062452070763 : ℝ) / 2 ^ 82 ≤ ((boxLoCert 3 : ℚ) : ℝ) := by
    rw [g3]; norm_num
  have hcenter : Real.pi - 2 * (u 0 + u 1 + u 2 + u 3) ≤ Real.arcsin (19 / 50) := by
    have hp : Real.pi < 3.1416 := Real.pi_lt_d4
    have hrat : (3.1416 : ℝ) - 2 * ((1798923298417342433274219 : ℝ) / 2 ^ 82
        + (1648215922234750999800171 : ℝ) / 2 ^ 82 + (1357971481365603998574955 : ℝ) / 2 ^ 82
          + (1852132483251062452070763 : ℝ) / 2 ^ 82)
        ≤ (1150475603510479590494077 : ℝ) / 2951479051793528258560000 := by
      norm_num
    linarith [hp, hlo, hrat, (hu 0).1, (hu 1).1, (hu 2).1, (hu 3).1, lo0, lo1, lo2, lo3]
  fin_cases k
  · simp [angleVec]; linarith [(hu 0).2, hi0, hlo]
  · simp [angleVec]; linarith [(hu 1).2, hi1, hlo]
  · simp [angleVec]; linarith [(hu 2).2, hi2, hlo]
  · simp [angleVec]; linarith [(hu 3).2, hi3, hlo]
  · simp [angleVec]; linarith [hcenter]
  · simp [angleVec]; linarith [(hu 3).2, hi3, hlo]
  · simp [angleVec]; linarith [(hu 2).2, hi2, hlo]
  · simp [angleVec]; linarith [(hu 1).2, hi1, hlo]
  · simp [angleVec]; linarith [(hu 0).2, hi0, hlo]

/-- **(a) The chart point is nonnegative**: for `u` in the certificate box and the actual chart
`L = 2 arcsin (19/50)`, `D = 9L - 2π > 0`, every slot satisfies `0 ≤ chartY u L D i`. -/
theorem chartY_nonneg (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50)) (hD : D = 9 * L - 2 * Real.pi) (i : Fin 9) :
    0 ≤ chartY u L D i := by
  have hDpos : 0 < D := by
    rw [hD, hL]
    exact D_pos
  have hle := angleVec_le_arcsin u hu (shift3 i)
  unfold chartY
  exact div_nonneg (by rw [hL]; linarith) hDpos.le

/-! ## Obligation (b): the canonical anchors are the accumulating rotated circleMap -/

/-- **(b) The lifted nine-slot telescope**: the canonical anchor at label `j` (raw label
`(j+2) mod 9`) is the unit-circle point at angle `rawAnchorAngle u 2` accumulated by the chart
widths.  Over the 9-term chain there is exactly ONE wrap (raw `k = 8`, `rawAnchorAngle_wrap`),
the rest are `rawAnchorAngle_step` (`k : Fin 8`); `circleMap` is `2π`-periodic
(`circleMap_add_two_pi`), so the lift is harmless.  Needs only `D ≠ 0` (for `width_chartY`). -/
theorem canonAnchors_eq_circleMap_chart (u : Fin 12 → ℝ) (L D : ℝ) (hD0 : D ≠ 0) (j : Fin 9) :
    FlashRootNetwork.canonAnchors u j
      = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) j) := by
  have wr : rawAnchorAngle u 0 + 2 * Real.pi = rawAnchorAngle u 8 + 2 * angleVec u 0 := by
    linarith [rawAnchorAngle_wrap u]
  -- `show ... from` normalizes the `⟨↑k + 1⟩`-shaped indices to numerals (defeq) so that
  -- linarith's atom matching sees the same atoms as the per-case goals below.
  have s1 : rawAnchorAngle u 1 = rawAnchorAngle u 0 + 2 * angleVec u 1 := by
    linarith [show rawAnchorAngle u 1 - rawAnchorAngle u 0 = 2 * angleVec u 1 from
      rawAnchorAngle_step u (⟨0, by omega⟩ : Fin 8)]
  have s2 : rawAnchorAngle u 2 = rawAnchorAngle u 1 + 2 * angleVec u 2 := by
    linarith [show rawAnchorAngle u 2 - rawAnchorAngle u 1 = 2 * angleVec u 2 from
      rawAnchorAngle_step u (⟨1, by omega⟩ : Fin 8)]
  have s3 : rawAnchorAngle u 3 = rawAnchorAngle u 2 + 2 * angleVec u 3 := by
    linarith [show rawAnchorAngle u 3 - rawAnchorAngle u 2 = 2 * angleVec u 3 from
      rawAnchorAngle_step u (⟨2, by omega⟩ : Fin 8)]
  have s4 : rawAnchorAngle u 4 = rawAnchorAngle u 3 + 2 * angleVec u 4 := by
    linarith [show rawAnchorAngle u 4 - rawAnchorAngle u 3 = 2 * angleVec u 4 from
      rawAnchorAngle_step u (⟨3, by omega⟩ : Fin 8)]
  have s5 : rawAnchorAngle u 5 = rawAnchorAngle u 4 + 2 * angleVec u 5 := by
    linarith [show rawAnchorAngle u 5 - rawAnchorAngle u 4 = 2 * angleVec u 5 from
      rawAnchorAngle_step u (⟨4, by omega⟩ : Fin 8)]
  have s6 : rawAnchorAngle u 6 = rawAnchorAngle u 5 + 2 * angleVec u 6 := by
    linarith [show rawAnchorAngle u 6 - rawAnchorAngle u 5 = 2 * angleVec u 6 from
      rawAnchorAngle_step u (⟨5, by omega⟩ : Fin 8)]
  have s7 : rawAnchorAngle u 7 = rawAnchorAngle u 6 + 2 * angleVec u 7 := by
    linarith [show rawAnchorAngle u 7 - rawAnchorAngle u 6 = 2 * angleVec u 7 from
      rawAnchorAngle_step u (⟨6, by omega⟩ : Fin 8)]
  have s8 : rawAnchorAngle u 8 = rawAnchorAngle u 7 + 2 * angleVec u 8 := by
    linarith [show rawAnchorAngle u 8 - rawAnchorAngle u 7 = 2 * angleVec u 8 from
      rawAnchorAngle_step u (⟨7, by omega⟩ : Fin 8)]
  have c0 : anchorAngle L D (chartY u L D) 0 = 0 := anchor_zero L D _
  have c1 : anchorAngle L D (chartY u L D) 1
      = anchorAngle L D (chartY u L D) 0 + width L D (chartY u L D) 0 := by
    linarith [show anchorAngle L D (chartY u L D) 1 - anchorAngle L D (chartY u L D) 0
        = width L D (chartY u L D) 0 from
      anchor_succ_sub L D (chartY u L D) (⟨0, by omega⟩ : Fin 9)]
  have c2 : anchorAngle L D (chartY u L D) 2
      = anchorAngle L D (chartY u L D) 1 + width L D (chartY u L D) 1 := by
    linarith [show anchorAngle L D (chartY u L D) 2 - anchorAngle L D (chartY u L D) 1
        = width L D (chartY u L D) 1 from
      anchor_succ_sub L D (chartY u L D) (⟨1, by omega⟩ : Fin 9)]
  have c3 : anchorAngle L D (chartY u L D) 3
      = anchorAngle L D (chartY u L D) 2 + width L D (chartY u L D) 2 := by
    linarith [show anchorAngle L D (chartY u L D) 3 - anchorAngle L D (chartY u L D) 2
        = width L D (chartY u L D) 2 from
      anchor_succ_sub L D (chartY u L D) (⟨2, by omega⟩ : Fin 9)]
  have c4 : anchorAngle L D (chartY u L D) 4
      = anchorAngle L D (chartY u L D) 3 + width L D (chartY u L D) 3 := by
    linarith [show anchorAngle L D (chartY u L D) 4 - anchorAngle L D (chartY u L D) 3
        = width L D (chartY u L D) 3 from
      anchor_succ_sub L D (chartY u L D) (⟨3, by omega⟩ : Fin 9)]
  have c5 : anchorAngle L D (chartY u L D) 5
      = anchorAngle L D (chartY u L D) 4 + width L D (chartY u L D) 4 := by
    linarith [show anchorAngle L D (chartY u L D) 5 - anchorAngle L D (chartY u L D) 4
        = width L D (chartY u L D) 4 from
      anchor_succ_sub L D (chartY u L D) (⟨4, by omega⟩ : Fin 9)]
  have c6 : anchorAngle L D (chartY u L D) 6
      = anchorAngle L D (chartY u L D) 5 + width L D (chartY u L D) 5 := by
    linarith [show anchorAngle L D (chartY u L D) 6 - anchorAngle L D (chartY u L D) 5
        = width L D (chartY u L D) 5 from
      anchor_succ_sub L D (chartY u L D) (⟨5, by omega⟩ : Fin 9)]
  have c7 : anchorAngle L D (chartY u L D) 7
      = anchorAngle L D (chartY u L D) 6 + width L D (chartY u L D) 6 := by
    linarith [show anchorAngle L D (chartY u L D) 7 - anchorAngle L D (chartY u L D) 6
        = width L D (chartY u L D) 6 from
      anchor_succ_sub L D (chartY u L D) (⟨6, by omega⟩ : Fin 9)]
  have c8 : anchorAngle L D (chartY u L D) 8
      = anchorAngle L D (chartY u L D) 7 + width L D (chartY u L D) 7 := by
    linarith [show anchorAngle L D (chartY u L D) 8 - anchorAngle L D (chartY u L D) 7
        = width L D (chartY u L D) 7 from
      anchor_succ_sub L D (chartY u L D) (⟨7, by omega⟩ : Fin 9)]
  have w0 : width L D (chartY u L D) 0 = 2 * angleVec u 3 :=
    width_chartY u hD0 (⟨0, by omega⟩ : Fin 9)
  have w1 : width L D (chartY u L D) 1 = 2 * angleVec u 4 :=
    width_chartY u hD0 (⟨1, by omega⟩ : Fin 9)
  have w2 : width L D (chartY u L D) 2 = 2 * angleVec u 5 :=
    width_chartY u hD0 (⟨2, by omega⟩ : Fin 9)
  have w3 : width L D (chartY u L D) 3 = 2 * angleVec u 6 :=
    width_chartY u hD0 (⟨3, by omega⟩ : Fin 9)
  have w4 : width L D (chartY u L D) 4 = 2 * angleVec u 7 :=
    width_chartY u hD0 (⟨4, by omega⟩ : Fin 9)
  have w5 : width L D (chartY u L D) 5 = 2 * angleVec u 8 :=
    width_chartY u hD0 (⟨5, by omega⟩ : Fin 9)
  have w6 : width L D (chartY u L D) 6 = 2 * angleVec u 0 :=
    width_chartY u hD0 (⟨6, by omega⟩ : Fin 9)
  have w7 : width L D (chartY u L D) 7 = 2 * angleVec u 1 :=
    width_chartY u hD0 (⟨7, by omega⟩ : Fin 9)
  show circleMap (rawAnchorAngle u (FlashRootNetwork.rawOfRing j))
      = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) j)
  fin_cases j
  · show circleMap (rawAnchorAngle u 2)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 0)
    exact congrArg circleMap (by linarith [c0])
  · show circleMap (rawAnchorAngle u 3)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 1)
    exact congrArg circleMap (by linarith [s3, c0, c1, w0])
  · show circleMap (rawAnchorAngle u 4)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 2)
    exact congrArg circleMap (by linarith [s3, s4, c0, c1, c2, w0, w1])
  · show circleMap (rawAnchorAngle u 5)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 3)
    exact congrArg circleMap (by linarith [s3, s4, s5, c0, c1, c2, c3, w0, w1, w2])
  · show circleMap (rawAnchorAngle u 6)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 4)
    exact congrArg circleMap (by linarith [s3, s4, s5, s6, c0, c1, c2, c3, c4, w0, w1, w2, w3])
  · show circleMap (rawAnchorAngle u 7)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 5)
    exact congrArg circleMap
      (by linarith [s3, s4, s5, s6, s7, c0, c1, c2, c3, c4, c5, w0, w1, w2, w3, w4])
  · show circleMap (rawAnchorAngle u 8)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 6)
    exact congrArg circleMap
      (by linarith [s3, s4, s5, s6, s7, s8, c0, c1, c2, c3, c4, c5, c6, w0, w1, w2, w3, w4, w5])
  · show circleMap (rawAnchorAngle u 0)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 7)
    exact ((circleMap_add_two_pi (rawAnchorAngle u 0)).symm.trans (congrArg circleMap
      (by linarith [wr, s3, s4, s5, s6, s7, s8, c0, c1, c2, c3, c4, c5, c6, c7,
        w0, w1, w2, w3, w4, w5, w6])))
  · show circleMap (rawAnchorAngle u 1)
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) 8)
    exact ((circleMap_add_two_pi (rawAnchorAngle u 1)).symm.trans (congrArg circleMap
      (by linarith [wr, s1, s2, s3, s4, s5, s6, s7, s8, c0, c1, c2, c3, c4, c5, c6, c7, c8,
        w0, w1, w2, w3, w4, w5, w6, w7])))

/-- **The actual-chart identity** (obligations (a)+(b) closed over the already-proved core):
for `u` in the certificate box and the actual chart parameters, the chart point is a
nonnegative simplex point AND the canonical anchor network is the accumulated rotated
`circleMap` starting at raw angle `rawAnchorAngle u 2`. -/
theorem chart_identity (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    {L D : ℝ} (hL : L = 2 * Real.arcsin (19 / 50)) (hD : D = 9 * L - 2 * Real.pi) (j : Fin 9) :
    0 ≤ chartY u L D j ∧ ∑ i : Fin 9, chartY u L D i = 1 ∧
      FlashRootNetwork.canonAnchors u j
        = circleMap (rawAnchorAngle u 2 + anchorAngle L D (chartY u L D) j) := by
  have hD0 : D ≠ 0 := by
    intro h
    have h' : D = 9 * L - 2 * Real.pi := hD
    rw [h, hL] at h'
    exact absurd h'.symm (ne_of_gt D_pos)
  exact ⟨chartY_nonneg u hu hL hD j, chartY_sum_one u hD hD0,
    canonAnchors_eq_circleMap_chart u L D hD0 j⟩

end N11Formalization.FlashLeafRootChart

#print axioms N11Formalization.FlashLeafRootChart.sin_pi_div_nine_lt
#print axioms N11Formalization.FlashLeafRootChart.D_pos
#print axioms N11Formalization.FlashLeafRootChart.sum_shift3
#print axioms N11Formalization.FlashLeafRootChart.width_chartY
#print axioms N11Formalization.FlashLeafRootChart.chartY_sum_one
#print axioms N11Formalization.FlashLeafRootChart.angleVec_le_arcsin
#print axioms N11Formalization.FlashLeafRootChart.chartY_nonneg
#print axioms N11Formalization.FlashLeafRootChart.canonAnchors_eq_circleMap_chart
#print axioms N11Formalization.FlashLeafRootChart.chart_identity
