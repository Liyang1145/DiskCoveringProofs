/-
  evidence/f1-step2/F1-BallD35-C5.lean
  ====================================

  **F1 第 2 步 · 件 C 的第五片（`C5`）**：链式法则的 **`hub0`/`hub1` / `wPoint` / `dist` /
  残差节点** 升级为**一般点** —— **件 C 普查后的最后四层** ✓✓。

  **依据（整库普查）**：`hasFDerivAt_hub0_0/1`、`hasFDerivAt_hub1_0/1`、`hasFDerivAt_wPoint_0/1`、
  `hasFDerivAt_dist`、`fderiv_residualComp` **全部点冻结于 `u0`** ✗ ⇒ 本件只把 `u0 → z`、
  `Wp → WpAt z`、`u0 6 → z 6` 等**点相关字面量**换成一般点，**结构逐字不变** ✓。

  **依赖**：`N11Formalization.ResidualDerivDist`（`coord` 族/`Point`/`dist_point_eq_sqrt`/
  `pad12_four`/`five`/`six`/`hub0_coord0` 等）+ `ResidualDerivJT`（`Wfun`，用于 `wPoint` 的
  `sqrt` 侧前置口径对齐）。**零重推**：本件只写根内**没有**的一般点版 ✓。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.ResidualDerivDist
import N11Formalization.ResidualDerivJT

/-! ## 0. **外部名自查前言**（Lead R238 过程口径；逐条 `#check`） -/
#check @N11Formalization.coord
#check @N11Formalization.coord_apply_single
#check @N11Formalization.pad12_four
#check @N11Formalization.pad12_five
#check @N11Formalization.pad12_six
#check @N11Formalization.hub0
#check @N11Formalization.hub1
#check @N11Formalization.hub0_coord0
#check @N11Formalization.hub0_coord1
#check @N11Formalization.hub1_coord0
#check @N11Formalization.hub1_coord1
#check @N11Formalization.wPoint
#check @N11Formalization.wPoint_coord0
#check @N11Formalization.wPoint_coord1
#check @N11Formalization.dist_point_eq_sqrt
#check @N11Formalization.residualFun
#check @N11Formalization.Point
#check @N11Formalization.Uvec

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 1. `hub0`/`hub1` 在任意点（**与点无关**：坐标 0 是 `coord 4`/`coord 5`，坐标 1 恒 0） -/

theorem hasFDerivAt_hub0_0_any (z : Fin 7 → ℝ) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 0) (coord 4) z := by
  have h : (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 0) = fun w => w 4 := by
    funext w
    rw [hub0_coord0, pad12_four]
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := z)

theorem hasFDerivAt_hub0_1_any (z : Fin 7 → ℝ) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 1)
      (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) z := by
  have h : (fun w : Fin 7 → ℝ => (hub0 (pad12 w)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext w
    rw [hub0_coord1]
  rw [h]
  exact hasFDerivAt_const (0 : ℝ) z

theorem hasFDerivAt_hub1_0_any (z : Fin 7 → ℝ) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 0) (coord 5) z := by
  have h : (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 0) = fun w => w 5 := by
    funext w
    rw [hub1_coord0, pad12_five]
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := z)

theorem hasFDerivAt_hub1_1_any (z : Fin 7 → ℝ) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 1)
      (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) z := by
  have h : (fun w : Fin 7 → ℝ => (hub1 (pad12 w)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext w
    rw [hub1_coord1]
  rw [h]
  exact hasFDerivAt_const (0 : ℝ) z

/-! ## 2. `wPoint` 两坐标在任意点（镜像 `hasFDerivAt_wPoint_0/1`，`Wp → WpAt z`） -/

/-- `wPoint` 坐标 1 的 radicand 在**任意点**（= 盒心处 `Wp`）。 -/
def WpAt (z : Fin 7 → ℝ) : ℝ := (z 6) ^ 2 - ((z 5 - z 4) / 2) ^ 2

theorem hasFDerivAt_wPoint_0_any (z : Fin 7 → ℝ) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0)
      ((1 / 2 : ℝ) • (coord 4 + coord 5)) z := by
  have h : (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 0)
      = fun w => (1 / 2 : ℝ) * (w 4 + w 5) := by
    funext w
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  rw [h]
  have h45 : HasFDerivAt (fun w : Fin 7 → ℝ => w 4 + w 5) (coord 4 + coord 5) z :=
    (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := z)).add
      (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := z))
  exact h45.const_mul (1 / 2)

theorem hasFDerivAt_wPoint_1_any (z : Fin 7 → ℝ) (hWp : WpAt z ≠ 0) :
    HasFDerivAt (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1)
      ((1 / (2 * Real.sqrt (WpAt z))) • ((2 * z 6) • coord 6
        - (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) z := by
  have h6 : HasFDerivAt (fun w : Fin 7 → ℝ => w 6) (coord 6) z :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := z)
  have h6sq : HasFDerivAt (fun w : Fin 7 → ℝ => (w 6) ^ 2) ((2 * z 6) • coord 6) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h6.pow 2
  have h54 : HasFDerivAt (fun w : Fin 7 → ℝ => w 5 - w 4) (coord 5 - coord 4) z :=
    (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := z)).sub
      (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := z))
  have hhalf : HasFDerivAt (fun w : Fin 7 → ℝ => (w 5 - w 4) / 2)
      ((1 / 2 : ℝ) • (coord 5 - coord 4)) z := by
    have he : (fun w : Fin 7 → ℝ => (w 5 - w 4) / 2)
        = fun w => (1 / 2 : ℝ) * (w 5 - w 4) := by
      funext w
      ring
    rw [he]
    exact h54.const_mul (1 / 2)
  have hhalf2 : HasFDerivAt (fun w : Fin 7 → ℝ => ((w 5 - w 4) / 2) ^ 2)
      ((2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hhalf.pow 2
  have hrad : HasFDerivAt (fun w : Fin 7 → ℝ => (w 6) ^ 2 - ((w 5 - w 4) / 2) ^ 2)
      ((2 * z 6) • coord 6
        - (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) z :=
    h6sq.sub hhalf2
  have hfun : (fun w : Fin 7 → ℝ => (wPoint (pad12 w)).ofLp 1)
      = fun w => Real.sqrt ((w 6) ^ 2 - ((w 5 - w 4) / 2) ^ 2) := by
    funext w
    rw [wPoint_coord1, pad12_six, pad12_five, pad12_four]
  rw [hfun]
  exact hrad.sqrt (by simpa [WpAt] using hWp)

/-! ## 3. `dist (P w) (Q w)` 链式在任意点（镜像 `hasFDerivAt_dist`，`u0 → z`） -/

theorem hasFDerivAt_dist_any
    (z : Fin 7 → ℝ)
    (Px Py Qx Qy : (Fin 7 → ℝ) → ℝ)
    (Px' Py' Qx' Qy' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hPx : HasFDerivAt Px Px' z) (hPy : HasFDerivAt Py Py' z)
    (hQx : HasFDerivAt Qx Qx' z) (hQy : HasFDerivAt Qy Qy' z)
    (hg : (Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2 ≠ 0) :
    HasFDerivAt (fun w : Fin 7 → ℝ => Real.sqrt ((Px w - Qx w) ^ 2 + (Py w - Qy w) ^ 2))
      ((1 / (2 * Real.sqrt ((Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2)))
        • ((2 * (Px z - Qx z)) • (Px' - Qx') + (2 * (Py z - Qy z)) • (Py' - Qy'))) z := by
  have hX : HasFDerivAt (fun w : Fin 7 → ℝ => Px w - Qx w) (Px' - Qx') z := hPx.sub hQx
  have hY : HasFDerivAt (fun w : Fin 7 → ℝ => Py w - Qy w) (Py' - Qy') z := hPy.sub hQy
  have hx2 : HasFDerivAt (fun w : Fin 7 → ℝ => (Px w - Qx w) ^ 2)
      ((2 * (Px z - Qx z)) • (Px' - Qx')) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hX.pow 2
  have hy2 : HasFDerivAt (fun w : Fin 7 → ℝ => (Py w - Qy w) ^ 2)
      ((2 * (Py z - Qy z)) • (Py' - Qy')) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hY.pow 2
  exact (hx2.add hy2).sqrt hg

theorem fderiv_dist_any_single
    (z : Fin 7 → ℝ)
    (Px Py Qx Qy : (Fin 7 → ℝ) → ℝ)
    (Px' Py' Qx' Qy' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hPx : HasFDerivAt Px Px' z) (hPy : HasFDerivAt Py Py' z)
    (hQx : HasFDerivAt Qx Qx' z) (hQy : HasFDerivAt Qy Qy' z)
    (hg : (Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2 ≠ 0) (i : Fin 7) :
    (fderiv ℝ (fun w : Fin 7 → ℝ =>
        Real.sqrt ((Px w - Qx w) ^ 2 + (Py w - Qy w) ^ 2)) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt ((Px z - Qx z) ^ 2 + (Py z - Qy z) ^ 2)))
          * (2 * (Px z - Qx z) * (Px' (Pi.single i 1) - Qx' (Pi.single i 1))
            + 2 * (Py z - Qy z) * (Py' (Pi.single i 1) - Qy' (Pi.single i 1))) := by
  rw [(hasFDerivAt_dist_any z Px Py Qx Qy Px' Py' Qx' Qy' hPx hPy hQx hQy hg).fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]

/-! ## 4. 一般点的残差节点（镜像 `fderiv_residualComp`） -/

theorem fderiv_residualComp_any
    (k : Fin 5) (z : Fin 7 → ℝ) (A B : (Fin 12 → ℝ) → Point)
    (A0' A1' B0' B1' : (Fin 7 → ℝ) →L[ℝ] ℝ)
    (hA0 : HasFDerivAt (fun w : Fin 7 → ℝ => (A (pad12 w)).ofLp 0) A0' z)
    (hA1 : HasFDerivAt (fun w : Fin 7 → ℝ => (A (pad12 w)).ofLp 1) A1' z)
    (hB0 : HasFDerivAt (fun w : Fin 7 → ℝ => (B (pad12 w)).ofLp 0) B0' z)
    (hB1 : HasFDerivAt (fun w : Fin 7 → ℝ => (B (pad12 w)).ofLp 1) B1' z)
    (hfun : ∀ w : Fin 7 → ℝ, residualFun w k = dist (A (pad12 w)) (B (pad12 w)) - w 6)
    (hg : ((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0) ^ 2
        + ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1) ^ 2 ≠ 0)
    (i : Fin 7) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w k) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0) ^ 2
              + ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0)
              * (A0' (Pi.single i 1) - B0' (Pi.single i 1))
            + 2 * ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1)
              * (A1' (Pi.single i 1) - B1' (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) := by
  have hd := hasFDerivAt_dist_any z
    (fun w : Fin 7 → ℝ => (A (pad12 w)).ofLp 0) (fun w : Fin 7 → ℝ => (A (pad12 w)).ofLp 1)
    (fun w : Fin 7 → ℝ => (B (pad12 w)).ofLp 0) (fun w : Fin 7 → ℝ => (B (pad12 w)).ofLp 1)
    A0' A1' B0' B1' hA0 hA1 hB0 hB1 hg
  have hz : HasFDerivAt (fun w : Fin 7 → ℝ => w 6) (coord 6) z :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := z)
  have htot : HasFDerivAt (fun w : Fin 7 → ℝ =>
      Real.sqrt (((A (pad12 w)).ofLp 0 - (B (pad12 w)).ofLp 0) ^ 2
        + ((A (pad12 w)).ofLp 1 - (B (pad12 w)).ofLp 1) ^ 2) - w 6)
      (((1 / (2 * Real.sqrt (((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0) ^ 2
              + ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1) ^ 2)))
          • ((2 * ((A (pad12 z)).ofLp 0 - (B (pad12 z)).ofLp 0)) • (A0' - B0')
            + (2 * ((A (pad12 z)).ofLp 1 - (B (pad12 z)).ofLp 1)) • (A1' - B1')))
        - coord 6) z :=
    hd.sub hz
  have hEq : (fun w : Fin 7 → ℝ => residualFun w k)
      = fun w : Fin 7 → ℝ => Real.sqrt (((A (pad12 w)).ofLp 0 - (B (pad12 w)).ofLp 0) ^ 2
          + ((A (pad12 w)).ofLp 1 - (B (pad12 w)).ofLp 1) ^ 2) - w 6 := by
    funext w
    rw [hfun w, dist_point_eq_sqrt]
  rw [hEq, htot.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, coord_six_apply_single i]

end N11Formalization

#print axioms N11Formalization.hasFDerivAt_hub0_0_any
#print axioms N11Formalization.hasFDerivAt_hub1_1_any
#print axioms N11Formalization.hasFDerivAt_wPoint_1_any
#print axioms N11Formalization.hasFDerivAt_dist_any
#print axioms N11Formalization.fderiv_dist_any_single
#print axioms N11Formalization.fderiv_residualComp_any
