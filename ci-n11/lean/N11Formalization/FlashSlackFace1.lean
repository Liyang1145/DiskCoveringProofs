import N11Formalization.ResumeAttainmentAnnulusFace
import N11Formalization.NondegProof
import N11Formalization.RootRangeBoxFull

/-!
# FlashSlackFace1 —— 面 [0,1,H1] 的**盒级**距离供给（固定点 O0 路线；scope 已更正）

**消费者**：根内 `ResumeAttainment.tri_cover_pt_le`。

**目标**：对 `u ∈ InCertBox`，
`dist (ringCenter u 0) O0 ≤ u 6`、`dist (ringCenter u 1) O0 ≤ u 6`、`dist (hub1 u) O0 ≤ u 6`，
其中 `O0 = dO (-385882560178/10^12) (-295977251136/10^12)`。

**数值核**（`evidence/flash-slack/scope_fix.out.txt`）：盒心处三点到 `O0` 的距离**数值上接近**
（均在 `0.378831171` 同位附近；`O0` 取为该点附近的有理点，**不作精确外心/相等断言**），
`u 6 ≥ 0.379983852` ⇒ 中心级裕度 `~1.15e-3`；
按已证包络（`ndRingBox` / `u5` 盒）放大到整盒后裕度 `≥ 2.9e-4`（最紧 = hub 的 x 侧）。

**拆分建议（给 `-Build`）**：本件已把重活按定理隔离；若要进一步降单次运行时间，可把
§2（`nd_eval` 读数 + `*_coord_bounds`）切到独立模块 `FlashSlackFace1Coordinates`，
本件只 `import` 它并消费 `ring0_coord_bounds`/`ring1_coord_bounds`/`hub1_coord_bounds`
（三者结论只含坐标不等式）。**勿**把 `nd_eval` 与下面的装配放同一次 elaboration。

**经验口径（本工程新增）**：`norm_num` 在 **ℚ 侧**比较大分母（`2^82`）有理数会卡死
（实测 `((boxLoCert 5 : ℚ)) ≥ (-14943/10^5 : ℚ)` 型目标 > 7 min 不出）；**在 ℝ 侧**
写同一比较则 21 s 内出（`(-0.14943 : ℝ) ≤ ((boxLoCert 5 : ℚ) : ℝ)`）⇒ 一律只在 ℝ 侧比较。

**镜像面 [7,8,H1]**：`O0' = refl O0`；顶点是 `ringCenter u 1 / ringCenter u 0 / hub1 u`
关于 x 轴的镜像（根内 `rc7`/`rc6`/`hub_mirror1` + `dist_mirror`）⇒ 由本件三条直接转写。
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace N11Formalization.FlashSlackFace1

open N11Formalization

/-! ## 1. 通用引理、固定点、常数 -/

/-- 固定点 `O0 = (ox, oy)`。 -/
def dO (ox oy : ℚ) : Point := !₂[((ox : ℚ) : ℝ), ((oy : ℚ) : ℝ)]

theorem dO_ofLp_0 (ox oy : ℚ) : (dO ox oy).ofLp 0 = ((ox : ℚ) : ℝ) := rfl
theorem dO_ofLp_1 (ox oy : ℚ) : (dO ox oy).ofLp 1 = ((oy : ℚ) : ℝ) := rfl

/-- 面 [0,1,H1] 的固定点（取定的有理点；数值上接近盒心处三点的中心，**不作精确外心断言**）。 -/
def O0 : Point := dO (-385882560178 / 10 ^ 12) (-295977251136 / 10 ^ 12)

theorem O0_ofLp_0 : O0.ofLp 0 = (((-385882560178 : ℚ) / (10 : ℚ) ^ 12 : ℚ) : ℝ) := rfl
theorem O0_ofLp_1 : O0.ofLp 1 = (((-295977251136 : ℚ) / (10 : ℚ) ^ 12 : ℚ) : ℝ) := rfl

/-- **常数（独立 opaque 件）**：`boxLoCert 6` 的精确有理等式。消费者不必再 `norm_num` 整盒。 -/
theorem c6lo_eq : boxLoCert 6 = (1837489159457200081021291 : ℚ) / 2 ^ 82 := rfl
theorem c5lo_eq : boxLoCert 5 = (-722591886991921657599637 : ℚ) / 2 ^ 82 := rfl
theorem c5hi_eq : boxHiCert 5 = (-722591877320515100682603 : ℚ) / 2 ^ 82 := rfl

theorem c6lo_ge_mu : ((((1837489159457200081021291 : ℚ) / 2 ^ 82 : ℚ) : ℝ))
    ≥ (189991926 / 500000000 : ℝ) := by norm_num

/-- 一维夹逼：`z ∈ [c,d]` 且 `O` 到两端点距离 ≤ `A` ⇒ `O` 到 `z` 距离 ≤ `A`。 -/
theorem dist_le_of_mem_Icc {O z c d A : ℝ} (hz : c ≤ z ∧ z ≤ d)
    (hc : |O - c| ≤ A) (hd : |O - d| ≤ A) : |O - z| ≤ A := by
  have hmax : |O - z| ≤ max |O - c| |O - d| := by
    rw [abs_sub_le_iff]
    constructor
    · have h1 : O - c ≤ |O - c| := le_abs_self _
      have h2 : |O - c| ≤ max |O - c| |O - d| := le_max_left _ _
      linarith [hz.1]
    · have h1 : -(O - d) ≤ |O - d| := neg_le_abs _
      have h2 : |O - d| ≤ max |O - c| |O - d| := le_max_right _ _
      linarith [hz.2]
  exact le_trans hmax (max_le hc hd)

/-- 坐标偏差 ⇒ 距离上界。 -/
theorem dist_le_of_abs_sub_le_sq {x y : Point} {a b : ℝ}
    (hab : |x.ofLp 0 - y.ofLp 0| ≤ a) (hcd : |x.ofLp 1 - y.ofLp 1| ≤ b) :
    dist x y ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hd : dist x y ^ 2 = (x.ofLp 0 - y.ofLp 0) ^ 2 + (x.ofLp 1 - y.ofLp 1) ^ 2 :=
    ResumeAttainment.dist_sq_coord x y
  rw [← Real.sqrt_sq (dist_nonneg (x := x) (y := y))]
  apply Real.sqrt_le_sqrt
  rw [hd]
  nlinarith [abs_nonneg (x.ofLp 0 - y.ofLp 0), abs_nonneg (x.ofLp 1 - y.ofLp 1),
    sq_abs (x.ofLp 0 - y.ofLp 0), sq_abs (x.ofLp 1 - y.ofLp 1)]

/-- **距离核**：只消费四个坐标不等式 + 数值界。**不展开任何几何/区间定义。** -/
theorem dist_le_of_coord_bounds {P : Point} {xlo xhi ylo yhi A B D : ℝ}
    (hx : xlo ≤ P.ofLp 0 ∧ P.ofLp 0 ≤ xhi) (hy : ylo ≤ P.ofLp 1 ∧ P.ofLp 1 ≤ yhi)
    (hdx : |O0.ofLp 0 - xlo| ≤ A) (hdx' : |O0.ofLp 0 - xhi| ≤ A)
    (hdy : |O0.ofLp 1 - ylo| ≤ B) (hdy' : |O0.ofLp 1 - yhi| ≤ B)
    (hD : 0 ≤ D) (hsq : A ^ 2 + B ^ 2 ≤ D ^ 2) : dist P O0 ≤ D := by
  have hA : |P.ofLp 0 - O0.ofLp 0| ≤ A := by
    rw [abs_sub_comm]; exact dist_le_of_mem_Icc hx hdx hdx'
  have hB : |P.ofLp 1 - O0.ofLp 1| ≤ B := by
    rw [abs_sub_comm]; exact dist_le_of_mem_Icc hy hdy hdy'
  have h1 := dist_le_of_abs_sub_le_sq (x := P) (y := O0) hA hB
  have h2 : Real.sqrt (A ^ 2 + B ^ 2) ≤ D := by
    rw [show D = Real.sqrt (D ^ 2) from (Real.sqrt_sq hD).symm]
    exact Real.sqrt_le_sqrt hsq
  linarith

/-- `u 6` 的有理下界（消费独立的 `c6lo_ge_mu`，不 `norm_num` 整盒）。 -/
theorem le_u6 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    (189991926 / 500000000 : ℝ) ≤ u 6 := by
  have h6 := (hu 6).1
  rw [c6lo_eq] at h6
  exact le_trans c6lo_ge_mu h6

end N11Formalization.FlashSlackFace1

namespace N11Formalization.FlashSlackFace1

open N11Formalization N11Formalization.RootRangeBoxFull

/-! ## 2. 坐标数据（可整体切到 `FlashSlackFace1Coordinates` 模块） -/

theorem rb0_lo : ((-76471 : ℚ) / (10 : ℚ) ^ 5) ≤ (ndRingBox ndBox 0 0).lo := by nd_eval
theorem rb0_hi : (ndRingBox ndBox 0 0).hi ≤ ((-76470 : ℚ) / (10 : ℚ) ^ 5) := by nd_eval
theorem rb1_lo : ((-29838 : ℚ) / (10 : ℚ) ^ 5) ≤ (ndRingBox ndBox 0 1).lo := by nd_eval
theorem rb1_hi : (ndRingBox ndBox 0 1).hi ≤ ((-29836 : ℚ) / (10 : ℚ) ^ 5) := by nd_eval

theorem rc0_lo : ((-35579 : ℚ) / (10 : ℚ) ^ 5) ≤ (ndRingBox ndBox 1 0).lo := by nd_eval
theorem rc0_hi : (ndRingBox ndBox 1 0).hi ≤ ((-35578 : ℚ) / (10 : ℚ) ^ 5) := by nd_eval
theorem rc1_lo : ((-67362 : ℚ) / (10 : ℚ) ^ 5) ≤ (ndRingBox ndBox 1 1).lo := by nd_eval
theorem rc1_hi : (ndRingBox ndBox 1 1).hi ≤ ((-67361 : ℚ) / (10 : ℚ) ^ 5) := by nd_eval

theorem cast0x_lo : (((-76471 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.76471 : ℝ) := by norm_num
theorem cast0x_hi : (((-76470 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.76470 : ℝ) := by norm_num
theorem cast0y_lo : (((-29838 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.29838 : ℝ) := by norm_num
theorem cast0y_hi : (((-29836 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.29836 : ℝ) := by norm_num
theorem cast1x_lo : (((-35579 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.35579 : ℝ) := by norm_num
theorem cast1x_hi : (((-35578 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.35578 : ℝ) := by norm_num
theorem cast1y_lo : (((-67362 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.67362 : ℝ) := by norm_num
theorem cast1y_hi : (((-67361 : ℚ) / (10 : ℚ) ^ 5 : ℚ) : ℝ) = (-0.67361 : ℝ) := by norm_num

/-- `ringCenter u 0` 的四坐标不等式。 -/
theorem ring0_coord_bounds (u : Fin 12 → ℝ) (hu : InCertBox u) :
    (-0.76471 : ℝ) ≤ (ringCenter u 0).ofLp 0 ∧ (ringCenter u 0).ofLp 0 ≤ (-0.76470 : ℝ) ∧
    (-0.29838 : ℝ) ≤ (ringCenter u 0).ofLp 1 ∧ (ringCenter u 0).ofLp 1 ≤ (-0.29836 : ℝ) := by
  have hQ : ∀ i, (ndBox i).Mem (u i) := hQ u hu
  have h1 := RatInterval.mem_lo_le (ndRingBox_mem hQ 0 0)
  have h2 := RatInterval.mem_le_hi (ndRingBox_mem hQ 0 0)
  have h3 := RatInterval.mem_lo_le (ndRingBox_mem hQ 0 1)
  have h4 := RatInterval.mem_le_hi (ndRingBox_mem hQ 0 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cast0x_lo]; exact le_trans (Rat.cast_le.mpr rb0_lo) h1
  · rw [← cast0x_hi]; exact le_trans h2 (Rat.cast_le.mpr rb0_hi)
  · rw [← cast0y_lo]; exact le_trans (Rat.cast_le.mpr rb1_lo) h3
  · rw [← cast0y_hi]; exact le_trans h4 (Rat.cast_le.mpr rb1_hi)

/-- `ringCenter u 1` 的四坐标不等式。 -/
theorem ring1_coord_bounds (u : Fin 12 → ℝ) (hu : InCertBox u) :
    (-0.35579 : ℝ) ≤ (ringCenter u 1).ofLp 0 ∧ (ringCenter u 1).ofLp 0 ≤ (-0.35578 : ℝ) ∧
    (-0.67362 : ℝ) ≤ (ringCenter u 1).ofLp 1 ∧ (ringCenter u 1).ofLp 1 ≤ (-0.67361 : ℝ) := by
  have hQ : ∀ i, (ndBox i).Mem (u i) := hQ u hu
  have h1 := RatInterval.mem_lo_le (ndRingBox_mem hQ 1 0)
  have h2 := RatInterval.mem_le_hi (ndRingBox_mem hQ 1 0)
  have h3 := RatInterval.mem_lo_le (ndRingBox_mem hQ 1 1)
  have h4 := RatInterval.mem_le_hi (ndRingBox_mem hQ 1 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cast1x_lo]; exact le_trans (Rat.cast_le.mpr rc0_lo) h1
  · rw [← cast1x_hi]; exact le_trans h2 (Rat.cast_le.mpr rc0_hi)
  · rw [← cast1y_lo]; exact le_trans (Rat.cast_le.mpr rc1_lo) h3
  · rw [← cast1y_hi]; exact le_trans h4 (Rat.cast_le.mpr rc1_hi)

/-- `hub1 u` 的四坐标不等式（`hub1 = (u 5, 0)`，盒直接给，只在 ℝ 侧比较）。 -/
theorem hub1_coord_bounds (u : Fin 12 → ℝ) (hu : InCertBox u) :
    (-0.14943 : ℝ) ≤ (hub1 u).ofLp 0 ∧ (hub1 u).ofLp 0 ≤ (-0.14942 : ℝ) ∧
    (0 : ℝ) ≤ (hub1 u).ofLp 1 ∧ (hub1 u).ofLp 1 ≤ (0 : ℝ) := by
  have h5 := hu 5
  have hl : (-0.14943 : ℝ) ≤ (u 5 : ℝ) := by
    have h := h5.1
    rw [c5lo_eq] at h
    exact le_trans (by norm_num) h
  have hh : (u 5 : ℝ) ≤ (-0.14942 : ℝ) := by
    have h := h5.2
    rw [c5hi_eq] at h
    exact le_trans h (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hub1_coord0]; exact hl
  · rw [hub1_coord0]; exact hh
  · rw [hub1_coord1]
  · rw [hub1_coord1]

end N11Formalization.FlashSlackFace1

namespace N11Formalization.FlashSlackFace1

open N11Formalization N11Formalization.RootRangeBoxFull

/-! ## 3. 数值区间不等式（纯 ℝ 侧 `norm_num`；常数已按 lead 复核校正） -/

theorem num_ring0_x_lo : |O0.ofLp 0 - (-0.76471 : ℝ)| ≤ 0.3788275 := by
  rw [O0_ofLp_0]; norm_num
theorem num_ring0_x_hi : |O0.ofLp 0 - (-0.76470 : ℝ)| ≤ 0.3788275 := by
  rw [O0_ofLp_0]; norm_num
theorem num_ring0_y_lo : |O0.ofLp 1 - (-0.29838 : ℝ)| ≤ 0.0024028 := by
  rw [O0_ofLp_1]; norm_num
theorem num_ring0_y_hi : |O0.ofLp 1 - (-0.29836 : ℝ)| ≤ 0.0024028 := by
  rw [O0_ofLp_1]; norm_num
theorem num_ring0_sq : (0.3788275 : ℝ) ^ 2 + (0.0024028 : ℝ) ^ 2
    ≤ (189991926 / 500000000 : ℝ) ^ 2 := by norm_num

theorem num_ring1_x_lo : |O0.ofLp 0 - (-0.35579 : ℝ)| ≤ 0.03011 := by
  rw [O0_ofLp_0]; norm_num
theorem num_ring1_x_hi : |O0.ofLp 0 - (-0.35578 : ℝ)| ≤ 0.03011 := by
  rw [O0_ofLp_0]; norm_num
theorem num_ring1_y_lo : |O0.ofLp 1 - (-0.67362 : ℝ)| ≤ 0.37766 := by
  rw [O0_ofLp_1]; norm_num
theorem num_ring1_y_hi : |O0.ofLp 1 - (-0.67361 : ℝ)| ≤ 0.37766 := by
  rw [O0_ofLp_1]; norm_num
theorem num_ring1_sq : (0.03011 : ℝ) ^ 2 + (0.37766 : ℝ) ^ 2
    ≤ (189991926 / 500000000 : ℝ) ^ 2 := by norm_num

theorem num_hub_x_lo : |O0.ofLp 0 - (-0.14943 : ℝ)| ≤ 0.23647 := by
  rw [O0_ofLp_0]; norm_num
theorem num_hub_x_hi : |O0.ofLp 0 - (-0.14942 : ℝ)| ≤ 0.23647 := by
  rw [O0_ofLp_0]; norm_num
theorem num_hub_y : |O0.ofLp 1 - (0 : ℝ)| ≤ 0.29598 := by
  rw [O0_ofLp_1]; norm_num
theorem num_hub_sq : (0.23647 : ℝ) ^ 2 + (0.29598 : ℝ) ^ 2
    ≤ (189991926 / 500000000 : ℝ) ^ 2 := by norm_num

/-! ## 4. 装配 -/

theorem dist_ring0_le (u : Fin 12 → ℝ) (hu : InCertBox u) :
    dist (ringCenter u 0) O0 ≤ u 6 := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := ring0_coord_bounds u hu
  exact (dist_le_of_coord_bounds (P := ringCenter u 0) (xlo := -0.76471) (xhi := -0.76470)
    (ylo := -0.29838) (yhi := -0.29836) (A := 0.3788275) (B := 0.0024028)
    (D := 189991926 / 500000000) ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    num_ring0_x_lo num_ring0_x_hi num_ring0_y_lo num_ring0_y_hi
    (by norm_num) num_ring0_sq).trans (le_u6 u hu)

theorem dist_ring1_le (u : Fin 12 → ℝ) (hu : InCertBox u) :
    dist (ringCenter u 1) O0 ≤ u 6 := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := ring1_coord_bounds u hu
  exact (dist_le_of_coord_bounds (P := ringCenter u 1) (xlo := -0.35579) (xhi := -0.35578)
    (ylo := -0.67362) (yhi := -0.67361) (A := 0.03011) (B := 0.37766)
    (D := 189991926 / 500000000) ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    num_ring1_x_lo num_ring1_x_hi num_ring1_y_lo num_ring1_y_hi
    (by norm_num) num_ring1_sq).trans (le_u6 u hu)

theorem dist_hub1_le (u : Fin 12 → ℝ) (hu : InCertBox u) :
    dist (hub1 u) O0 ≤ u 6 := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hub1_coord_bounds u hu
  exact (dist_le_of_coord_bounds (P := hub1 u) (xlo := -0.14943) (xhi := -0.14942)
    (ylo := 0) (yhi := 0) (A := 0.23647) (B := 0.29598)
    (D := 189991926 / 500000000) ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    num_hub_x_lo num_hub_x_hi num_hub_y num_hub_y
    (by norm_num) num_hub_sq).trans (le_u6 u hu)

end N11Formalization.FlashSlackFace1


#print axioms N11Formalization.FlashSlackFace1.dist_ring0_le
#print axioms N11Formalization.FlashSlackFace1.dist_ring1_le
#print axioms N11Formalization.FlashSlackFace1.dist_hub1_le


