/-
n11-formalization —— **`ActualSigns` 的 25 条 hub/chord 符号**（flash-boundary-caps 分区）。

写域：本文件（先 evidence/，核通后**原字节**进 src 为 `flash-boundary-caps` 新件；**不覆盖**任何已核件）。

## 0. 目标（lead R-FBC-23/24 分区）

我负责 `FlashAttainmentFinal.ActualSigns` 的：
* `hh0 : ∀ i : Fin 9, 0 ≤ phi (ringCenter u) succ9 i (hub0 u)`（9 条）
* `hh1 : ∀ i : Fin 9, 0 ≤ phi (ringCenter u) succ9 i (hub1 u)`（9 条）
* `hchordA : ∀ j, (j=3 ∨ j=4 ∨ j=5) → 0 < orient (ringCenter u 6) (ringCenter u 2) (ringCenter u j)`（3 条）
* `hchordB : ∀ j, (j=7 ∨ j=8 ∨ j=0 ∨ j=1) → 0 < orient (ringCenter u 2) (ringCenter u 6) (ringCenter u j)`（4 条）
（合计 25；63 条 `RingConvex` 归 flash-slack-faces。）

## 1. 口径

* 定义（只读，tiling 写域）：`orient a b c = det2 (b-a) (c-a)`、`det2 u v = u₀v₁ - u₁v₀`（`FlashTilingCore`）；
  `phi q s i x = orient (q i) (q (s i)) x`（`FlashTilingFan`），`succ9 i = i + 1`。
* **复用 slack 的近似定向引理** `FlashTilingSigns.orient_pos_of_approx`（其单例 `FlashTilingSignsInst.lean`
  已 green `FA9FFC1A`）：6 条坐标误差 ≤ R + 4 条近似点量级 ≤ U + `hM : 4R(U+2R)+4UR < orient A0 B0 D0` ⇒ `0 < orient A B D`。
* **坐标误差前件**（lead 指示：shared coords 未到先用它完成 25 条）：
  `hcoord : ∀ k c, |(ringCenter u k).ofLp c - (Cp k c)| ≤ 1/10000`（近似点取自 `evidence/flash-slack/sign_data2.py`，
  |真值 − 点| ≤ 1e-6）；hub 同理 `|(hub0 u).ofLp 0 - 272977/10^6| ≤ 1/10000 ∧ (hub0 u).ofLp 1 = 0`。
* **裕度已核（`evidence/flash-caps/margins-25.py` / `.out.txt`）**：25 条的近似行列式
  M ∈ [0.3078, 1.1938]，阈值（R=1e-4, U=2）≈ 1.6e-3 ⇒ **全部安全**（最小 M ≈ 0.3078 ≫ 1.6e-3）。
* 无浮点、无 `sorry`、无自定义 axiom（只用 slack/工程的已证引理 + `norm_num`）。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.FlashTilingFan
import N11Formalization.FlashTilingSigns
import N11Formalization.FlashTilingCoordBounds
import N11Formalization.FlashTilingRingConvex
import N11Formalization.RootRangeBoxFull
import N11Formalization.FlashAttainmentFinal

set_option linter.unusedVariables false

noncomputable section

namespace N11Formalization.FlashTilingHubChordSigns

open N11Formalization
open N11Formalization.FlashTiling
open N11Formalization.FlashTilingSigns

/-! ## §1 9 个环心与 2 个 hub 的十进制近似点（取自 `sign_data2.py`） -/

def C0p : Point := !₂[(-764706 / 10 ^ 6 : ℝ), (-298370 / 10 ^ 6 : ℝ)]
def C1p : Point := !₂[(-355787 / 10 ^ 6 : ℝ), (-673611 / 10 ^ 6 : ℝ)]
def C2p : Point := !₂[( 94837 / 10 ^ 6 : ℝ), (-694424 / 10 ^ 6 : ℝ)]
def C3p : Point := !₂[(615812 / 10 ^ 6 : ℝ), (-598609 / 10 ^ 6 : ℝ)]
def C4p : Point := !₂[(892522 / 10 ^ 6 : ℝ), (      0 : ℝ)]
def C5p : Point := !₂[(615812 / 10 ^ 6 : ℝ), ( 598609 / 10 ^ 6 : ℝ)]
def C6p : Point := !₂[( 94837 / 10 ^ 6 : ℝ), ( 694424 / 10 ^ 6 : ℝ)]
def C7p : Point := !₂[(-355787 / 10 ^ 6 : ℝ), ( 673611 / 10 ^ 6 : ℝ)]
def C8p : Point := !₂[(-764706 / 10 ^ 6 : ℝ), ( 298370 / 10 ^ 6 : ℝ)]
def H0p : Point := !₂[(272977 / 10 ^ 6 : ℝ), (0 : ℝ)]
def H1p : Point := !₂[(-149428 / 10 ^ 6 : ℝ), (0 : ℝ)]

theorem C0p_0 : C0p.ofLp 0 = (-764706 / 10 ^ 6 : ℝ) := rfl
theorem C0p_1 : C0p.ofLp 1 = (-298370 / 10 ^ 6 : ℝ) := rfl
theorem C1p_0 : C1p.ofLp 0 = (-355787 / 10 ^ 6 : ℝ) := rfl
theorem C1p_1 : C1p.ofLp 1 = (-673611 / 10 ^ 6 : ℝ) := rfl
theorem C2p_0 : C2p.ofLp 0 = (94837 / 10 ^ 6 : ℝ) := rfl
theorem C2p_1 : C2p.ofLp 1 = (-694424 / 10 ^ 6 : ℝ) := rfl
theorem C3p_0 : C3p.ofLp 0 = (615812 / 10 ^ 6 : ℝ) := rfl
theorem C3p_1 : C3p.ofLp 1 = (-598609 / 10 ^ 6 : ℝ) := rfl
theorem C4p_0 : C4p.ofLp 0 = (892522 / 10 ^ 6 : ℝ) := rfl
theorem C4p_1 : C4p.ofLp 1 = (0 : ℝ) := rfl
theorem C5p_0 : C5p.ofLp 0 = (615812 / 10 ^ 6 : ℝ) := rfl
theorem C5p_1 : C5p.ofLp 1 = (598609 / 10 ^ 6 : ℝ) := rfl
theorem C6p_0 : C6p.ofLp 0 = (94837 / 10 ^ 6 : ℝ) := rfl
theorem C6p_1 : C6p.ofLp 1 = (694424 / 10 ^ 6 : ℝ) := rfl
theorem C7p_0 : C7p.ofLp 0 = (-355787 / 10 ^ 6 : ℝ) := rfl
theorem C7p_1 : C7p.ofLp 1 = (673611 / 10 ^ 6 : ℝ) := rfl
theorem C8p_0 : C8p.ofLp 0 = (-764706 / 10 ^ 6 : ℝ) := rfl
theorem C8p_1 : C8p.ofLp 1 = (298370 / 10 ^ 6 : ℝ) := rfl
theorem H0p_0 : H0p.ofLp 0 = (272977 / 10 ^ 6 : ℝ) := rfl
theorem H0p_1 : H0p.ofLp 1 = (0 : ℝ) := rfl
theorem H1p_0 : H1p.ofLp 0 = (-149428 / 10 ^ 6 : ℝ) := rfl
theorem H1p_1 : H1p.ofLp 1 = (0 : ℝ) := rfl

/-! ## §2 坐标误差事实（**共享 11 条**，不重复 36 个读数）

每条：由 `ringCoord u hu k`（四个访问子）与 `rd{k}{x,y}_{lo,hi}`（slack 件里的十进制端点）
经 `Rat.cast_le.mpr` + `le_trans` 得 `(ℝ) 区间`，再与近似点比 `≤ 1/10000`。
（cast 注意：`norm_num at h ⊢` 归约两侧；只用 `norm_num only at h` 会因 goal 未归约而 fail —— slack 踩过。） -/

theorem err_ring_0 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 0).ofLp 0 - C0p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 0).ofLp 1 - C0p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 0
  have a1 := le_trans (Rat.cast_le.mpr rd0x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd0x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd0y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd0y_hi)
  constructor
  · rw [abs_sub_le_iff, C0p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C0p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_1 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 1).ofLp 0 - C1p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 1).ofLp 1 - C1p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 1
  have a1 := le_trans (Rat.cast_le.mpr rd1x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd1x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd1y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd1y_hi)
  constructor
  · rw [abs_sub_le_iff, C1p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C1p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_2 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 2).ofLp 0 - C2p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 2).ofLp 1 - C2p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 2
  have a1 := le_trans (Rat.cast_le.mpr rd2x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd2x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd2y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd2y_hi)
  constructor
  · rw [abs_sub_le_iff, C2p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C2p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_3 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 3).ofLp 0 - C3p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 3).ofLp 1 - C3p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 3
  have a1 := le_trans (Rat.cast_le.mpr rd3x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd3x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd3y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd3y_hi)
  constructor
  · rw [abs_sub_le_iff, C3p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C3p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_4 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 4).ofLp 0 - C4p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 4).ofLp 1 - C4p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 4
  have a1 := le_trans (Rat.cast_le.mpr rd4x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd4x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd4y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd4y_hi)
  constructor
  · rw [abs_sub_le_iff, C4p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C4p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_5 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 5).ofLp 0 - C5p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 5).ofLp 1 - C5p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 5
  have a1 := le_trans (Rat.cast_le.mpr rd5x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd5x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd5y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd5y_hi)
  constructor
  · rw [abs_sub_le_iff, C5p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C5p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_6 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 6).ofLp 0 - C6p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 6).ofLp 1 - C6p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 6
  have a1 := le_trans (Rat.cast_le.mpr rd6x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd6x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd6y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd6y_hi)
  constructor
  · rw [abs_sub_le_iff, C6p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C6p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_7 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 7).ofLp 0 - C7p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 7).ofLp 1 - C7p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 7
  have a1 := le_trans (Rat.cast_le.mpr rd7x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd7x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd7y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd7y_hi)
  constructor
  · rw [abs_sub_le_iff, C7p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C7p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

theorem err_ring_8 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(ringCenter u 8).ofLp 0 - C8p.ofLp 0| ≤ 1 / 10000 ∧
      |(ringCenter u 8).ofLp 1 - C8p.ofLp 1| ≤ 1 / 10000 := by
  have h := ringCoord u hu 8
  have a1 := le_trans (Rat.cast_le.mpr rd8x_lo) h.1
  have a2 := le_trans h.2.1 (Rat.cast_le.mpr rd8x_hi)
  have b1 := le_trans (Rat.cast_le.mpr rd8y_lo) h.2.2.1
  have b2 := le_trans h.2.2.2 (Rat.cast_le.mpr rd8y_hi)
  constructor
  · rw [abs_sub_le_iff, C8p_0]; constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, C8p_1]; constructor <;> (norm_num at b1 b2 ⊢; linarith)

/-- hub0 = `(u 4, 0)`：界直接取 `InCertBox`（`boxLoCert 4 = 1320038024120705549412715/2^82`、
`boxHiCert 4 = 1320038033792112106329749/2^82`，两端均 ≈ 0.27297746）。 -/
theorem err_hub0 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(hub0 u).ofLp 0 - H0p.ofLp 0| ≤ 1 / 10000 ∧
      |(hub0 u).ofLp 1 - H0p.ofLp 1| ≤ 1 / 10000 := by
  have h4 := hu 4
  rw [show boxLoCert 4 = (1320038024120705549412715 : ℚ) / 2 ^ 82 from rfl,
    show boxHiCert 4 = (1320038033792112106329749 : ℚ) / 2 ^ 82 from rfl] at h4
  have a1 : ((1320038024120705549412715 : ℝ) / 2 ^ 82) ≤ u 4 := by
    have := h4.1; push_cast at this; exact this
  have a2 : u 4 ≤ ((1320038033792112106329749 : ℝ) / 2 ^ 82) := by
    have := h4.2; push_cast at this; exact this
  constructor
  · rw [abs_sub_le_iff, hub0, H0p_0]
    constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, hub0, H0p_1]
    constructor <;> norm_num

/-- hub1 = `(u 5, 0)`：`boxLoCert 5 = -722591886991921657599637/2^82`、
`boxHiCert 5 = -722591877320515100682603/2^82`。 -/
theorem err_hub1 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    |(hub1 u).ofLp 0 - H1p.ofLp 0| ≤ 1 / 10000 ∧
      |(hub1 u).ofLp 1 - H1p.ofLp 1| ≤ 1 / 10000 := by
  have h5 := hu 5
  rw [show boxLoCert 5 = (-722591886991921657599637 : ℚ) / 2 ^ 82 from rfl,
    show boxHiCert 5 = (-722591877320515100682603 : ℚ) / 2 ^ 82 from rfl] at h5
  have a1 : ((-722591886991921657599637 : ℝ) / 2 ^ 82) ≤ u 5 := by
    have := h5.1; push_cast at this; exact this
  have a2 : u 5 ≤ ((-722591877320515100682603 : ℝ) / 2 ^ 82) := by
    have := h5.2; push_cast at this; exact this
  constructor
  · rw [abs_sub_le_iff, hub1, H1p_0]
    constructor <;> (norm_num at a1 a2 ⊢; linarith)
  · rw [abs_sub_le_iff, hub1, H1p_1]
    constructor <;> norm_num

/-! ## §3 25 条符号的**算术核**：`4R(U+2R)+4UR < orient A0 B0 D0`（R = 1e-4，U = 2） -/

/-- 统一阈值（R = 1/10000, U = 2）：`4R(U+2R) + 4UR = 0.00160008`。 -/
theorem threshold_value :
    4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000) = (0.00160008 : ℝ) := by
  norm_num

-- chord A：j ∈ {3,4,5}，`orient (C6) (C2) (Cj)`
theorem hM_chordA_3 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C6p C2p C3p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C6p, C2p, C3p]
theorem hM_chordA_4 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C6p C2p C4p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C6p, C2p, C4p]
theorem hM_chordA_5 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C6p C2p C5p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C6p, C2p, C5p]

-- chord B：j ∈ {7,8,0,1}，`orient (C2) (C6) (Cj)`
theorem hM_chordB_7 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C6p C7p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C6p, C7p]
theorem hM_chordB_8 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C6p C8p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C6p, C8p]
theorem hM_chordB_0 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C6p C0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C6p, C0p]
theorem hM_chordB_1 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C6p C1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C6p, C1p]

-- hh0：i = 0..8，`orient (C_i) (C_{i+1 mod 9}) (H0)`
theorem hM_hh0_0 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C0p C1p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C0p, C1p, H0p]
theorem hM_hh0_1 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C1p C2p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C1p, C2p, H0p]
theorem hM_hh0_2 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C3p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C3p, H0p]
theorem hM_hh0_3 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C3p C4p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C3p, C4p, H0p]
theorem hM_hh0_4 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C4p C5p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C4p, C5p, H0p]
theorem hM_hh0_5 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C5p C6p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C5p, C6p, H0p]
theorem hM_hh0_6 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C6p C7p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C6p, C7p, H0p]
theorem hM_hh0_7 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C7p C8p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C7p, C8p, H0p]
theorem hM_hh0_8 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C8p C0p H0p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C8p, C0p, H0p]

-- hh1：i = 0..8，`orient (C_i) (C_{i+1 mod 9}) (H1)`
theorem hM_hh1_0 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C0p C1p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C0p, C1p, H1p]
theorem hM_hh1_1 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C1p C2p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C1p, C2p, H1p]
theorem hM_hh1_2 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C2p C3p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C2p, C3p, H1p]
theorem hM_hh1_3 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C3p C4p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C3p, C4p, H1p]
theorem hM_hh1_4 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C4p C5p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C4p, C5p, H1p]
theorem hM_hh1_5 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C5p C6p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C5p, C6p, H1p]
theorem hM_hh1_6 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C6p C7p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C6p, C7p, H1p]
theorem hM_hh1_7 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C7p C8p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C7p, C8p, H1p]
theorem hM_hh1_8 : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
    < FlashTiling.orient C8p C0p H1p := by
  norm_num [FlashTiling.orient, FlashTiling.det2, C8p, C0p, H1p]

/-! ## §4 25 条 actual 符号（`orient_pos_of_approx` + §2 误差 + §3 算术核） -/

-- chord A：`0 < orient (C6) (C2) (Cj)`，j = 3,4,5
theorem chordA_3 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 2) (ringCenter u 3) :=
  orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 2) (D := ringCenter u 3)
    (A0 := C6p) (B0 := C2p) (D0 := C3p) (R := 1 / 10000) (U := 2)
    (err_ring_6 u hu).1 (err_ring_6 u hu).2 (err_ring_2 u hu).1 (err_ring_2 u hu).2
    (err_ring_3 u hu).1 (err_ring_3 u hu).2
    (by norm_num [C6p, C2p]) (by norm_num [C6p, C2p])
    (by norm_num [C6p, C3p]) (by norm_num [C6p, C3p])
    (by norm_num) (by norm_num) hM_chordA_3

theorem chordA_4 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 2) (ringCenter u 4) :=
  orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 2) (D := ringCenter u 4)
    (A0 := C6p) (B0 := C2p) (D0 := C4p) (R := 1 / 10000) (U := 2)
    (err_ring_6 u hu).1 (err_ring_6 u hu).2 (err_ring_2 u hu).1 (err_ring_2 u hu).2
    (err_ring_4 u hu).1 (err_ring_4 u hu).2
    (by norm_num [C6p, C2p]) (by norm_num [C6p, C2p])
    (by norm_num [C6p, C4p]) (by norm_num [C6p, C4p])
    (by norm_num) (by norm_num) hM_chordA_4

theorem chordA_5 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 2) (ringCenter u 5) :=
  orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 2) (D := ringCenter u 5)
    (A0 := C6p) (B0 := C2p) (D0 := C5p) (R := 1 / 10000) (U := 2)
    (err_ring_6 u hu).1 (err_ring_6 u hu).2 (err_ring_2 u hu).1 (err_ring_2 u hu).2
    (err_ring_5 u hu).1 (err_ring_5 u hu).2
    (by norm_num [C6p, C2p]) (by norm_num [C6p, C2p])
    (by norm_num [C6p, C5p]) (by norm_num [C6p, C5p])
    (by norm_num) (by norm_num) hM_chordA_5

-- chord B：`0 < orient (C2) (C6) (Cj)`，j = 7,8,0,1
theorem chordB_7 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u 7) :=
  orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 6) (D := ringCenter u 7)
    (A0 := C2p) (B0 := C6p) (D0 := C7p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_ring_7 u hu).1 (err_ring_7 u hu).2
    (by norm_num [C2p, C6p]) (by norm_num [C2p, C6p])
    (by norm_num [C2p, C7p]) (by norm_num [C2p, C7p])
    (by norm_num) (by norm_num) hM_chordB_7

theorem chordB_8 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u 8) :=
  orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 6) (D := ringCenter u 8)
    (A0 := C2p) (B0 := C6p) (D0 := C8p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_ring_8 u hu).1 (err_ring_8 u hu).2
    (by norm_num [C2p, C6p]) (by norm_num [C2p, C6p])
    (by norm_num [C2p, C8p]) (by norm_num [C2p, C8p])
    (by norm_num) (by norm_num) hM_chordB_8

theorem chordB_0 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u 0) :=
  orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 6) (D := ringCenter u 0)
    (A0 := C2p) (B0 := C6p) (D0 := C0p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_ring_0 u hu).1 (err_ring_0 u hu).2
    (by norm_num [C2p, C6p]) (by norm_num [C2p, C6p])
    (by norm_num [C2p, C0p]) (by norm_num [C2p, C0p])
    (by norm_num) (by norm_num) hM_chordB_0

theorem chordB_1 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u 1) :=
  orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 6) (D := ringCenter u 1)
    (A0 := C2p) (B0 := C6p) (D0 := C1p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_ring_1 u hu).1 (err_ring_1 u hu).2
    (by norm_num [C2p, C6p]) (by norm_num [C2p, C6p])
    (by norm_num [C2p, C1p]) (by norm_num [C2p, C1p])
    (by norm_num) (by norm_num) hM_chordB_1

-- hh0：`0 ≤ phi (ringCenter u) succ9 i (hub0 u)`，i = 0..8（succ9 8 = 0）
theorem hh0_0 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (0 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u ⟨1, by norm_num⟩)
    (D := hub0 u) (A0 := C0p) (B0 := C1p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_0 u hu).1 (err_ring_0 u hu).2 (err_ring_1 u hu).1 (err_ring_1 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C0p, C1p]) (by norm_num [C0p, C1p])
    (by norm_num [C0p, H0p]) (by norm_num [C0p, H0p])
    (by norm_num) (by norm_num) hM_hh0_0
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_1 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (1 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u ⟨2, by norm_num⟩)
    (D := hub0 u) (A0 := C1p) (B0 := C2p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_1 u hu).1 (err_ring_1 u hu).2 (err_ring_2 u hu).1 (err_ring_2 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C1p, C2p]) (by norm_num [C1p, C2p])
    (by norm_num [C1p, H0p]) (by norm_num [C1p, H0p])
    (by norm_num) (by norm_num) hM_hh0_1
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_8 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (8 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0)
    (D := hub0 u) (A0 := C8p) (B0 := C0p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_8 u hu).1 (err_ring_8 u hu).2 (err_ring_0 u hu).1 (err_ring_0 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C8p, C0p]) (by norm_num [C8p, C0p])
    (by norm_num [C8p, H0p]) (by norm_num [C8p, H0p])
    (by norm_num) (by norm_num) hM_hh0_8
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_2 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (2 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u ⟨3, by norm_num⟩)
    (D := hub0 u) (A0 := C2p) (B0 := C3p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_3 u hu).1 (err_ring_3 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C2p, C3p]) (by norm_num [C2p, C3p])
    (by norm_num [C2p, H0p]) (by norm_num [C2p, H0p])
    (by norm_num) (by norm_num) hM_hh0_2
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_3 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (3 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u ⟨4, by norm_num⟩)
    (D := hub0 u) (A0 := C3p) (B0 := C4p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_3 u hu).1 (err_ring_3 u hu).2 (err_ring_4 u hu).1 (err_ring_4 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C3p, C4p]) (by norm_num [C3p, C4p])
    (by norm_num [C3p, H0p]) (by norm_num [C3p, H0p])
    (by norm_num) (by norm_num) hM_hh0_3
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_4 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (4 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u ⟨5, by norm_num⟩)
    (D := hub0 u) (A0 := C4p) (B0 := C5p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_4 u hu).1 (err_ring_4 u hu).2 (err_ring_5 u hu).1 (err_ring_5 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C4p, C5p]) (by norm_num [C4p, C5p])
    (by norm_num [C4p, H0p]) (by norm_num [C4p, H0p])
    (by norm_num) (by norm_num) hM_hh0_4
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_5 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (5 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u ⟨6, by norm_num⟩)
    (D := hub0 u) (A0 := C5p) (B0 := C6p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_5 u hu).1 (err_ring_5 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C5p, C6p]) (by norm_num [C5p, C6p])
    (by norm_num [C5p, H0p]) (by norm_num [C5p, H0p])
    (by norm_num) (by norm_num) hM_hh0_5
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_6 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (6 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u ⟨7, by norm_num⟩)
    (D := hub0 u) (A0 := C6p) (B0 := C7p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_6 u hu).1 (err_ring_6 u hu).2 (err_ring_7 u hu).1 (err_ring_7 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C6p, C7p]) (by norm_num [C6p, C7p])
    (by norm_num [C6p, H0p]) (by norm_num [C6p, H0p])
    (by norm_num) (by norm_num) hM_hh0_6
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh0_7 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (7 : Fin 9) (hub0 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u ⟨8, by norm_num⟩)
    (D := hub0 u) (A0 := C7p) (B0 := C8p) (D0 := H0p) (R := 1 / 10000) (U := 2)
    (err_ring_7 u hu).1 (err_ring_7 u hu).2 (err_ring_8 u hu).1 (err_ring_8 u hu).2
    (err_hub0 u hu).1 (err_hub0 u hu).2
    (by norm_num [C7p, C8p]) (by norm_num [C7p, C8p])
    (by norm_num [C7p, H0p]) (by norm_num [C7p, H0p])
    (by norm_num) (by norm_num) hM_hh0_7
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

-- hh1：`0 ≤ phi (ringCenter u) succ9 i (hub1 u)`，i = 0..8
theorem hh1_0 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (0 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u ⟨1, by norm_num⟩)
    (D := hub1 u) (A0 := C0p) (B0 := C1p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_0 u hu).1 (err_ring_0 u hu).2 (err_ring_1 u hu).1 (err_ring_1 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C0p, C1p]) (by norm_num [C0p, C1p])
    (by norm_num [C0p, H1p]) (by norm_num [C0p, H1p])
    (by norm_num) (by norm_num) hM_hh1_0
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_1 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (1 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u ⟨2, by norm_num⟩)
    (D := hub1 u) (A0 := C1p) (B0 := C2p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_1 u hu).1 (err_ring_1 u hu).2 (err_ring_2 u hu).1 (err_ring_2 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C1p, C2p]) (by norm_num [C1p, C2p])
    (by norm_num [C1p, H1p]) (by norm_num [C1p, H1p])
    (by norm_num) (by norm_num) hM_hh1_1
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_2 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (2 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u ⟨3, by norm_num⟩)
    (D := hub1 u) (A0 := C2p) (B0 := C3p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_2 u hu).1 (err_ring_2 u hu).2 (err_ring_3 u hu).1 (err_ring_3 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C2p, C3p]) (by norm_num [C2p, C3p])
    (by norm_num [C2p, H1p]) (by norm_num [C2p, H1p])
    (by norm_num) (by norm_num) hM_hh1_2
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_3 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (3 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u ⟨4, by norm_num⟩)
    (D := hub1 u) (A0 := C3p) (B0 := C4p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_3 u hu).1 (err_ring_3 u hu).2 (err_ring_4 u hu).1 (err_ring_4 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C3p, C4p]) (by norm_num [C3p, C4p])
    (by norm_num [C3p, H1p]) (by norm_num [C3p, H1p])
    (by norm_num) (by norm_num) hM_hh1_3
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_4 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (4 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u ⟨5, by norm_num⟩)
    (D := hub1 u) (A0 := C4p) (B0 := C5p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_4 u hu).1 (err_ring_4 u hu).2 (err_ring_5 u hu).1 (err_ring_5 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C4p, C5p]) (by norm_num [C4p, C5p])
    (by norm_num [C4p, H1p]) (by norm_num [C4p, H1p])
    (by norm_num) (by norm_num) hM_hh1_4
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_5 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (5 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u ⟨6, by norm_num⟩)
    (D := hub1 u) (A0 := C5p) (B0 := C6p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_5 u hu).1 (err_ring_5 u hu).2 (err_ring_6 u hu).1 (err_ring_6 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C5p, C6p]) (by norm_num [C5p, C6p])
    (by norm_num [C5p, H1p]) (by norm_num [C5p, H1p])
    (by norm_num) (by norm_num) hM_hh1_5
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_6 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (6 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u ⟨7, by norm_num⟩)
    (D := hub1 u) (A0 := C6p) (B0 := C7p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_6 u hu).1 (err_ring_6 u hu).2 (err_ring_7 u hu).1 (err_ring_7 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C6p, C7p]) (by norm_num [C6p, C7p])
    (by norm_num [C6p, H1p]) (by norm_num [C6p, H1p])
    (by norm_num) (by norm_num) hM_hh1_6
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_7 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (7 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u ⟨8, by norm_num⟩)
    (D := hub1 u) (A0 := C7p) (B0 := C8p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_7 u hu).1 (err_ring_7 u hu).2 (err_ring_8 u hu).1 (err_ring_8 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C7p, C8p]) (by norm_num [C7p, C8p])
    (by norm_num [C7p, H1p]) (by norm_num [C7p, H1p])
    (by norm_num) (by norm_num) hM_hh1_7
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

theorem hh1_8 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 (8 : Fin 9) (hub1 u) := by
  have h := orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0)
    (D := hub1 u) (A0 := C8p) (B0 := C0p) (D0 := H1p) (R := 1 / 10000) (U := 2)
    (err_ring_8 u hu).1 (err_ring_8 u hu).2 (err_ring_0 u hu).1 (err_ring_0 u hu).2
    (err_hub1 u hu).1 (err_hub1 u hu).2
    (by norm_num [C8p, C0p]) (by norm_num [C8p, C0p])
    (by norm_num [C8p, H1p]) (by norm_num [C8p, H1p])
    (by norm_num) (by norm_num) hM_hh1_8
  simpa [FlashTiling.phi, FlashTiling.succ9] using h.le

/-! ## §5 装配：`ActualSigns u`（`hcv` 取自 slack 的 63 条，我的 25 条为其余四字段） -/

theorem actualSigns (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    FlashAttainmentFinal.ActualSigns u :=
  { hcv := FlashTilingSigns.ringConvex hu
    hh0 := fun i => by
      fin_cases i <;>
        first
          | exact hh0_0 u hu | exact hh0_1 u hu | exact hh0_2 u hu | exact hh0_3 u hu
          | exact hh0_4 u hu | exact hh0_5 u hu | exact hh0_6 u hu | exact hh0_7 u hu
          | exact hh0_8 u hu
    hh1 := fun i => by
      fin_cases i <;>
        first
          | exact hh1_0 u hu | exact hh1_1 u hu | exact hh1_2 u hu | exact hh1_3 u hu
          | exact hh1_4 u hu | exact hh1_5 u hu | exact hh1_6 u hu | exact hh1_7 u hu
          | exact hh1_8 u hu
    hchordA := fun j hj => by
      rcases hj with rfl | rfl | rfl <;>
        first | exact chordA_3 u hu | exact chordA_4 u hu | exact chordA_5 u hu
    hchordB := fun j hj => by
      rcases hj with rfl | rfl | rfl | rfl <;>
        first | exact chordB_7 u hu | exact chordB_8 u hu | exact chordB_0 u hu | exact chordB_1 u hu }

end N11Formalization.FlashTilingHubChordSigns

#print axioms N11Formalization.FlashTilingHubChordSigns.err_ring_0
#print axioms N11Formalization.FlashTilingHubChordSigns.err_hub0
#print axioms N11Formalization.FlashTilingHubChordSigns.chordA_3
#print axioms N11Formalization.FlashTilingHubChordSigns.chordB_0
#print axioms N11Formalization.FlashTilingHubChordSigns.hh0_0
#print axioms N11Formalization.FlashTilingHubChordSigns.hh1_8
#print axioms N11Formalization.FlashTilingHubChordSigns.actualSigns
