import N11Formalization.HessIvBox
import N11Formalization.HessSeamMain
import N11Formalization.D2Leaves
import N11Formalization.F1.BallD35Hrad

/-!
# Lead：**盒版 L7 外框 `mem_hessIvBox`**（49 格内容的**核心** ✓）—— **v4：修 def 第三项的分母**

**v1–v3 的教训（子代理 33 次尝试 ＋ 全打印，共同定案 ✓✓）**：
* `hP2`／`hT3` 我**手写**类型 ✗ ⇒ 产生"我抄的形 ≠ Lean 产出的形" ✗ ⇒ **已改为不写类型** ✓（v3 起 ✓，一次消掉 2 个错 ✓）
* **最后一个错**由**全打印**定案 ✓：goal 的第三项是 **`(1 / (G) * (2√G)) * (…)`** ✗，
  而 `invPos_mem_div` 产出的是 **`(1 / (G * (2√G))) * (…)`** ✓ —— **数学上对的是后者** ✓（`mul` 的值 = `G * 2√G` ✓）
  ⇒ ⇒ **故改 def**：第三项的 `1 / (` 组**必须包住 `(2 * √G)`** ✓✓
**另两条（子代理 ✓）**：`mulLo_pos` 在 **`namespace N11Formalization.HessSeam`** 内 ⇒ 需 `import …HessSeamMain` **＋** `open N11Formalization.HessSeam` ✓；
`d2` 两条**作参数** ✓。判据：**exit=0 且输出 0 行**（**无 `sorry`** ✓）。
-/

namespace N11Formalization.Lead.HessBoxMem

open N11Formalization
open RatInterval
open N11Formalization.HessSeam
open N11Formalization.Lead.HessBox

/-- **盒版 L7 外框的实数靶**（`distHessReal`（`HessSeamMain` L82–86 ✓）的**逐点**版 ✓）。 -/
noncomputable def distHessRealBox (x : Fin 12 → ℝ) (k : Fin 5) (i j : Fin 7) : ℝ :=
  (2 * ((1 / (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2 + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)))
          * (dUxReal k i x * dUxReal k j x + dUyReal k i x * dUyReal k j x))
     + 2 * ((1 / (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2 + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)))
          * ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * secondPartial (DeltaX k) (first7 x) i j
             + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * secondPartial (DeltaY k) (first7 x) i j))
     - 2 * ((1 / (((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2 + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2)
              * (2 * Real.sqrt ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2 + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2))))
          * (((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * dUxReal k i x
                + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * dUyReal k i x)
              * ((((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) * dUxReal k j x
                + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) * dUyReal k j x))))

/-- **盒版 `mem_hessIv`**（49 格内容的**核心** ✓；`d2` 两条作参数 ✓；**中间体不写类型** ✓）。 -/
theorem mem_hessIvBox (d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval)
    {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR)
    (k : Fin 5)
    (hrad : 0 < (radIvBox k).lo) (h2rad : 0 < (twoRadSqrtIvBox k).lo)
    (hd2x : ∀ (k : Fin 5) (i j : Fin 7), (d2xIv k i j).Mem (secondPartial (DeltaX k) (first7 x) i j))
    (hd2y : ∀ (k : Fin 5) (i j : Fin 7), (d2yIv k i j).Mem (secondPartial (DeltaY k) (first7 x) i j))
    (i j : Fin 7) :
    (hessIvBox d2xIv d2yIv k i j).Mem (distHessRealBox x k i j) := by
  have h1x := dUxIvBox_mem k i hx
  have h1xj := dUxIvBox_mem k j hx
  have h1y := dUyIvBox_mem k i hx
  have h1yj := dUyIvBox_mem k j hx
  have hDx := DxIvBox_mem k hx
  have hDy := DyIvBox_mem k hx
  have hP := invPos_mem_div (twoRadSqrtIvBox_mem k hx) h2rad
  have hU := add_mem (mul_mem h1x h1xj) (mul_mem h1y h1yj)
  have hG := add_mem (mul_mem hDx (hd2x k i j)) (mul_mem hDy (hd2y k i j))
  have hS := mul_mem (radIvBox_mem k hx) (twoRadSqrtIvBox_mem k hx)
  have hSpos : 0 < (mul (radIvBox k) (twoRadSqrtIvBox k)).lo :=
    mulLo_pos hrad h2rad (valid_of_mem (radIvBox_mem k hx))
      (valid_of_mem (twoRadSqrtIvBox_mem k hx))
  have hP2 := invPos_mem_div hS hSpos
  have hci := add_mem (mul_mem hDx h1x) (mul_mem hDy h1y)
  have hcj := add_mem (mul_mem hDx h1xj) (mul_mem hDy h1yj)
  have hT1 := mul_mem (ofRat_mem 2) (mul_mem hP hU)
  have hT2 := mul_mem (ofRat_mem 2) (mul_mem hP hG)
  have hT3 := mul_mem (ofRat_mem 2) (mul_mem hP2 (mul_mem hci hcj))
  simp only [hessIvBox, distHessRealBox]
  exact sub_mem (add_mem hT1 hT2) hT3

end N11Formalization.Lead.HessBoxMem
