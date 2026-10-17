import N11Formalization.D2Leaves
import N11Formalization.BoxRstar

/-!
# hess-seam：`mem_hessEntry_of_leaves`（叶子 `Mem` ⇒ 外框 `hessIv` 的 `Mem` ⇒ 盒心 `hH`）

**任务**（Lead 派发）：把**叶子 `Mem`**（`ring2`/`Wy2`/`mem_arc2` 的二阶 ＋ `d2xIv`/`d2yIv`
（`Δ` 二阶）＋ `Δ` 一阶（`DxIv`/`DyIv`）＋ `1/(2√S)`）缝成**外框 `hessIv` 的 `Mem`**，
`hL7`（`hessEntry = distHessReal`，同一套 `Δ`/`∂Δ`/`∂²Δ`）**显式具名**地挂上 ⇒ **盒心 `hH`** ⇒ 接
`Jt` 总装；另给 `hH_ball`（一般 `x`、显式具名、不造三阶层）。

## 本件的层（每层只引用**直接下层**的名字；不整塔展开、不整批 `simp`）

| 层 | 内容 | 用到的下层（**都是根内已证名字**） |
|---|---|---|
| L0 | 实侧具名靶 `DxR`/`DyR`/`radR`/`twoRadSqrtR`/`d1xR`/`d1yR`/`d2xR`/`d2yR`/`distHessReal` | — |
| L1 | `mulLo_pos`（`mul` 的端点正性；区间内核缺这一条） | `RatInterval.mul` |
| L2 | `d1xIv_mem`/`d1yIv_mem`（`d1xIv` 的 `k = 4` 分派 ⇒ `dUxIv_mem`/`dUx4Iv_mem`） | `dUxIv_mem`/`dUyIv_mem`/`dUx4Iv_mem`/`dUy4Iv_mem` |
| L3 | `mem_hessIv`（外框缝；**同型于 `ResidualDerivD.compIv_mem`**） | L0＋L1＋L2＋`DxIv_mem`/`DyIv_mem`/`radIv_mem`/`twoRadSqrtIv_mem`/`d2xIv_mem`/`d2yIv_mem` |
| L4 | `mem_hessEntry_of_leaves`（`hL7` ⇒ `hH`） | L3 |
| L5 | 单格判据 `mem_hessIv_cell_0_0_0` / `mem_hessEntry_cell_0_0_0` | L3/L4 |
| L6 | `mem_Jt_at_center_of_leaves`（`Jt` 的 12×12 总装） | L4＋`mem_Jt_at_center` |
| L7 | `hH_ball`：`hessEntryAt` ＋ `HHBall`（球级具名义务）＋ `mem_hessEntry_of_hH_ball`（⇒ 盒心 `hH`） | `hessEntry`/`Metric.closedBall`/`certCR_mem_ball` |

**未消前提（全部显式）**：`hL7`（L7 实数恒等式，见 `evidence/jt-build/HESS-SPEC.md` §2）＋
4 条**有限有理不等式**批（`0 < (WkIv j).lo` ×9、`0 < (radIv k).lo` ×5、`0 < WpIv.lo`）＋
可微性三条（`hdT`/`hd`/`hadj`；根内已有 `differentiableAt_residualFun_cCertR`、
`differentiableAt_TCSystem_of_conditions`、`contDiffAt_fderiv_residualFun`）。

**口径**：盒心 `u0 = first7 cCertR`；端点 = 精确 `ℚ`；无 `decide`-on-`ℚ`、无 `native_decide`、
无 `sorry`、无公理、不改任何根内文件。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-! ## L0. 实侧具名靶（= `DxIv`/`DyIv`/`radIv`/`twoRadSqrtIv`/`d1xIv`/`d1yIv`/`d2xIv`/`d2yIv` 的 Mem 靶） -/

/-- `Δx_k`（真值形态，= `DxIv_mem` 的右端）。 -/
def DxR (k : Fin 5) : ℝ := ((Apt k) (pad12 u0)).ofLp 0 - ((Bpt k) (pad12 u0)).ofLp 0

/-- `Δy_k`。 -/
def DyR (k : Fin 5) : ℝ := ((Apt k) (pad12 u0)).ofLp 1 - ((Bpt k) (pad12 u0)).ofLp 1

/-- `S_k = Δx_k² + Δy_k²`（= `radIv_mem` 的右端）。 -/
def radR (k : Fin 5) : ℝ := DxR k ^ 2 + DyR k ^ 2

/-- `2√S_k`（= `twoRadSqrtIv_mem` 的右端）。 -/
def twoRadSqrtR (k : Fin 5) : ℝ := 2 * Real.sqrt (radR k)

/-- `Δ` 的一阶 x 分量（= `d1xIv` 的 Mem 靶；`k = 4` 走 `wPoint` 支）。 -/
def d1xR (k : Fin 5) (i : Fin 7) : ℝ :=
  if k = 4 then
    (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1) - (dring0CLM 6) (Pi.single i 1))
  else
    (((dring0CLM (resSlot k) + dring0CLM ((resSlot k) + 1) - darc0CLM (resSlot k)) (Pi.single i 1)
      - (coord (resHub k)) (Pi.single i 1)))

/-- `Δ` 的一阶 y 分量（= `d1yIv` 的 Mem 靶；`k = 4` 走 `wPoint`/`ringCenter 6` 支）。 -/
def d1yR (k : Fin 5) (i : Fin 7) : ℝ :=
  if k = 4 then
    ((((1 / (2 * Real.sqrt Wp)) • ((2 * u0 6) • coord 6
          - (2 * ((u0 5 - u0 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) (Pi.single i 1))
      - (dring1CLM 6) (Pi.single i 1))
  else
    (((dring1CLM (resSlot k) + dring1CLM ((resSlot k) + 1) - darc1CLM (resSlot k)) (Pi.single i 1)
      - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))

/-- `Δ` 的二阶 x 分量（= `d2xIv_mem` 的右端）。 -/
def d2xR (k : Fin 5) (i j : Fin 7) : ℝ := secondPartial (DeltaX k) u0 i j

/-- `Δ` 的二阶 y 分量（= `d2yIv_mem` 的右端）。 -/
def d2yR (k : Fin 5) (i j : Fin 7) : ℝ := secondPartial (DeltaY k) u0 i j

/-- **L7 外框的实数靶**（逐字对应 `hessIv` 的表达式树）：
`(d_i·d_j)/√S + (d·d_ij)/√S − (d·d_i)(d·d_j)/S^{3/2}`。 -/
def distHessReal (k : Fin 5) (i j : Fin 7) : ℝ :=
  (2 * ((1 / twoRadSqrtR k) * (d1xR k i * d1xR k j + d1yR k i * d1yR k j))
      + 2 * ((1 / twoRadSqrtR k) * (DxR k * d2xR k i j + DyR k * d2yR k i j)))
    - 2 * ((1 / (radR k * twoRadSqrtR k))
        * ((DxR k * d1xR k i + DyR k * d1yR k i) * (DxR k * d1xR k j + DyR k * d1yR k j)))

/-! ## L1. `mul` 的端点正性（区间内核缺这一条；`twoMulIv_pos` 只管 `ofRat 2` 的左乘） -/

/-- `0 < A.lo`、`0 < B.lo` ⇒ `mul A B` 的四个端点积全正 ⇒ `0 < (mul A B).lo`。 -/
theorem mulLo_pos {A B : RatInterval} (hA : 0 < A.lo) (hB : 0 < B.lo)
    (hAv : Valid A) (hBv : Valid B) : 0 < (mul A B).lo := by
  have hAhi : 0 < A.hi := lt_of_lt_of_le hA hAv
  have hBhi : 0 < B.hi := lt_of_lt_of_le hB hBv
  have h1 : 0 < A.lo * B.lo := mul_pos hA hB
  have h2 : 0 < A.lo * B.hi := mul_pos hA hBhi
  have h3 : 0 < A.hi * B.lo := mul_pos hAhi hB
  have h4 : 0 < A.hi * B.hi := mul_pos hAhi hBhi
  unfold RatInterval.mul
  exact lt_min (lt_min h1 h2) (lt_min h3 h4)

/-! ## L2. `d1xIv` / `d1yIv` 的 `Mem`（`k = 4` 分派 ⇒ 一阶叶子） -/

theorem d1xIv_mem (k : Fin 5) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv (resSlot k)).lo)
    (h1 : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (twoSqrtWkIv 6).lo) :
    (d1xIv k i).Mem (d1xR k i) := by
  by_cases hk : k = 4
  · rw [d1xIv, if_pos hk, d1xR, if_pos hk]
    exact dUx4Iv_mem i hW6
  · rw [d1xIv, if_neg hk, d1xR, if_neg hk]
    exact dUxIv_mem k i h0 h1

theorem d1yIv_mem (k : Fin 5) (i : Fin 7)
    (h0 : 0 < (twoSqrtWkIv (resSlot k)).lo)
    (h1 : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (twoSqrtWkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d1yIv k i).Mem (d1yR k i) := by
  by_cases hk : k = 4
  · rw [d1yIv, if_pos hk, d1yR, if_pos hk]
    exact dUy4Iv_mem i hW6 hWp
  · rw [d1yIv, if_neg hk, d1yR, if_neg hk]
    exact dUyIv_mem k i h0 h1

/-! ## L3. 外框缝：`hessIv` 的 `Mem`（一格 `(k,i,j)`；与 `compIv_mem` 同型） -/

theorem mem_hessIv (k : Fin 5) (i j : Fin 7)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) (hrad : 0 < (radIv k).lo) :
    (hessIv d2xIv d2yIv k i j).Mem (distHessReal k i j) := by
  have h0' : 0 < (twoSqrtWkIv (resSlot k)).lo := twoSqrtWkIv_pos (resSlot k) h0
  have h1' : 0 < (twoSqrtWkIv ((resSlot k) + 1)).lo := twoSqrtWkIv_pos ((resSlot k) + 1) h1
  have h6' : 0 < (twoSqrtWkIv 6).lo := twoSqrtWkIv_pos 6 hW6
  have h1x : (d1xIv k i).Mem (d1xR k i) := d1xIv_mem k i h0' h1' h6'
  have h1xj : (d1xIv k j).Mem (d1xR k j) := d1xIv_mem k j h0' h1' h6'
  have h1y : (d1yIv k i).Mem (d1yR k i) := d1yIv_mem k i h0' h1' h6' hWp
  have h1yj : (d1yIv k j).Mem (d1yR k j) := d1yIv_mem k j h0' h1' h6' hWp
  have hDx : (DxIv k).Mem (DxR k) := DxIv_mem k
  have hDy : (DyIv k).Mem (DyR k) := DyIv_mem k
  have hP : (invPos (twoRadSqrtIv k)).Mem (1 / twoRadSqrtR k) :=
    invPos_mem_div (twoRadSqrtIv_mem k) (twoRadSqrtIv_pos k hrad)
  have hU : (add (mul (d1xIv k i) (d1xIv k j)) (mul (d1yIv k i) (d1yIv k j))).Mem
      (d1xR k i * d1xR k j + d1yR k i * d1yR k j) :=
    add_mem (mul_mem h1x h1xj) (mul_mem h1y h1yj)
  have hG : (add (mul (DxIv k) (d2xIv k i j)) (mul (DyIv k) (d2yIv k i j))).Mem
      (DxR k * d2xR k i j + DyR k * d2yR k i j) :=
    add_mem (mul_mem hDx (d2xIv_mem k i j h0 h1 hW6 hWp))
      (mul_mem hDy (d2yIv_mem k i j h0 h1 hW6 hWp))
  have hT1 : (mul (ofRat 2) (mul (invPos (twoRadSqrtIv k))
        (add (mul (d1xIv k i) (d1xIv k j)) (mul (d1yIv k i) (d1yIv k j))))).Mem
      (2 * ((1 / twoRadSqrtR k) * (d1xR k i * d1xR k j + d1yR k i * d1yR k j))) :=
    mul_mem (ofRat_mem 2) (mul_mem hP hU)
  have hT2 : (mul (ofRat 2) (mul (invPos (twoRadSqrtIv k))
        (add (mul (DxIv k) (d2xIv k i j)) (mul (DyIv k) (d2yIv k i j))))).Mem
      (2 * ((1 / twoRadSqrtR k) * (DxR k * d2xR k i j + DyR k * d2yR k i j))) :=
    mul_mem (ofRat_mem 2) (mul_mem hP hG)
  have hS : (mul (radIv k) (twoRadSqrtIv k)).Mem (radR k * twoRadSqrtR k) :=
    mul_mem (radIv_mem k) (twoRadSqrtIv_mem k)
  have hSpos : 0 < (mul (radIv k) (twoRadSqrtIv k)).lo :=
    mulLo_pos hrad (twoRadSqrtIv_pos k hrad) (valid_of_mem (radIv_mem k))
      (valid_of_mem (twoRadSqrtIv_mem k))
  have hP2 : (invPos (mul (radIv k) (twoRadSqrtIv k))).Mem (1 / (radR k * twoRadSqrtR k)) :=
    invPos_mem_div hS hSpos
  have hci : (add (mul (DxIv k) (d1xIv k i)) (mul (DyIv k) (d1yIv k i))).Mem
      (DxR k * d1xR k i + DyR k * d1yR k i) :=
    add_mem (mul_mem hDx h1x) (mul_mem hDy h1y)
  have hcj : (add (mul (DxIv k) (d1xIv k j)) (mul (DyIv k) (d1yIv k j))).Mem
      (DxR k * d1xR k j + DyR k * d1yR k j) :=
    add_mem (mul_mem hDx h1xj) (mul_mem hDy h1yj)
  have hT3 : (mul (ofRat 2) (mul (invPos (mul (radIv k) (twoRadSqrtIv k)))
        (mul (add (mul (DxIv k) (d1xIv k i)) (mul (DyIv k) (d1yIv k i)))
             (add (mul (DxIv k) (d1xIv k j)) (mul (DyIv k) (d1yIv k j)))))).Mem
      (2 * ((1 / (radR k * twoRadSqrtR k))
        * ((DxR k * d1xR k i + DyR k * d1yR k i)
            * (DxR k * d1xR k j + DyR k * d1yR k j)))) :=
    mul_mem (ofRat_mem 2) (mul_mem hP2 (mul_mem hci hcj))
  exact sub_mem (add_mem hT1 hT2) hT3

/-! ## L4. `hL7`（显式具名）⇒ 盒心 `hH` -/

/-- **`mem_hessEntry_of_leaves`**：`hL7`（`hessEntry = distHessReal`，同一套 `Δ`/`∂Δ`/`∂²Δ`）＋
4 条**有限有理不等式**批 ⇒ 盒心 `hH`（= `Jt` 总装唯一条件前提）。 -/
theorem mem_hessEntry_of_leaves
    (hL7 : ∀ (i j : Fin 7) (mm : Fin 5), hessEntry i j mm = distHessReal mm i j)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (i j : Fin 7) (mm : Fin 5) :
    (HessOf d2xIv d2yIv i j mm).Mem (hessEntry i j mm) := by
  rw [hL7 i j mm]
  exact mem_hessIv mm i j (hWk (resSlot mm)) (hWk ((resSlot mm) + 1)) (hWk 6) hWp (hrad mm)

/-! ## L5. 单格判据（Lead 派发）：`(k,i,j) = (0,0,0)` -/

/-- 单格外框（`hessIv 0 0 0`；`resSlot 0 = 1`、`resSlot 0 + 1 = 2`）。 -/
theorem mem_hessIv_cell_0_0_0
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) :
    (hessIv d2xIv d2yIv 0 0 0).Mem (distHessReal 0 0 0) :=
  mem_hessIv 0 0 0 (hWk 1) (hWk 2) (hWk 6) hWp (hrad 0)

/-- 单格 `hH`（`(i,j,mm) = (0,0,0)`）。 -/
theorem mem_hessEntry_cell_0_0_0
    (hL7 : ∀ (i j : Fin 7) (mm : Fin 5), hessEntry i j mm = distHessReal mm i j)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) :
    (HessOf d2xIv d2yIv 0 0 0).Mem (hessEntry 0 0 0) :=
  mem_hessEntry_of_leaves hL7 hWk hrad hWp 0 0 0

/-! ## L6. `Jt` 的 12×12 总装（唯一条件前提 = `hL7` ＋ 三条可微性 ＋ 三批有限有理不等式） -/

theorem mem_Jt_at_center_of_leaves
    (hL7 : ∀ (i j : Fin 7) (mm : Fin 5), hessEntry i j mm = distHessReal mm i j)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (r c : Fin 12) :
    (Jt (HessOf d2xIv d2yIv) r c).Mem ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) r) :=
  mem_Jt_at_center (HessOf d2xIv d2yIv) hdT hd hadj hWk hrad hWp
    (mem_hessEntry_of_leaves hL7 hWk hrad hWp) r c

/-! ## L7. `hH_ball`：一般 `x`（**不造三阶层**；`HESS-SPEC §6` 路径 1 = 盒上直接区间求值） -/

/-- 一般点 `x` 的 Hessian 单元（`hessEntryAt u0 = hessEntry`；只换求值点，不换阶数）。 -/
def hessEntryAt (x : Fin 7 → ℝ) (i j : Fin 7) (mm : Fin 5) : ℝ :=
  ((fderiv ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) x) (Pi.single j 1)) (Pi.single i 1) mm

theorem hessEntry_eq_hessEntryAt (i j : Fin 7) (mm : Fin 5) :
    hessEntry i j mm = hessEntryAt u0 i j mm := rfl

/-- **`hH_ball`（球级二阶义务的显式具名形态）**：同一个 `Hess` 在**整个证书球**上包络
`hessEntryAt`。它是 `hH` 的 `x`-参数化加强，**不需要**残差三阶（盒上直接区间求值即可）。 -/
def HHBall (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) : Prop :=
  ∀ x ∈ Metric.closedBall u0 rhoCertR, ∀ i j mm, (Hess i j mm).Mem (hessEntryAt x i j mm)

/-- **`hH_ball ⇒ hH`**（只需球心在球内 = `0 ≤ rhoCertR`；**零新层**）。 -/
theorem mem_hessEntry_of_hH_ball {Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval}
    (h : HHBall Hess) (hρ : 0 ≤ rhoCertR) : ∀ i j mm, (Hess i j mm).Mem (hessEntry i j mm) := by
  intro i j mm
  rw [hessEntry_eq_hessEntryAt]
  exact h u0 (Metric.mem_closedBall.mpr (by simpa using hρ)) i j mm

/-- **球级 `hH` 的 `Jt` 形态**（球心处；消费侧若能给出 `hH_ball`，则 `Jt` 总装在球心处
无条件成立 —— 与 `hH` 版本同一条链，只是前提更强）。 -/
theorem mem_Jt_at_center_of_hH_ball {Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval}
    (h : HHBall Hess) (hρ : 0 ≤ rhoCertR)
    (hdT : DifferentiableAt ℝ TCSystem cCertR) (hd : DifferentiableAt ℝ residualFun u0)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) u0)
    (hWk : ∀ j : Fin 9, 0 < (WkIv j).lo) (hrad : ∀ k : Fin 5, 0 < (radIv k).lo)
    (hWp : 0 < WpIv.lo) (r c : Fin 12) :
    (Jt Hess r c).Mem ((fderiv ℝ TCSystem cCertR (Pi.single c 1)) r) :=
  mem_Jt_at_center Hess hdT hd hadj hWk hrad hWp (mem_hessEntry_of_hH_ball h hρ) r c

end HessSeam

end N11Formalization
