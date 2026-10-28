import N11Formalization.F1.BallD35Hrad
import N11Formalization.ResidualDerivJTHess

/-!
# Lead：**盒版 `hessIvBox` ＋ `HessOfBox`**（49 格内容的容器 ✓）

**为什么需要它**（R186 查证 ✓）：`hessIv`（`ResidualDerivJTHess` L440–453 ✓）只把 **`d2xIv`／`d2yIv`** 参数化 ✗，
   而内部的一阶/几何表（`d1xIv`／`d1yIv`／`DxIv`／`DyIv`／`radIv`／`twoRadSqrtIv`）**全是中心版** ✗
   ⇒ 于是 `HessOf d2xIvBox d2yIvBox` = **盒二阶 ＋ 中心一阶** ✗ ⇒ 对球大概**过紧**（作包络不成立 ✗）
**本件**：把 `hessIv` 的**六处表全部换成盒版**（**纯文字替换** ✓）＋ 盒版 `HessOfBox` ✓。
**关键简化**（R188 实测 ✓）：盒版家族**本身含 `k = 4` 支**（`dUxIvBox` L341–346 ✓）⇒ **不需要 `dUx4IvBox`、也不需要分派器** ✓✓
   ⇒ 故 `d1xIvBox := dUxIvBox`（平凡 ✓），六对替换为：
   `d1xIv k i → dUxIvBox k i`｜`d1yIv k i → dUyIvBox k i`｜`DxIv k → DxIvBox k`｜`DyIv k → DyIvBox k`｜`radIv k → radIvBox k`｜`twoRadSqrtIv k → twoRadSqrtIvBox k` ✓
★ **本件零证明** ✓（两个 `def` ✓）；**它的 `_mem` 才是 49 格内容**（下一件 ✓）。
口径：`open RatInterval`（§66.2 ✓）；含 `invPos`／`sqrt` ⇒ `noncomputable` ✓。
判据：**exit=0 且输出 0 行**。
-/

namespace N11Formalization.Lead.HessBox

open N11Formalization
open RatInterval

/-- **盒版 `hessIv`**：把 `hessIv`（L440–453）的六处表换成盒版（**纯替换** ✓）。 -/
noncomputable def hessIvBox (d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval)
    (k : Fin 5) (i j : Fin 7) : RatInterval :=
  sub
    (add
      (mul (ofRat 2)
        (mul (invPos (twoRadSqrtIvBox k))
          (add (mul (dUxIvBox k i) (dUxIvBox k j)) (mul (dUyIvBox k i) (dUyIvBox k j)))))
      (mul (ofRat 2)
        (mul (invPos (twoRadSqrtIvBox k))
          (add (mul (DxIvBox k) (d2xIv k i j)) (mul (DyIvBox k) (d2yIv k i j))))))
    (mul (ofRat 2)
      (mul (invPos (mul (radIvBox k) (twoRadSqrtIvBox k)))
        (mul (add (mul (DxIvBox k) (dUxIvBox k i)) (mul (DyIvBox k) (dUyIvBox k i)))
             (add (mul (DxIvBox k) (dUxIvBox k j)) (mul (DyIvBox k) (dUyIvBox k j))))))

/-- **盒版 `HessOf`**：同型 `Fin 7 → Fin 7 → Fin 5 → RatInterval`（照 `HessOf` L456–458 ✓）。 -/
noncomputable def HessOfBox (d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval) :
    Fin 7 → Fin 7 → Fin 5 → RatInterval :=
  fun i j mm => hessIvBox d2xIv d2yIv mm i j

end N11Formalization.Lead.HessBox
