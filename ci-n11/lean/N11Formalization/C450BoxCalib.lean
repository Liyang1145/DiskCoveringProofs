import N11Formalization.C450Identify
import N11Formalization.C450EllMono
import N11Formalization.C450GeomBox

/-!
# C450：**实际合法域的六条件校准**（单盒）

**本文件不含 C450 的排除结论。** 它把 `C450EllMono.ell_mem_of_box` 的**六条符号前提**
在**实际几何合法域** `ρ ∈ [6199/10000, 6201/10000]`、`v ∈ [1/4, 1]`、`e ∈ [0, 1/250]`
上**逐条 discharge**（全部 `norm_num`），得到该盒的 `ℓ²`/`ℓ` 区间 —— 即"实际域 → 盒"里
**纯算术的那一半**（不是再套一层 generic hyp：六条前提在此**由具体数决定**，无待定假设）。

## 依赖（Lead 负责 module copy/build，同 identify 先例）

* `N11Formalization.C450EllMono` ← 由本 scope 的 `C450EllMono.V3.lean`
  （`16A39B64EBA38FC2CAEF4CF5C9DF046239810C9E5D297C04549DACAF3879250D`，gate3 GREEN）集成；
* `N11Formalization.C450GeomBox` ← 由 `C450GeomBox.V2.lean`
  （`D0211E675D9A53323B8C6FDFE11A82E3643A746E7E5897AF789D60C6AD5F03BC`，gate2 GREEN，generic boxes）集成；
* `N11Formalization.C450Identify`（已在树内）。

## 仍未做（真实域的另一半，写明）

* `ρ` 的**来源**：`ρ = cos t − √(R² − sin²t)`（内根）、`t ∈ [0, 1/1250]` ⟹
  `ρ ∈ [cos(1/1250) − R, 1 − √(R² − sin²(1/1250))]`（`cos`/`sin` 单调 + Lag 包络），
  数值上 ≈ `[0.61999968, 0.62000084] ⊂ [6199/10000, 6201/10000]`（本件把它作为**输入前提**，未证）；
* `v = c₀/ρ ∈ [1/4, 1]`（由 φ 的域）与 `e ∈ [0, 1/250]`（seg-0 的 e-段）同理；
* `b` 侧有理比较（宽盒 `[11/20, 2/3]`）另写新 consumer 型；**不**套 `C450InnerAtom` 的 `3/5` 前提。

## 不主张

* 不主张逐段盒界、`hper`、十边界支；本件只把"实际域六条件"钉成具体数。
-/

namespace N11Formalization

section

/-- `ℓ²` 盒（**实际合法域**）：`ρ ∈ [6199/10000,6201/10000]`、`v ∈ [1/4,1]`、`e ∈ [0,1/250]`
⟹ `ℓ² ∈ [ℓ²(6199/10000, 1, 1/250), ℓ²(6201/10000, 1/4, 0)]`。
六条符号前提逐条由 `norm_num` discharge（无待定假设）。 -/
theorem ellsq_box_seg0 {ρ v e : ℝ}
    (hρlo : (6199 : ℝ) / 10000 ≤ ρ) (hρhi : ρ ≤ (6201 : ℝ) / 10000)
    (hvlo : (1 : ℝ) / 4 ≤ v) (hvhi : v ≤ 1)
    (helo : (0 : ℝ) ≤ e) (hehi : e ≤ 1 / 250) :
    (((6199 : ℝ) / 10000) ^ 2) - 2 * ((6199 : ℝ) / 10000) * 1 * (1 / 250) + (1 / 250) ^ 2
        ≤ ρ ^ 2 - 2 * ρ * v * e + e ^ 2
      ∧ ρ ^ 2 - 2 * ρ * v * e + e ^ 2
        ≤ (((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0 + 0 ^ 2 := by
  refine ellsq_mem_of_box (ρ_lo := (6199 : ℝ) / 10000) (ρ_hi := (6201 : ℝ) / 10000)
    (v_lo := (1 : ℝ) / 4) (v_hi := 1) (e_lo := 0) (e_hi := 1 / 250)
    hρlo hρhi hvlo hvhi helo hehi ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num

/-- `ℓ` 盒（开方，实际合法域）。 -/
theorem ell_box_seg0 {ρ v e : ℝ}
    (hρlo : (6199 : ℝ) / 10000 ≤ ρ) (hρhi : ρ ≤ (6201 : ℝ) / 10000)
    (hvlo : (1 : ℝ) / 4 ≤ v) (hvhi : v ≤ 1)
    (helo : (0 : ℝ) ≤ e) (hehi : e ≤ 1 / 250) :
    Real.sqrt ((((6199 : ℝ) / 10000) ^ 2) - 2 * ((6199 : ℝ) / 10000) * 1 * (1 / 250)
          + (1 / 250) ^ 2)
        ≤ Real.sqrt (ρ ^ 2 - 2 * ρ * v * e + e ^ 2)
      ∧ Real.sqrt (ρ ^ 2 - 2 * ρ * v * e + e ^ 2)
        ≤ Real.sqrt ((((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0
          + 0 ^ 2) := by
  refine ell_mem_of_box (ρ_lo := (6199 : ℝ) / 10000) (ρ_hi := (6201 : ℝ) / 10000)
    (v_lo := (1 : ℝ) / 4) (v_hi := 1) (e_lo := 0) (e_hi := 1 / 250)
    hρlo hρhi hvlo hvhi helo hehi ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num

/-- `b` 的**区间型**（把 `ℓ` 盒接到 `c450B`；`ℓ_hi = √(ℓ²(6201/10000,1/4,0)) < 2R` 由 `norm_num` 侧给出）。 -/
theorem b_box_seg0 {c : Point} {e : ℝ}
    (hℓlo : Real.sqrt ((((6199 : ℝ) / 10000) ^ 2) - 2 * ((6199 : ℝ) / 10000) * 1 * (1 / 250)
          + (1 / 250) ^ 2) ≤ ‖c - !₂[e, 0]‖)
    (hℓhi : ‖c - !₂[e, 0]‖
      ≤ Real.sqrt ((((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0 + 0 ^ 2))
    (h2R : Real.sqrt ((((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0 + 0 ^ 2)
      < 2 * ((19 : ℝ) / 50)) :
    Real.arccos (Real.sqrt ((((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0
        + 0 ^ 2) / (2 * ((19 : ℝ) / 50)))
        ≤ c450B c e
      ∧ c450B c e ≤ Real.arccos (Real.sqrt ((((6199 : ℝ) / 10000) ^ 2)
        - 2 * ((6199 : ℝ) / 10000) * 1 * (1 / 250) + (1 / 250) ^ 2) / (2 * ((19 : ℝ) / 50))) :=
  c450B_mem_of_ell_box hℓlo hℓhi h2R

#check @N11Formalization.ellsq_box_seg0
#check @N11Formalization.ell_box_seg0
#check @N11Formalization.b_box_seg0

#print axioms N11Formalization.ellsq_box_seg0
#print axioms N11Formalization.ell_box_seg0

end

end N11Formalization
