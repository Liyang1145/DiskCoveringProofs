import N11Formalization.C450Identify

/-!
# C450：**实际几何 → 条件盒**（generic bounds，V2）

**本文件不含 C450 的排除结论。** 本件只登记两个 **generic bounds**（区间型）：
`c450B_mem_of_ell_box`（`ℓ` 盒 ⟹ `b` 区间）与 `c450Cq_mem_of_boxes`（`ρ,v,e,ℓ` 盒 ⟹ `u` 区间）。
**不**声称解除 root 几何 box 前提；**不**接任何 consumer 阈值（新 consumer 若走宽盒
`b ∈ [11/20,2/3]` 须另写型，不得套旧 `3/5` 前提）。

## V2 相对 `lead/c450-geombox-gate1.log` exit1 的修复（3 处）

| gate1 | 错误 | V2 修法 |
|---|---|---|
| L74 | `rw [← hc0]` 目标里没有 product 形状 | 按 Lead：改 `rw [hc0]`（**目标方向**，把 `c 0` 换成 `‖c‖ * (c 0/‖c‖)`） |
| L80/L86 | `div_le_div_iff_of_pos` **不存在**（真库只有 `div_le_div_iff_of_pos_right/_left`，且为同分母/单侧形） | 不猜名：改为**清分母**路线 —— 先叉乘得 key，再用 `sub_nonneg` + `div_nonneg` + `pool`-free 恒等式（`field_simp; ring`）证明差的非负 |

## 不主张

* 不主张段域、逐段盒界、`hper` 或十边界支。
-/

namespace N11Formalization

section

/-- **`b`-盒**（`ℓ`-盒 ⟹ `c450B` 区间；`Real.arccos` 反单调）。 -/
theorem c450B_mem_of_ell_box {c : Point} {e ℓ_lo ℓ_hi : ℝ}
    (hlo : ℓ_lo ≤ ‖c - !₂[e, 0]‖) (hhi : ‖c - !₂[e, 0]‖ ≤ ℓ_hi)
    (h2R : ℓ_hi < 2 * ((19 : ℝ) / 50)) :
    Real.arccos (ℓ_hi / (2 * ((19 : ℝ) / 50))) ≤ c450B c e
      ∧ c450B c e ≤ Real.arccos (ℓ_lo / (2 * ((19 : ℝ) / 50))) := by
  have h2Rpos : (0 : ℝ) < 2 * ((19 : ℝ) / 50) := by norm_num
  have hlt : ‖c - !₂[e, 0]‖ < 2 * ((19 : ℝ) / 50) := lt_of_le_of_lt hhi h2R
  have hB : c450B c e = Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50))) := by
    rw [c450B, if_pos hlt]
  rw [hB]
  constructor
  · exact Real.arccos_le_arccos (by rw [div_le_div_iff_of_pos_right h2Rpos]; exact hhi)
  · exact Real.arccos_le_arccos (by rw [div_le_div_iff_of_pos_right h2Rpos]; exact hlo)

/-- **`u`-盒**（`ρ,v,e,ℓ` 盒 ⟹ `c450Cq` 区间）。`hA0/hB0` 是几何层给的两条正性前提。 -/
theorem c450Cq_mem_of_boxes {c : Point} {e ρ_lo ρ_hi v_lo v_hi e_lo e_hi ℓ_lo ℓ_hi : ℝ}
    (hρlo : ρ_lo ≤ ‖c‖) (hρhi : ‖c‖ ≤ ρ_hi) (hρpos : 0 < ρ_lo)
    (hvlo : v_lo ≤ c 0 / ‖c‖) (hvhi : c 0 / ‖c‖ ≤ v_hi) (hv0 : 0 ≤ v_lo)
    (helo : e_lo ≤ e) (hehi : e ≤ e_hi)
    (hℓlo : ℓ_lo ≤ ‖c - !₂[e, 0]‖) (hℓhi : ‖c - !₂[e, 0]‖ ≤ ℓ_hi) (hℓpos : 0 < ℓ_lo)
    (hA0 : 0 ≤ ρ_lo * v_lo - e_hi) (hB0 : 0 ≤ ρ_hi * v_hi - e_lo) :
    (ρ_lo * v_lo - e_hi) / ℓ_hi ≤ c450Cq c e
      ∧ c450Cq c e ≤ (ρ_hi * v_hi - e_lo) / ℓ_lo := by
  have hρ : (0 : ℝ) < ‖c‖ := lt_of_lt_of_le hρpos hρlo
  have hc0 : c 0 = ‖c‖ * (c 0 / ‖c‖) := by field_simp
  have hvnn : (0 : ℝ) ≤ c 0 / ‖c‖ := le_trans hv0 hvlo
  have hLpos : (0 : ℝ) < ‖c - !₂[e, 0]‖ := lt_of_lt_of_le hℓpos hℓlo
  have hℓhipos : (0 : ℝ) < ℓ_hi := lt_of_lt_of_le hLpos hℓhi
  have hnum_lo : ρ_lo * v_lo - e_hi ≤ c 0 - e := by
    have h1 : ρ_lo * v_lo ≤ ρ_lo * (c 0 / ‖c‖) := mul_le_mul_of_nonneg_left hvlo hρpos.le
    have h2 : ρ_lo * (c 0 / ‖c‖) ≤ ‖c‖ * (c 0 / ‖c‖) := mul_le_mul_of_nonneg_right hρlo hvnn
    rw [hc0]
    linarith
  have hnum_hi : c 0 - e ≤ ρ_hi * v_hi - e_lo := by
    have hvhin : (0 : ℝ) ≤ v_hi := le_trans hv0 (le_trans hvlo hvhi)
    have h1 : ‖c‖ * (c 0 / ‖c‖) ≤ ‖c‖ * v_hi :=
      mul_le_mul_of_nonneg_left hvhi (norm_nonneg c)
    have h2 : ‖c‖ * v_hi ≤ ρ_hi * v_hi := mul_le_mul_of_nonneg_right hρhi hvhin
    rw [hc0]
    linarith
  have hnumlo_nn : (0 : ℝ) ≤ c 0 - e := le_trans hA0 hnum_lo
  have hCq : c450Cq c e = (c 0 - e) / ‖c - !₂[e, 0]‖ := rfl
  rw [hCq]
  constructor
  · -- 下界：叉乘 key，再清分母
    have hkey : (ρ_lo * v_lo - e_hi) * ‖c - !₂[e, 0]‖ ≤ (c 0 - e) * ℓ_hi := by
      have s1 : (ρ_lo * v_lo - e_hi) * ‖c - !₂[e, 0]‖ ≤ (c 0 - e) * ‖c - !₂[e, 0]‖ :=
        mul_le_mul_of_nonneg_right hnum_lo (le_of_lt hLpos)
      have s2 : (c 0 - e) * ‖c - !₂[e, 0]‖ ≤ (c 0 - e) * ℓ_hi :=
        mul_le_mul_of_nonneg_left hℓhi hnumlo_nn
      linarith
    have hsub : 0 ≤ (c 0 - e) / ‖c - !₂[e, 0]‖ - (ρ_lo * v_lo - e_hi) / ℓ_hi := by
      have hnum : 0 ≤ (c 0 - e) * ℓ_hi - (ρ_lo * v_lo - e_hi) * ‖c - !₂[e, 0]‖ := by linarith
      have hdist : (c 0 - e) / ‖c - !₂[e, 0]‖ - (ρ_lo * v_lo - e_hi) / ℓ_hi
          = ((c 0 - e) * ℓ_hi - (ρ_lo * v_lo - e_hi) * ‖c - !₂[e, 0]‖)
            / (‖c - !₂[e, 0]‖ * ℓ_hi) := by
        field_simp <;> ring
      rw [hdist]
      exact div_nonneg hnum (le_of_lt (mul_pos hLpos hℓhipos))
    linarith
  · -- 上界：同法
    have hkey : (c 0 - e) * ℓ_lo ≤ (ρ_hi * v_hi - e_lo) * ‖c - !₂[e, 0]‖ := by
      have s1 : (c 0 - e) * ℓ_lo ≤ (ρ_hi * v_hi - e_lo) * ℓ_lo :=
        mul_le_mul_of_nonneg_right hnum_hi (le_of_lt hℓpos)
      have s2 : (ρ_hi * v_hi - e_lo) * ℓ_lo ≤ (ρ_hi * v_hi - e_lo) * ‖c - !₂[e, 0]‖ :=
        mul_le_mul_of_nonneg_left hℓlo hB0
      linarith
    have hsub : 0 ≤ (ρ_hi * v_hi - e_lo) / ℓ_lo - (c 0 - e) / ‖c - !₂[e, 0]‖ := by
      have hnum : 0 ≤ (ρ_hi * v_hi - e_lo) * ‖c - !₂[e, 0]‖ - (c 0 - e) * ℓ_lo := by linarith
      have hdist : (ρ_hi * v_hi - e_lo) / ℓ_lo - (c 0 - e) / ‖c - !₂[e, 0]‖
          = ((ρ_hi * v_hi - e_lo) * ‖c - !₂[e, 0]‖ - (c 0 - e) * ℓ_lo)
            / (‖c - !₂[e, 0]‖ * ℓ_lo) := by
        field_simp <;> ring
      rw [hdist]
      exact div_nonneg hnum (le_of_lt (mul_pos hLpos hℓpos))
    linarith

#check @N11Formalization.c450B_mem_of_ell_box
#check @N11Formalization.c450Cq_mem_of_boxes

#print axioms N11Formalization.c450B_mem_of_ell_box
#print axioms N11Formalization.c450Cq_mem_of_boxes

end

end N11Formalization
