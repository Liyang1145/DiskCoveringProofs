import N11Formalization.ResidualInterval
import N11Formalization.IntervalsHighLag

/-!
# `Fm` 的高阶（**阶乘余项**）入口 `*Lag` —— 独立模块

本文件把 `ResidualInterval.lean` 的几何表达式树**逐节点**照搬到 `IntervalsHighLag.lean`
（Lead）的阶乘版点级界上：`sinLoNLag_le_sin` / `sin_le_sinHiNLag` /
`cosLoNLag_le_cos` / `cos_le_cosHiNLag`（余项 `|q|^29/29!`、`|q|^28/28!`，
**对每个 `q : ℚ` 成立**；`|q| ≤ 1` 上宽度 `≤ 2/29! ≈ 5.0e-31`）。

**为什么单独成件**：`IntervalsHighLag.lean` 由 Lead 维护且在改；核心件
`ResidualInterval.lean` 是 `FmAssembly`（box-rstar）的依赖，必须只依赖稳定的
`Interval/Range`。故高阶入口在此单独声明，**不改**核心件的任何名字与形状。

读数：`ResidualIntervalReadoutLag.lean`（`FM_MODE=lag` 生成）给出本件 5 个分量的
**精确端点与宽度**（kernel-proved），全部 `< 9.956e-10`。
-/

noncomputable section

namespace N11Formalization

/-! ## 6. 高阶（**阶乘余项**）入口：`*Lag`

`DEAD §C′` 的三角精度缺口由 `IntervalsHighLag.lean` 的**阶乘版**点级界修掉
（`sinLoNLag_le_sin` / `sin_le_sinHiNLag` / `cosLoNLag_le_cos` / `cos_le_cosHiNLag`，
对**每个** `q : ℚ` 成立；`|q| ≤ 1` 上宽度 `≤ 2/29! ≈ 5.0e-31`）。
本节只**新增**入口，不动上面的低阶版本（`box-rstar` 的 `FmAssembly` 依赖
`mem_residualInterval*` 的名字与形状，保持不变）：

* `sinTotLag` / `cosTotLag`：同一套相位机制（`phaseOf` + `reducedBox` + `phasePos/Neg`）
  换到阶乘版点级界；
* `residualIntervalLag`：几何表达式树**逐节点相同**，只把三角算子换成 `*Lag`；
* `mem_residualIntervalLag`（任意 `q`，无条件）/ `..._cCert`（证书盒心实例化）。

**读数**：`ResidualIntervalReadoutLag.lean`（由 `evidence/fm-eval/gen_readout.py` 生成）
给出 `*Lag` 版 5 个分量的**精确端点与宽度**（kernel-proved），
`FM_TRIG_MODE=lagrange` 的 Python 投影与之逐位一致。 -/

namespace RatInterval

theorem sinIHighLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    (sinIHighLag A).Mem (Real.sin x) := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  unfold sinIHighLag
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [if_pos h]
    have hlo1 : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have hhi1 : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hlo' : -(Real.pi / 2) ≤ (A.lo : ℝ) := le_trans neg_pi_div_two_le_neg_one hlo1
    have hhi' : (A.hi : ℝ) ≤ Real.pi / 2 := le_trans hhi1 one_le_pi_div_two
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((sinLoNLag A.lo : ℚ) : ℝ) ≤ Real.sin x
      have hmono : Real.sin (A.lo : ℝ) ≤ Real.sin x :=
        Real.sin_le_sin_of_le_of_le_pi_div_two hlo' (by linarith [hhi', hhi]) hlo
      exact le_trans (sinLoNLag_le_sin A.lo) hmono
    · show Real.sin x ≤ ((sinHiNLag A.hi : ℚ) : ℝ)
      have hmono : Real.sin x ≤ Real.sin (A.hi : ℝ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hlo', hlo]) hhi' hhi
      exact le_trans hmono (sin_le_sinHiNLag A.hi)
  · rw [if_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.sin x
      push_cast
      exact neg_one_le_sin x
    · show Real.sin x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact sin_le_one' x

/-- 阶乘版紧 `cos` 区间（上端点 `cosHiNLag (min|·|)`，与 `cosWin` 同款但用阶乘界）。 -/
def cosWinLag (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨cosLoNLag (highAbs A), cosHiNLag (lowAbs A)⟩ else intv (-1) 1

theorem cosWinLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    (cosWinLag A).Mem (Real.cos x) := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  unfold cosWinLag
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [if_pos h]
    have hlo1 : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have hhi1 : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hMcast : ((highAbs A : ℚ) : ℝ) = max |(A.lo : ℝ)| |(A.hi : ℝ)| := by
      unfold highAbs; push_cast; rfl
    have hxM : |x| ≤ ((highAbs A : ℚ) : ℝ) := by
      rw [hMcast]; exact abs_le_max_abs_endpoints hlo hhi
    have hM0 : (0 : ℝ) ≤ ((highAbs A : ℚ) : ℝ) := by
      rw [hMcast]; exact le_trans (abs_nonneg _) (le_max_left _ _)
    have hM1 : ((highAbs A : ℚ) : ℝ) ≤ 1 := by
      rw [hMcast]
      refine max_le ?_ ?_
      · rw [abs_le]; exact ⟨by linarith, by linarith⟩
      · rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hmcast : ((lowAbs A : ℚ) : ℝ) = (if 0 ≤ A.lo then (A.lo : ℝ)
        else if A.hi ≤ 0 then -((A.hi : ℝ)) else 0) := by
      unfold lowAbs
      by_cases h1 : 0 ≤ A.lo
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : A.hi ≤ 0
        · rw [if_pos h2, if_pos h2]; push_cast; ring
        · rw [if_neg h2, if_neg h2]; norm_num
    have hmx : ((lowAbs A : ℚ) : ℝ) ≤ |x| := by
      rw [hmcast]
      by_cases h1 : 0 ≤ A.lo
      · rw [if_pos h1]
        have h1' : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h1
        rw [abs_of_nonneg (le_trans h1' hlo)]
        exact hlo
      · rw [if_neg h1]
        by_cases h2 : A.hi ≤ 0
        · rw [if_pos h2]
          have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
          have hx0 : x ≤ 0 := le_trans hhi h2'
          rw [abs_of_nonpos hx0]
          linarith
        · rw [if_neg h2]
          exact abs_nonneg x
    have hm0 : (0 : ℝ) ≤ ((lowAbs A : ℚ) : ℝ) := by
      rw [hmcast]
      split_ifs with h1 h2
      · exact_mod_cast h1
      · have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
        linarith
      · norm_num
    have hm1 : ((lowAbs A : ℚ) : ℝ) ≤ 1 := le_trans hmx hx1
    have hcosabs : Real.cos |x| = Real.cos x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.cos_neg]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((cosLoNLag (highAbs A) : ℚ) : ℝ) ≤ Real.cos x
      have hq : |(((highAbs A : ℚ)) : ℝ)| ≤ 1 := by rw [abs_of_nonneg hM0]; exact hM1
      have hspec := cosLoNLag_le_cos (q := highAbs A)
      have hdec : Real.cos (((highAbs A : ℚ)) : ℝ) ≤ Real.cos x := by
        rw [← hcosabs]
        exact cos_le_cos_of_le_on_unit (abs_nonneg x) hM1 hxM
      exact le_trans hspec hdec
    · show Real.cos x ≤ ((cosHiNLag (lowAbs A) : ℚ) : ℝ)
      have hq : |(((lowAbs A : ℚ)) : ℝ)| ≤ 1 := by rw [abs_of_nonneg hm0]; exact hm1
      have hspec := cos_le_cosHiNLag (q := lowAbs A)
      have hdec : Real.cos x ≤ Real.cos (((lowAbs A : ℚ)) : ℝ) := by
        rw [← hcosabs]
        exact cos_le_cos_of_le_on_unit hm0 hx1 hmx
      exact le_trans hdec hspec
  · rw [if_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-- 阶乘版 `sin`/`cos` 沿 `+π/2` 步进的逐格区间对。 -/
def phasePosLag (A : RatInterval) : ℕ → RatInterval × RatInterval
  | 0 => (sinIHighLag A, cosWinLag A)
  | n + 1 => ((phasePosLag A n).2, (phasePosLag A n).1.neg)

/-- 阶乘版 `sin`/`cos` 沿 `−π/2` 步进的逐格区间对。 -/
def phaseNegLag (A : RatInterval) : ℕ → RatInterval × RatInterval
  | 0 => (sinIHighLag A, cosWinLag A)
  | n + 1 => ((phaseNegLag A n).2.neg, (phaseNegLag A n).1)

theorem phasePosLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    ∀ n : ℕ, ((phasePosLag A n).1).Mem (Real.sin (x + (n : ℝ) * (Real.pi / 2))) ∧
      ((phasePosLag A n).2).Mem (Real.cos (x + (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (sinIHighLag A).Mem (Real.sin (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using sinIHighLag_mem hA
    · show (cosWinLag A).Mem (Real.cos (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using cosWinLag_mem hA
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show ((phasePosLag A n).2).Mem (Real.sin (x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x + (n : ℝ) * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring,
        Real.sin_add_pi_div_two]
      exact ih.2
    · show (((phasePosLag A n).1).neg).Mem (Real.cos (x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x + (n : ℝ) * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring,
        Real.cos_add_pi_div_two]
      exact neg_mem ih.1

theorem phaseNegLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    ∀ n : ℕ, ((phaseNegLag A n).1).Mem (Real.sin (x - (n : ℝ) * (Real.pi / 2))) ∧
      ((phaseNegLag A n).2).Mem (Real.cos (x - (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (sinIHighLag A).Mem (Real.sin (x - ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using sinIHighLag_mem hA
    · show (cosWinLag A).Mem (Real.cos (x - ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using cosWinLag_mem hA
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show (((phaseNegLag A n).2).neg).Mem (Real.sin (x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x - (n : ℝ) * (Real.pi / 2)) - Real.pi / 2 by push_cast; ring,
        sin_sub_pi_div_two']
      exact neg_mem ih.2
    · show ((phaseNegLag A n).1).Mem (Real.cos (x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x - (n : ℝ) * (Real.pi / 2)) - Real.pi / 2 by push_cast; ring,
        cos_sub_pi_div_two']
      exact ih.1

/-- 阶乘版按符号选相位。 -/
def phaseBothLag (A : RatInterval) (k : ℤ) : RatInterval × RatInterval :=
  if 0 ≤ k then phasePosLag A k.toNat else phaseNegLag A (-k).toNat

theorem phaseBothLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) (k : ℤ) :
    ((phaseBothLag A k).1).Mem (Real.sin (x + (k : ℝ) * (Real.pi / 2))) ∧
      ((phaseBothLag A k).2).Mem (Real.cos (x + (k : ℝ) * (Real.pi / 2))) := by
  unfold phaseBothLag
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    rcases int_split_nat k with ⟨hk0, hkeq⟩ | ⟨hk0, hkeq⟩
    · constructor
      · rw [show x + (k : ℝ) * (Real.pi / 2)
            = x + ((k.toNat : ℕ) : ℝ) * (Real.pi / 2) from by rw [int_cast_toNat hkeq]]
        exact (phasePosLag_mem hA k.toNat).1
      · rw [show x + (k : ℝ) * (Real.pi / 2)
            = x + ((k.toNat : ℕ) : ℝ) * (Real.pi / 2) from by rw [int_cast_toNat hkeq]]
        exact (phasePosLag_mem hA k.toNat).2
    · have hkz : k = 0 := le_antisymm hk0 hk
      subst hkz
      refine ⟨?_, ?_⟩
      · show (sinIHighLag A).Mem (Real.sin (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
        simpa using sinIHighLag_mem hA
      · show (cosWinLag A).Mem (Real.cos (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
        simpa using cosWinLag_mem hA
  · rw [if_neg hk]
    have hklt : k < 0 := not_le.mp hk
    have hnat : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (neg_pos.mpr hklt).le
    have hcast : (k : ℝ) = -(((-k).toNat : ℕ) : ℝ) := by
      have h := congrArg (fun m : ℤ => (m : ℝ)) (show k = -((((-k).toNat : ℕ) : ℤ)) by
        rw [hnat]; ring)
      rw [Int.cast_neg, Int.cast_natCast] at h
      exact h
    constructor
    · rw [show x + (k : ℝ) * (Real.pi / 2) = x - (((-k).toNat : ℕ) : ℝ) * (Real.pi / 2) from by
        rw [hcast]; ring]
      exact (phaseNegLag_mem hA (-k).toNat).1
    · rw [show x + (k : ℝ) * (Real.pi / 2) = x - (((-k).toNat : ℕ) : ℝ) * (Real.pi / 2) from by
        rw [hcast]; ring]
      exact (phaseNegLag_mem hA (-k).toNat).2

/-- 阶乘版归约相位格。 -/
def phaseRedLag (A : RatInterval) : RatInterval × RatInterval :=
  phaseBothLag (reducedBox A (phaseOf A)) (phaseOf A)

/-- 阶乘版 `sin` 总算子。 -/
def sinTotLag (A : RatInterval) : RatInterval := by
  classical
  exact if h : inWindow A (phaseOf A) then (phaseRedLag A).1 else intv (-1) 1

/-- 阶乘版 `cos` 总算子。 -/
def cosTotLag (A : RatInterval) : RatInterval := by
  classical
  exact if h : inWindow A (phaseOf A) then (phaseRedLag A).2 else intv (-1) 1

theorem sinTotLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (sinTotLag A).Mem (Real.sin x) := by
  classical
  have hkey : x = (x - (phaseOf A : ℝ) * (Real.pi / 2)) + (phaseOf A : ℝ) * (Real.pi / 2) := by
    ring
  unfold sinTotLag
  by_cases h : inWindow A (phaseOf A)
  · rw [dif_pos h, hkey]
    exact (phaseBothLag_mem (A := reducedBox A (phaseOf A)) (reducedBox_mem h hA) (phaseOf A)).1
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.sin x
      push_cast
      exact neg_one_le_sin x
    · show Real.sin x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact sin_le_one' x

theorem cosTotLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (cosTotLag A).Mem (Real.cos x) := by
  classical
  have hkey : x = (x - (phaseOf A : ℝ) * (Real.pi / 2)) + (phaseOf A : ℝ) * (Real.pi / 2) := by
    ring
  unfold cosTotLag
  by_cases h : inWindow A (phaseOf A)
  · rw [dif_pos h, hkey]
    exact (phaseBothLag_mem (A := reducedBox A (phaseOf A)) (reducedBox_mem h hA) (phaseOf A)).2
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-- 阶乘版窗口内接口引理（读数用）。 -/
theorem sinTotLag_of_inWindow {A : RatInterval} (h : inWindow A (phaseOf A)) :
    sinTotLag A = (phaseRedLag A).1 := by
  classical
  unfold sinTotLag
  exact dif_pos h

theorem cosTotLag_of_inWindow {A : RatInterval} (h : inWindow A (phaseOf A)) :
    cosTotLag A = (phaseRedLag A).2 := by
  classical
  unfold cosTotLag
  exact dif_pos h

end RatInterval

open RatInterval

/-- 阶乘版 `rhoK` 区间（表达式树与 `rhoInterval` 逐节点相同）。 -/
def rhoIntervalLag (q : Fin 12 → ℚ) (k : Fin 9) : RatInterval :=
  sub (cosTotLag ((angleVecInterval q) k))
    (sqrt (sub (sq (ofRat (q 6))) (sq (sinTotLag ((angleVecInterval q) k)))))

/-- 阶乘版 `ringCenter` 区间。 -/
def ringCenterIntervalLag (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => mul (rhoIntervalLag q k) (cosTotLag ((thetaInterval (angleVecInterval q)) k))
  | 1 => mul (rhoIntervalLag q k) (sinTotLag ((thetaInterval (angleVecInterval q)) k))

/-- 阶乘版 `arcEnd` 区间。 -/
def arcEndIntervalLag (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => cosTotLag (add ((thetaInterval (angleVecInterval q)) k) ((angleVecInterval q) k))
  | 1 => sinTotLag (add ((thetaInterval (angleVecInterval q)) k) ((angleVecInterval q) k))

/-- 阶乘版 `Uvec` 区间。 -/
def UvecIntervalLag (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => sub (add ((ringCenterIntervalLag q k) 0) ((ringCenterIntervalLag q (k + 1)) 0))
      ((arcEndIntervalLag q k) 0)
  | 1 => sub (add ((ringCenterIntervalLag q k) 1) ((ringCenterIntervalLag q (k + 1)) 1))
      ((arcEndIntervalLag q k) 1)

/-- 阶乘版 `wPoint` 区间。 -/
def wPointIntervalLag (q : Fin 12 → ℚ) : Fin 2 → RatInterval
  | 0 => mul (ofRat (1 / 2)) (add (ofRat (q 4)) (ofRat (q 5)))
  | 1 => sqrt (sub (sq (ofRat (q 6)))
      (sq (mul (ofRat (1 / 2)) (sub (ofRat (q 5)) (ofRat (q 4))))))

/-- **阶乘版残差包络** `Fm`（高阶入口）。 -/
def residualIntervalLag (q : Fin 12 → ℚ) : Fin 5 → RatInterval
  | 0 => sub (distInterval (UvecIntervalLag q 1) (hub1Interval q)) (ofRat (q 6))
  | 1 => sub (distInterval (UvecIntervalLag q 2) (hub0Interval q)) (ofRat (q 6))
  | 2 => sub (distInterval (UvecIntervalLag q 3) (hub0Interval q)) (ofRat (q 6))
  | 3 => sub (distInterval (UvecIntervalLag q 8) (hub1Interval q)) (ofRat (q 6))
  | 4 => sub (distInterval (wPointIntervalLag q) (ringCenterIntervalLag q 6)) (ofRat (q 6))

theorem rhoIntervalLag_mem (q : Fin 12 → ℚ) (k : Fin 9) :
    ((rhoIntervalLag q k)).Mem (rhoK (fun i => ((q i : ℚ) : ℝ)) k) := by
  rw [rhoK_eq]
  exact sub_mem (cosTotLag_mem (angleVecInterval_mem q k))
    (sqrt_mem (sub_mem (sq_mem_pow (ofRat_mem (q 6)))
      (sq_mem_pow (sinTotLag_mem (angleVecInterval_mem q k)))))

theorem ringCenterIntervalLag_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((ringCenterIntervalLag q k) i).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show ((rhoIntervalLag q k).mul (cosTotLag ((thetaInterval (angleVecInterval q)) k))).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [ringCenter_coord0]
    exact mul_mem (rhoIntervalLag_mem q k)
      (cosTotLag_mem (thetaInterval_mem (angleVecInterval_mem q) k))
  · show ((rhoIntervalLag q k).mul (sinTotLag ((thetaInterval (angleVecInterval q)) k))).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [ringCenter_coord1]
    exact mul_mem (rhoIntervalLag_mem q k)
      (sinTotLag_mem (thetaInterval_mem (angleVecInterval_mem q) k))

theorem arcEndIntervalLag_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((arcEndIntervalLag q k) i).Mem ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show (cosTotLag ((thetaInterval (angleVecInterval q) k).add ((angleVecInterval q) k))).Mem
      ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [arcEnd_coord0]
    exact cosTotLag_mem (add_mem (thetaInterval_mem (angleVecInterval_mem q) k)
      (angleVecInterval_mem q k))
  · show (sinTotLag ((thetaInterval (angleVecInterval q) k).add ((angleVecInterval q) k))).Mem
      ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [arcEnd_coord1]
    exact sinTotLag_mem (add_mem (thetaInterval_mem (angleVecInterval_mem q) k)
      (angleVecInterval_mem q k))

theorem UvecIntervalLag_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((UvecIntervalLag q k) i).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show (sub (add ((ringCenterIntervalLag q k) 0) ((ringCenterIntervalLag q (k + 1)) 0))
      ((arcEndIntervalLag q k) 0)).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [Uvec_coord0]
    exact sub_mem (add_mem (ringCenterIntervalLag_mem q k 0)
      (ringCenterIntervalLag_mem q (k + 1) 0)) (arcEndIntervalLag_mem q k 0)
  · show (sub (add ((ringCenterIntervalLag q k) 1) ((ringCenterIntervalLag q (k + 1)) 1))
      ((arcEndIntervalLag q k) 1)).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [Uvec_coord1]
    exact sub_mem (add_mem (ringCenterIntervalLag_mem q k 1)
      (ringCenterIntervalLag_mem q (k + 1) 1)) (arcEndIntervalLag_mem q k 1)

theorem wPointIntervalLag_mem (q : Fin 12 → ℚ) (i : Fin 2) :
    ((wPointIntervalLag q) i).Mem ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp i) := by
  fin_cases i
  · show (mul (ofRat (1 / 2)) (add (ofRat (q 4)) (ofRat (q 5)))).Mem
      ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp 0)
    rw [wPoint_coord0]
    have h : ((((q 4 : ℚ) : ℝ) + ((q 5 : ℚ) : ℝ)) / 2)
        = (((1 / 2 : ℚ) : ℝ) * (((q 4 : ℚ) : ℝ) + ((q 5 : ℚ) : ℝ))) := by
      push_cast; ring
    rw [h]
    exact mul_mem (ofRat_mem (1 / 2)) (add_mem (ofRat_mem (q 4)) (ofRat_mem (q 5)))
  · show (sqrt (sub (sq (ofRat (q 6)))
      (sq (mul (ofRat (1 / 2)) (sub (ofRat (q 5)) (ofRat (q 4))))))).Mem
      ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp 1)
    rw [wPoint_coord1]
    have h : ((((q 5 : ℚ) : ℝ) - ((q 4 : ℚ) : ℝ)) / 2)
        = (((1 / 2 : ℚ) : ℝ) * (((q 5 : ℚ) : ℝ) - ((q 4 : ℚ) : ℝ))) := by
      push_cast; ring
    rw [h]
    exact sqrt_mem (sub_mem (sq_mem_pow (ofRat_mem (q 6)))
      (sq_mem_pow (mul_mem (ofRat_mem (1 / 2)) (sub_mem (ofRat_mem (q 5)) (ofRat_mem (q 4))))))

/-- **阶乘版包含性主定理（任意 `q`，无条件）**。 -/
theorem mem_residualIntervalLag (q : Fin 12 → ℚ) (k : Fin 5) :
    ((residualIntervalLag q k)).Mem (residual (fun i => ((q i : ℚ) : ℝ)) k) := by
  fin_cases k
  · exact sub_mem (distInterval_mem (fun i => UvecIntervalLag_mem q 1 i)
      (fun i => hub1Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecIntervalLag_mem q 2 i)
      (fun i => hub0Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecIntervalLag_mem q 3 i)
      (fun i => hub0Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecIntervalLag_mem q 8 i)
      (fun i => hub1Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => wPointIntervalLag_mem q i)
      (fun i => ringCenterIntervalLag_mem q 6 i)) (ofRat_mem (q 6))

/-- **阶乘版实例化（残差版）**。 -/
theorem mem_residualIntervalLag_cCert_residual (k : Fin 5) :
    ((residualIntervalLag cCert k)).Mem (residual cCertR k) :=
  mem_residualIntervalLag cCert k

/-- **阶乘版实例化（`TCSystem` 版）**。 -/
theorem mem_residualIntervalLag_cCert (k : Fin 5) :
    ((residualIntervalLag cCert k)).Mem (TCSystem cCertR ⟨(k : ℕ), by omega⟩) := by
  rw [TCSystem_first]
  exact mem_residualIntervalLag_cCert_residual k

theorem mem_residualIntervalLag_cCert_TCSystem (k : Fin 5) :
    ((residualIntervalLag cCert k)).Mem (TCSystem cCertR ⟨(k : ℕ), by omega⟩) :=
  mem_residualIntervalLag_cCert k
end N11Formalization
