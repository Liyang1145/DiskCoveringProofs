/-
  evidence/f1-step2/F1-BallD35-C8.lean
  ====================================

  **F1 第 2 步 · 步骤 (a)：把 `ndJT_res_z_box` 从**条件式**升级为**无条件**** ✓✓

  **普查结论（本次"先查根 cone"的第四次收成）** ✓✓：**(a) 所需的**每一个**前提在根 cone 内**已有****：
  | 前提 | 根内现成件 |
  |---|---|
  | `hrho`：`∀ j, Wfun j z ≠ 0` | **`wkBox_pos j`**（9 个 j 全覆盖）+ **`wkBox_mem hx j`** ✓ |
  | `hradW`：`WpAt z ≠ 0` | **`WpIvBox_pos`** + **`WpIvBox_mem hx`** + `WpAt_eq_WpReal` ✓ |
  | `hU1..hU8`、`wPoint ≠ ringCenter 6` | **`nd_all_via_dist`**（一条五元合取，`∀ x ∈ ball`）✓✓ |
  | `hg`：`dist` 侧 radicand `≠ 0` | **`radIvBox_pos k`** + **`radIvBox_mem k hx`**（**与 `hg` 的表达式逐字同形** ✓） |
  | `hresid`：`residualFun` 在 `z` 可微 | **`contDiffAt_residualFun z hrho hradW hU1 hU2 hU3 hU8 hW i`**（`SmoothnessC2`）✓ |

  **⇒ 本片是**纯装配**：无新数学、零重推；每条都是"`Mem` + `lo > 0` ⇒ `≠ 0`"（`linarith` 级）✓。**

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C7
import N11Formalization.SmoothnessC2
import N11Formalization.NondegProof

/-! ## 0. **外部名自查前言**（Lead R238 过程口径） -/
#check @N11Formalization.wkBox_pos
#check @N11Formalization.wkBox_mem
#check @N11Formalization.WpIvBox_pos
#check @N11Formalization.WpIvBox_mem
#check @N11Formalization.radIvBox_pos
#check @N11Formalization.radIvBox_mem
#check @N11Formalization.nd_all_via_dist
#check @N11Formalization.contDiffAt_residualFun
#check @N11Formalization.ndJT_res_z_box
#check @N11Formalization.WpAt_eq_WpReal
#check @N11Formalization.Wfun
#check @N11Formalization.WpReal
#check @N11Formalization.pad12_six
#check @N11Formalization.pad12_five
#check @N11Formalization.pad12_four

noncomputable section

namespace N11Formalization

/-! ## 1. 三个盒的 `≠ 0`（`Mem` + `lo > 0` ⇒ `≠ 0`） -/

theorem wkBox_ne_zero {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) (j : Fin 9) :
    x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j) ≠ 0 := by
  intro hz
  have h1 : (((wkBox j).lo : ℚ) : ℝ)
      ≤ x 6 * x 6 - Real.sin (angleVec x j) * Real.sin (angleVec x j) :=
    (wkBox_mem hx j).1
  have h2 : (0 : ℝ) < (((wkBox j).lo : ℚ) : ℝ) := by exact_mod_cast wkBox_pos j
  rw [hz] at h1
  linarith

theorem WpReal_ne_zero_of_ball {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    WpReal x ≠ 0 := by
  intro hz
  have h1 : ((WpIvBox.lo : ℚ) : ℝ) ≤ WpReal x := (WpIvBox_mem hx).1
  have h2 : (0 : ℝ) < ((WpIvBox.lo : ℚ) : ℝ) := by exact_mod_cast WpIvBox_pos
  rw [hz] at h1
  linarith

theorem radIvBox_ne_zero_of_ball (k : Fin 5) {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
      + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2 ≠ 0 := by
  intro hz
  have h1 : ((radIvBox k).lo : ℝ)
      ≤ (((Apt k) x).ofLp 0 - ((Bpt k) x).ofLp 0) ^ 2
        + (((Apt k) x).ofLp 1 - ((Bpt k) x).ofLp 1) ^ 2 :=
    (radIvBox_mem k hx).1
  have h2 : (0 : ℚ) < (radIvBox k).lo := radIvBox_pos k
  have h2' : (0 : ℝ) < ((radIvBox k).lo : ℝ) := by exact_mod_cast h2
  rw [hz] at h1
  linarith

/-! ## 2. 三个前提的**球上**版本（改写 `pad12`/`pow_two`/`WpReal`） -/

theorem Wfun_ne_zero_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) (j : Fin 9) : Wfun j z ≠ 0 := by
  have h := wkBox_ne_zero hz j
  rw [pad12_six z] at h
  rw [Wfun, pow_two (z 6), pow_two (Real.sin (angleVec (pad12 z) j))]
  exact h

theorem WpAt_ne_zero_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) : WpAt z ≠ 0 := by
  rw [WpAt_eq_WpReal z]
  exact WpReal_ne_zero_of_ball hz

theorem hrho_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    ∀ j : Fin 9, ((pad12 z) 6) ^ 2 - (Real.sin (angleVec (pad12 z) j)) ^ 2 ≠ 0 := by
  intro j
  have h := wkBox_ne_zero hz j
  rw [pow_two ((pad12 z) 6), pow_two (Real.sin (angleVec (pad12 z) j))]
  exact h

theorem hradW_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    ((pad12 z) 6) ^ 2 - (((pad12 z) 5 - (pad12 z) 4) / 2) ^ 2 ≠ 0 := by
  have h := WpReal_ne_zero_of_ball hz
  rw [WpReal] at h
  exact h

/-- **`residualFun` 在 `z` 处可微（球上无条件）**：由 `contDiffAt_residualFun` 逐分量 + `differentiableAt_pi`。 -/
theorem differentiableAt_residualFun_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    DifferentiableAt ℝ residualFun z := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hres : ∀ i : Fin 5, DifferentiableAt ℝ (fun w : Fin 7 → ℝ => residualFun w i) z :=
    fun i => (contDiffAt_residualFun (n := ⊤) z (hrho_of_ball z hz) (hradW_of_ball z hz)
      (hU1 (pad12 z) hz) (hU2 (pad12 z) hz) (hU3 (pad12 z) hz) (hU8 (pad12 z) hz)
      (hWpne (pad12 z) hz) i).differentiableAt (by simp)
  exact differentiableAt_pi.mpr hres

/-! ## 3. **收口（无条件）** ✓✓✓ -/

/-- **F1 第 2 步收口·无条件版**：球级 35 格对**真 `fderiv`** 的 `Mem`，
**全部前提已由盒上正性族 + `nd_all_via_dist` 供给** ✓✓。 -/
theorem ndJT_res_z_box_uncond (k : Fin 5) (i : Fin 7) (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    (compIvBox k i).Mem ((fderiv ℝ residualFun z (Pi.single i 1)) k) :=
  ndJT_res_z_box k i z hz (differentiableAt_residualFun_of_ball z hz)
    (fun j => Wfun_ne_zero_of_ball z hz j) (WpAt_ne_zero_of_ball z hz)
    (radIvBox_ne_zero_of_ball k hz)

end N11Formalization

#print axioms N11Formalization.wkBox_ne_zero
#print axioms N11Formalization.WpReal_ne_zero_of_ball
#print axioms N11Formalization.radIvBox_ne_zero_of_ball
#print axioms N11Formalization.hrho_of_ball
#print axioms N11Formalization.hradW_of_ball
#print axioms N11Formalization.differentiableAt_residualFun_of_ball
#print axioms N11Formalization.ndJT_res_z_box_uncond
