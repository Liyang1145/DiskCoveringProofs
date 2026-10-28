/-
  evidence/f1-step2/F1-BallD35-C14.lean
  =====================================

  **F1 第 2 步 · `*Real` transport 族 + z 侧 35 格落格** ✓✓

  Lead 裁决（实测）：`dUxReal`/`dUyReal` 的使用者只有 `F1/BallD35C6/C7/Hrad`；
  `hessEntry`（`ResidualDerivJT` L345 定义）**与该族无关** ⇒ **不与 H3/Hess 共享 ⇒ 由我写** ✓。

  **链条（全机械，从 `Transport` 的 point 级族派生）**：
  `drhoReal_transport`（用 `angleVec_transport` + `pad12_first7_6`，**同 `rhoK_transport` L51 的写法** ✓）
  → `ring0/1Real_transport`（+ `rhoK_transport`/`thetaOf_transport`）
  → `arc0/1Real_transport`（+ `thetaOf_transport`/`angleVec_transport`）
  → `dUvec0/1Real_transport`
  → **`dUxReal`/`dUyReal_transport`**（+ `coord`/`Pi.single`，与 `u` 无关 ✓）

  **⇒ 收口**：z 侧 35 格落格（`mem_Jt_res_z_ball_x`），与 C13 的 λ 侧 25 格合成
  **`mem_Jt_res_row_all_x`（残差行 60 格，消费方形状、无条件）** ✓✓

  **件头接口记录（Lead ④）**：组装球级 `Jt'` 时按 **(乙)** 推进（自建 `Jt'` = `compIvBox` 残差块 + λ 块 + `Hess` 块），
  ⇒ `hsum`/`hsumR` 需对 `Jt'` **再实例化**（`K` 可能变大 ✗）；**(甲)/(乙) 最终取舍由 Lead 裁**（取决于 `root-audit` 的真实 `J` 数）✓。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C13
import N11Formalization.Transport

/-! ## 0. 外部名自查前言（Lead R238 过程口径；每条实测存在） -/
#check @N11Formalization.drhoReal
#check @N11Formalization.ring0Real
#check @N11Formalization.ring1Real
#check @N11Formalization.arc0Real
#check @N11Formalization.arc1Real
#check @N11Formalization.dUvec0Real
#check @N11Formalization.dUvec1Real
#check @N11Formalization.dUxReal
#check @N11Formalization.dUyReal
#check @N11Formalization.rhoK_transport
#check @N11Formalization.thetaOf_transport
#check @N11Formalization.angleVec_transport
#check @N11Formalization.pad12_first7_6

noncomputable section

namespace N11Formalization

/-! ## 1. `drhoReal` -/

theorem drhoReal_transport (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) :
    drhoReal (pad12 (first7 x)) j i = drhoReal x j i := by
  simp only [drhoReal, angleVec_transport x, pad12_first7_6]

/-! ## 2. `ring0Real` / `ring1Real` -/

theorem ring0Real_transport (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) :
    ring0Real (pad12 (first7 x)) j i = ring0Real x j i := by
  simp only [ring0Real, rhoK_transport x, angleVec_transport x, drhoReal_transport x]

theorem ring1Real_transport (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) :
    ring1Real (pad12 (first7 x)) j i = ring1Real x j i := by
  simp only [ring1Real, rhoK_transport x, angleVec_transport x, drhoReal_transport x]

/-! ## 3. `arc0Real` / `arc1Real` -/

theorem arc0Real_transport (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) :
    arc0Real (pad12 (first7 x)) j i = arc0Real x j i := by
  simp only [arc0Real, angleVec_transport x]

theorem arc1Real_transport (x : Fin 12 → ℝ) (j : Fin 9) (i : Fin 7) :
    arc1Real (pad12 (first7 x)) j i = arc1Real x j i := by
  simp only [arc1Real, angleVec_transport x]

/-! ## 4. `dUvec0Real` / `dUvec1Real` -/

theorem dUvec0Real_transport (x : Fin 12 → ℝ) (k : Fin 9) (i : Fin 7) :
    dUvec0Real (pad12 (first7 x)) k i = dUvec0Real x k i := by
  simp only [dUvec0Real, ring0Real_transport x, arc0Real_transport x]

theorem dUvec1Real_transport (x : Fin 12 → ℝ) (k : Fin 9) (i : Fin 7) :
    dUvec1Real (pad12 (first7 x)) k i = dUvec1Real x k i := by
  simp only [dUvec1Real, ring1Real_transport x, arc1Real_transport x]

/-! ## 5. **`dUxReal` / `dUyReal`** -/

theorem dUxReal_transport (k : Fin 5) (i : Fin 7) (x : Fin 12 → ℝ) :
    dUxReal k i (pad12 (first7 x)) = dUxReal k i x := by
  match k with
  | 0 => simp only [dUxReal, dUvec0Real_transport x]
  | 1 => simp only [dUxReal, dUvec0Real_transport x]
  | 2 => simp only [dUxReal, dUvec0Real_transport x]
  | 3 => simp only [dUxReal, dUvec0Real_transport x]
  | 4 => simp only [dUxReal, ring0Real_transport x]

theorem dUyReal_transport (k : Fin 5) (i : Fin 7) (x : Fin 12 → ℝ) :
    dUyReal k i (pad12 (first7 x)) = dUyReal k i x := by
  match k with
  | 0 => simp only [dUyReal, dUvec1Real_transport x]
  | 1 => simp only [dUyReal, dUvec1Real_transport x]
  | 2 => simp only [dUyReal, dUvec1Real_transport x]
  | 3 => simp only [dUyReal, dUvec1Real_transport x]
  | 4 => simp only [dUyReal, ring1Real_transport x, WpReal, pad12_first7_4, pad12_first7_5, pad12_first7_6]

/-! ## 6. **z 侧 35 格落格**（消费方形状；与 C13 的 λ 侧合起来 = 残差行 60 格） -/

set_option maxHeartbeats 1000000 in
theorem mem_Jt_res_z_ball_x (k : Fin 5) (j : Fin 7) (x : Fin 12 → ℝ)
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (compIvBox k j).Mem ((fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (row5 k)) := by
  have hdT : DifferentiableAt ℝ TCSystem x := differentiableAt_TCSystem_ball hx
  have hd : DifferentiableAt ℝ residualFun (first7 x) := differentiableAt_residualFun_first7_ball hx
  have hW : ∀ j' : Fin 9, Wfun j' (first7 x) ≠ 0 := by
    intro j'
    have h := wkBox_ne_zero hx j'
    rw [Wfun, angleVec_transport x]
    simpa only [pow_two, first7_six] using h
  have hWp : WpAt (first7 x) ≠ 0 := by
    rw [WpAt_eq_WpReal]
    simpa only [WpReal, pad12_first7_4, pad12_first7_5, pad12_first7_6]
      using WpReal_ne_zero_of_ball hx
  have hg : ((Apt k (pad12 (first7 x))).ofLp 0 - (Bpt k (pad12 (first7 x))).ofLp 0) ^ 2
      + ((Apt k (pad12 (first7 x))).ofLp 1 - (Bpt k (pad12 (first7 x))).ofLp 1) ^ 2 ≠ 0 := by
    have h := radIvBox_ne_zero_of_ball k hx
    rwa [← Apt_transport k x, ← Bpt_transport k x] at h
  rw [fderiv_TCSystem_res_z_any_x x hdT hd k j]
  rw [show (fderiv ℝ residualFun (first7 x) (Pi.single j 1)) k
      = (ContinuousLinearMap.proj k ∘SL fderiv ℝ residualFun (first7 x)) (Pi.single j 1) from rfl]
  rw [← fderiv_apply hd k]
  rw [fderiv_residual_k_any k j (first7 x) hW hWp hg]
  simp only [Apt_transport k x, Bpt_transport k x, dUxReal_transport k j x, dUyReal_transport k j x]
  exact compIvBox_mem_uncond k j hx

theorem mem_Jt_res_z_ball_all_x (x : Fin 12 → ℝ)
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ k : Fin 5, ∀ j : Fin 7,
      (compIvBox k j).Mem ((fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (row5 k)) :=
  fun k j => mem_Jt_res_z_ball_x k j x hx

/-! ## 7. **残差行 60 格**（35 区间 + 25 零）合取 -/

theorem mem_Jt_res_row_all_x (x : Fin 12 → ℝ)
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (∀ k : Fin 5, ∀ j : Fin 7,
        (compIvBox k j).Mem ((fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (row5 k)))
      ∧ (∀ k : Fin 5, ∀ m : Fin 5,
        (fderiv ℝ TCSystem x (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0) :=
  ⟨mem_Jt_res_z_ball_all_x x hx, JT_lam_res_ball_x x hx⟩

end N11Formalization

#print axioms N11Formalization.drhoReal_transport
#print axioms N11Formalization.ring0Real_transport
#print axioms N11Formalization.ring1Real_transport
#print axioms N11Formalization.arc0Real_transport
#print axioms N11Formalization.arc1Real_transport
#print axioms N11Formalization.dUvec0Real_transport
#print axioms N11Formalization.dUvec1Real_transport
#print axioms N11Formalization.dUxReal_transport
#print axioms N11Formalization.dUyReal_transport
#print axioms N11Formalization.mem_Jt_res_z_ball_x
#print axioms N11Formalization.mem_Jt_res_z_ball_all_x
#print axioms N11Formalization.mem_Jt_res_row_all_x
