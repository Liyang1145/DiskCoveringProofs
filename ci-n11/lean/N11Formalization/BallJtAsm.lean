import N11Formalization.F1.BallD35C14
import N11Formalization.F1.BallD35C11

/-!
# Lead scratch：**球级 `Jt'`（盒表版）＋ 4 条块引理 ＋ `hJ` 条件完整装配**

（**合并件**：scratch 件不可被 import ⇒ `Jt'` 的定义、块引理、装配必须同文件 ✓ —— 本会话已踩过同一坑 ✓。）

**依据**：
* `F1/BallD35C14` 件头 L20–21 的**项目自裁 (乙)**：球级 `Jt'` **自建** = `compIvBox` 残差块 + λ 块 + `Hess` 块 ✓
* 中心版 `D`（`ResidualDerivD` L619 ✓）各行**就是 `compIv` 家族** ⇒ **盒版取 `DBox := compIvBox`，不必新造表** ✓

**四支的球级依据（均已在锥 ✓）**：
| 支 | 依据 |
|---|---|
| 残差行 × z | `F1/BallD35C14.mem_Jt_res_z_ball_all_x x hx` ✓（与 `Jt'_res_z` 直接对接 ✓） |
| 残差行 × λ | `F1/BallD35C12.fderiv_TCSystem_res_lam_any_x` ✓ ⇒ `(ofRat 0).Mem 0` ✓ |
| KKT 行 × λ | `F1/BallD35C11.JT_kkt_lam_all` ✓ ＋ `neg_mem` ＋ 同一条 z 重写 ✓ |
| **KKT 行 × z** | ✗ **49 格** ⇒ 本件作**具名假设** `hKKTz` ✓（`tower-bc` 的 `d2xIvBox_mem`/`d2yIvBox_mem` 落根 ⇒ 一行实例化 ✓） |

⚠ `hadj`（一般点的 `fderiv residualFun` 可微性）暂作**参数** ✓（DEAD §59：属簿记切分 ✓；可由光滑性推出 ⇒ 待消除 ✓）。
判据：**exit=0 且输出 0 行**。
-/

namespace N11Formalization.Lead.JtBall

open N11Formalization

/-- **球级 `Jt'`**（盒表版）。 -/
noncomputable def Jt' (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (r c : Fin 12) : RatInterval :=
  if hr : (r : ℕ) < 5 then
    if hc : (c : ℕ) < 7 then compIvBox ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
    else RatInterval.ofRat 0
  else
    if hc : (c : ℕ) < 7 then
      RatInterval.neg (RatInterval.dot lamRat (Hess ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩))
    else
      RatInterval.neg (compIvBox ⟨(c : ℕ) - 7, by omega⟩ ⟨(r : ℕ) - 5, by omega⟩)

/-- 块 1（残差行 × z 列）。 -/
theorem Jt'_res_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (j : Fin 7) :
    Jt' Hess (row5 k) (up7 j) = compIvBox k j := by
  simp only [Jt']
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [mk_row5, mk_up7]

/-- 块 2（残差行 × λ 列）：恒 `[0,0]`。 -/
theorem Jt'_res_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (m : Fin 5) :
    Jt' Hess (row5 k) (up5 m) = RatInterval.ofRat 0 := by
  simp only [Jt']
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]

/-- 块 3（KKT 行 × z 列）：唯一二阶块。 -/
theorem Jt'_kkt_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i j : Fin 7) :
    Jt' Hess (kkt12 i) (up7 j)
      = RatInterval.neg (RatInterval.dot lamRat (Hess i j)) := by
  simp only [Jt']
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [sub5_kkt12, mk_up7]

/-- 块 4（KKT 行 × λ 列）：盒版转置。 -/
theorem Jt'_kkt_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i : Fin 7) (m : Fin 5) :
    Jt' Hess (kkt12 i) (up5 m) = RatInterval.neg (compIvBox m i) := by
  simp only [Jt']
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]
  simp only [sub7_up5, sub5_kkt12]

/-- **球级 `hJ` 装配（条件完整）**：以 49 格 KKT×z 的包络为假设 ⇒ 消费点需要的**球级 `hJ`** ✓。 -/
theorem mem_Jt'_ball_cond (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hadj : ∀ x : Fin 12 → ℝ, x ∈ Metric.closedBall certCR rhoCertR →
      DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x))
    (hKKTz : ∀ x : Fin 12 → ℝ, x ∈ Metric.closedBall certCR rhoCertR → ∀ i j : Fin 7,
      (RatInterval.neg (RatInterval.dot lamRat (Hess i j))).Mem
        ((fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (kkt12 i)))
    (x : Fin 12 → ℝ) (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ r c : Fin 12, (Jt' Hess r c).Mem ((fderiv ℝ TCSystem x (Pi.single c 1)) r) := by
  intro r c
  have hdT : DifferentiableAt ℝ TCSystem x := differentiableAt_TCSystem_ball hx
  have hd : DifferentiableAt ℝ residualFun (first7 x) := differentiableAt_residualFun_first7_ball hx
  by_cases hr : (r : ℕ) < 5
  · have hrw : r = row5 ⟨(r : ℕ), hr⟩ := by apply Fin.ext; simp only [row5]
    rw [hrw]
    by_cases hc : (c : ℕ) < 7
    · have hcw : c = up7 ⟨(c : ℕ), hc⟩ := by apply Fin.ext; simp only [up7]
      rw [hcw, Jt'_res_z]
      exact (mem_Jt_res_z_ball_all_x x hx) ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
    · have hcw : c = up5 ⟨(c : ℕ) - 7, by omega⟩ := by
        apply Fin.ext; simp only [up5]; omega
      rw [hcw, Jt'_res_lam]
      rw [fderiv_TCSystem_res_lam_any_x x hdT hd ⟨(r : ℕ), hr⟩ ⟨(c : ℕ) - 7, by omega⟩]
      simpa using RatInterval.ofRat_mem (0 : ℚ)
  · have hr5 : 5 ≤ (r : ℕ) := by omega
    have hrw : r = kkt12 ⟨(r : ℕ) - 5, by omega⟩ := by
      apply Fin.ext; simp only [kkt12]; omega
    rw [hrw]
    by_cases hc : (c : ℕ) < 7
    · have hcw : c = up7 ⟨(c : ℕ), hc⟩ := by apply Fin.ext; simp only [up7]
      rw [hcw, Jt'_kkt_z]
      exact hKKTz x hx ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩
    · have hcw : c = up5 ⟨(c : ℕ) - 7, by omega⟩ := by
        apply Fin.ext; simp only [up5]; omega
      rw [hcw, Jt'_kkt_lam]
      rw [JT_kkt_lam_all x hdT (hadj x hx) ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ) - 7, by omega⟩]
      refine RatInterval.neg_mem ?_
      have hz := (mem_Jt_res_z_ball_all_x x hx) ⟨(c : ℕ) - 7, by omega⟩ ⟨(r : ℕ) - 5, by omega⟩
      rwa [fderiv_TCSystem_res_z_any_x x hdT hd ⟨(c : ℕ) - 7, by omega⟩
        ⟨(r : ℕ) - 5, by omega⟩] at hz

end N11Formalization.Lead.JtBall
