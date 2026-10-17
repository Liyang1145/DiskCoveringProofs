import N11Formalization.BallJtAsm
import N11Formalization.HessSeamSmooth
import N11Formalization.KktZFderivAny
import N11Formalization.LamBox

/-!
# Lead：**球级 `Jt''`（Hess 块用 λ 盒）＋ 其装配**（**正确口径**版 ✓）

**为什么需要 `Jt''`**（R177–R182 查证 ✓）：
* `Jt'`（已落根 ✓）的 Hess 块是 `neg (dot lamRat (Hess i j))` ✗ —— `lamRat` **固定** ⇒ 只在**球心**等于 `last5` ✓
  而球级链式法则（`KktZFderivAny` ✓）给的值 = `-(Σ mm, (last5 x mm) * hessEntryAt (first7 x) i j mm)` ✗（权重随 `x` 变 ✓）
⇒ ⇒ 故球级正确块 = `neg (dotIv lamBox (Hess i j))` ✓（`lamBox` 覆盖球内 `last5 x` ✓，`LamBox.lean` 已绿 ✓）

**本件**：`Jt''`（残差/λ 块同 `Jt'` ✓；Hess 块用 λ 盒 ✓）＋ 4 条块引理 ＋ **装配**：
* 假设只留 **两样** ✓：消费点**已有的** 7 条 `hnd*`（`BoxRstar` L366–373 ✓）＋ **球级逐格 `Hess`-`Mem`**
  `hH : ∀ x ∈ closedBall certCR rhoCertR, ∀ i j mm, (Hess i j mm).Mem (hessEntryAt (first7 x) i j mm)` ✓
  ⇒ ⇒ 这**正是**两线（`tower-bc`／`d2iv-box`）逐格 `_mem` 的形状 ✓✓（不再需要 `hKKTz` ✓）
* KKT×z 支**由证明给出** ✓：链式法则 ⇒ `neg_mem` ⇒ `dotIv_mem`（`lamBox_mem` ＋ `hH`）⇒ 显式和桥 `Fin.sum_univ_five` ✓

判据：**exit=0 且输出 0 行**。写法口径：`open RatInterval`（§66.2 ✓）；`linarith` 前统一符号形态（§66.1 ✓）。
-/

namespace N11Formalization.Lead.JtBall2

open N11Formalization
open RatInterval
open N11Formalization.HessSeam
open N11Formalization.Lead.LamBox
open N11Formalization.Lead.KktZ

/-- **球级 `Jt''`**：Hess 块用 **λ 盒** ✓。 -/
noncomputable def Jt'' (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (r c : Fin 12) : RatInterval :=
  if hr : (r : ℕ) < 5 then
    if hc : (c : ℕ) < 7 then compIvBox ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
    else RatInterval.ofRat 0
  else
    if hc : (c : ℕ) < 7 then
      RatInterval.neg (dotIv lamBox (Hess ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩))
    else
      RatInterval.neg (compIvBox ⟨(c : ℕ) - 7, by omega⟩ ⟨(r : ℕ) - 5, by omega⟩)

theorem Jt''_res_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (j : Fin 7) :
    Jt'' Hess (row5 k) (up7 j) = compIvBox k j := by
  simp only [Jt'']
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [mk_row5, mk_up7]

theorem Jt''_res_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (k : Fin 5) (m : Fin 5) :
    Jt'' Hess (row5 k) (up5 m) = RatInterval.ofRat 0 := by
  simp only [Jt'']
  rw [dif_pos (show ((row5 k : Fin 12) : ℕ) < 5 from k.isLt),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]

theorem Jt''_kkt_z (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i j : Fin 7) :
    Jt'' Hess (kkt12 i) (up7 j)
      = RatInterval.neg (dotIv lamBox (Hess i j)) := by
  simp only [Jt'']
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_pos (show ((up7 j : Fin 12) : ℕ) < 7 from j.isLt)]
  simp only [sub5_kkt12, mk_up7]

theorem Jt''_kkt_lam (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval) (i : Fin 7) (m : Fin 5) :
    Jt'' Hess (kkt12 i) (up5 m) = RatInterval.neg (compIvBox m i) := by
  simp only [Jt'']
  rw [dif_neg (show ¬ ((kkt12 i : Fin 12) : ℕ) < 5 by simp),
    dif_neg (show ¬ ((up5 m : Fin 12) : ℕ) < 7 by simp)]
  simp only [sub7_up5, sub5_kkt12]

/-- `dotIvR (last5 x) (hessEntryAt (first7 x) i j)` 就是链式法则给的显式五和 ✓（桥 ✓）。 -/
theorem dotIvR_last5_hessEntryAt (x : Fin 12 → ℝ) (i j : Fin 7) :
    dotIvR (last5 x) (fun mm => hessEntryAt (first7 x) i j mm)
      = ∑ mm : Fin 5, (last5 x mm) * hessEntryAt (first7 x) i j mm := by
  rw [Fin.sum_univ_five]
  simp [dotIvR, dotIvFoldR, List.finRange, List.foldl]

/-- **球级 `hJ` 装配（正确口径 ✓）**：假设 = 7 条 `hnd*` ＋ **球级逐格 `Hess`-`Mem`** ✓。 -/
theorem mem_Jt''_ball (Hess : Fin 7 → Fin 7 → Fin 5 → RatInterval)
    (hndRho : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ Metric.closedBall certCR rhoCertR, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6)
    (hH : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ i j : Fin 7, ∀ mm : Fin 5,
      (Hess i j mm).Mem (hessEntryAt (first7 x) i j mm))
    (x : Fin 12 → ℝ) (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ r c : Fin 12, (Jt'' Hess r c).Mem ((fderiv ℝ TCSystem x (Pi.single c 1)) r) := by
  intro r c
  have hdT : DifferentiableAt ℝ TCSystem x := differentiableAt_TCSystem_ball hx
  have hd : DifferentiableAt ℝ residualFun (first7 x) := differentiableAt_residualFun_first7_ball hx
  have hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x) :=
    differentiableAt_fderiv_residualFun_ball hndRho hndW hndU1 hndU2 hndU3 hndU8 hndWp x hx
  by_cases hr : (r : ℕ) < 5
  · have hrw : r = row5 ⟨(r : ℕ), hr⟩ := by apply Fin.ext; simp only [row5]
    rw [hrw]
    by_cases hc : (c : ℕ) < 7
    · have hcw : c = up7 ⟨(c : ℕ), hc⟩ := by apply Fin.ext; simp only [up7]
      rw [hcw, Jt''_res_z]
      exact (mem_Jt_res_z_ball_all_x x hx) ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
    · have hcw : c = up5 ⟨(c : ℕ) - 7, by omega⟩ := by
        apply Fin.ext; simp only [up5]; omega
      rw [hcw, Jt''_res_lam]
      rw [fderiv_TCSystem_res_lam_any_x x hdT hd ⟨(r : ℕ), hr⟩ ⟨(c : ℕ) - 7, by omega⟩]
      simpa using RatInterval.ofRat_mem (0 : ℚ)
  · have hr5 : 5 ≤ (r : ℕ) := by omega
    have hrw : r = kkt12 ⟨(r : ℕ) - 5, by omega⟩ := by
      apply Fin.ext; simp only [kkt12]; omega
    rw [hrw]
    by_cases hc : (c : ℕ) < 7
    · have hcw : c = up7 ⟨(c : ℕ), hc⟩ := by apply Fin.ext; simp only [up7]
      rw [hcw, Jt''_kkt_z]
      rw [fderiv_TCSystem_kkt_z_any x hdT hadj ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩]
      refine RatInterval.neg_mem ?_
      have hdot := dotIv_mem (c := lamBox) (A := Hess ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩)
        (lam := last5 x) (x := fun mm => hessEntryAt (first7 x) ⟨(r : ℕ) - 5, by omega⟩
          ⟨(c : ℕ), hc⟩ mm)
        (fun mm => lamBox_mem x hx mm)
        (fun mm => hH x hx ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ), hc⟩ mm)
      rwa [dotIvR_last5_hessEntryAt] at hdot
    · have hcw : c = up5 ⟨(c : ℕ) - 7, by omega⟩ := by
        apply Fin.ext; simp only [up5]; omega
      rw [hcw, Jt''_kkt_lam]
      rw [JT_kkt_lam_all x hdT hadj ⟨(r : ℕ) - 5, by omega⟩ ⟨(c : ℕ) - 7, by omega⟩]
      refine RatInterval.neg_mem ?_
      have hz := (mem_Jt_res_z_ball_all_x x hx) ⟨(c : ℕ) - 7, by omega⟩ ⟨(r : ℕ) - 5, by omega⟩
      rwa [fderiv_TCSystem_res_z_any_x x hdT hd ⟨(c : ℕ) - 7, by omega⟩
        ⟨(r : ℕ) - 5, by omega⟩] at hz

end N11Formalization.Lead.JtBall2
