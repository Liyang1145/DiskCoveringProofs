import N11Formalization.TCSystem

/-!
# 源同一性（G0 的可核验部分）：把 `TC-ROOT-SOURCE-IDENTITY.md` 的六条逐条变成具名 kernel 引理

`TC-ROOT-SOURCE-IDENTITY.md` 声称 `tc_s32_kraw.py:res5`（证书实际使用的表达式树）与源文 §2 的
几何定义**是同一个函数**，依据是"逐赋值结构化归纳"。该文件当时只做了**数值**验证
（12/12 落在 `F_center` 的 1e-56 级包络内）。本文件把其中**可机械核验的部分** kernel 化：

| 源文/身份文件的条款 | 本文件的 kernel 声明 |
|---|---|
| ① `a4 = π − 2(a0+a1+a2+a3)`，九槽回文表 | `angleVec_0` … `angleVec_8`，`angleVec_four` |
| ② `ρ_k = cos a_k − √(R² − sin² a_k)` | `rhoK_eq` |
| ③ `θ₄ = 0`，两个方向的递推 | `thetaOf_four`，`thetaOf_rec`（`TCSystem.lean`） |
| ④ `C_k`、`B_k`、`U_k = C_k + C_{k+1} − B_k`（下标模 9） | `ringCenter_coord0/1`、`arcEnd_coord0/1`、`Uvec_coord0/1`、**`fin9_succ_val`** |
| ⑤ 四条残差的**顺序** `(U1,H1),(U2,H0),(U3,H0),(U8,H1)` | `residual_comp_0` … `residual_comp_3` |
| ⑥ `m=(y0+y1)/2`、`d=(y1−y0)/2`、`h=√(R²−d²)`、第五条 `√((m−C6x)²+(h−C6y)²) − R` | `wPoint_coord0/1`、`residual_comp_4` |
| `Q(dx·dx + dy·dy)` 即欧氏距离 | **`dist_point_eq_sqrt`** |

**诚实边界（不冒称完成）**：从 **Python 源码到 Lean** 的*自动*转写原则上不可能；
本文件只保证「**我的 Lean 转写**（`TCSystem.lean`）与上述六条结构描述**逐条一致**」，
每一条都有独立名字与 kernel 证明，从而**任何单条对读错误都会被定位到具体引理**。
这就是为什么上一轮 `e_R` 的下标错误（F 下标 6 vs 11）能被 `TCSystem_eR_at_eleven` 这类
具名引理钉死。**数值级**的独立验证由 root-audit 的 `my_tc.py` 承担（12/12 在 1e-56 包络内）。

**真实等级**：kernel-proved，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

/-- **源文 `Q(dx·dx + dy·dy)` 即欧氏距离**：`Point = EuclideanSpace ℝ (Fin 2)` 上
`dist p q = √((p₀−q₀)² + (p₁−q₁)²)`。这是把我把 `dist` 用于残差与源文 Python 写法的桥。 -/
theorem dist_point_eq_sqrt (p q : Point) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have h0 : (p - q).ofLp 0 = p.ofLp 0 - q.ofLp 0 := rfl
  have h1 : (p - q).ofLp 1 = p.ofLp 1 - q.ofLp 1 := rfl
  simp only [Fin.sum_univ_two, h0, h1, Real.norm_eq_abs, sq_abs]

/-- **源文的 `(k+1) % 9` 与 `Fin 9` 加法一致**（源 `res5` 用 `k2 = (k+1) % 9`，
本工程 `Uvec` 用 `k + 1`）。 -/
theorem fin9_succ_val (k : Fin 9) : ((k + 1 : Fin 9) : ℕ) = ((k : ℕ) + 1) % 9 :=
  Fin.val_add k 1

/-! ## ① 九槽角向量（回文表） -/

theorem angleVec_0 (u : Fin 12 → ℝ) : angleVec u 0 = u 0 := rfl
theorem angleVec_1 (u : Fin 12 → ℝ) : angleVec u 1 = u 1 := rfl
theorem angleVec_2 (u : Fin 12 → ℝ) : angleVec u 2 = u 2 := rfl
theorem angleVec_3 (u : Fin 12 → ℝ) : angleVec u 3 = u 3 := rfl
theorem angleVec_4 (u : Fin 12 → ℝ) :
    angleVec u 4 = Real.pi - 2 * (u 0 + u 1 + u 2 + u 3) := rfl
theorem angleVec_5 (u : Fin 12 → ℝ) : angleVec u 5 = u 3 := rfl
theorem angleVec_6 (u : Fin 12 → ℝ) : angleVec u 6 = u 2 := rfl
theorem angleVec_7 (u : Fin 12 → ℝ) : angleVec u 7 = u 1 := rfl
theorem angleVec_8 (u : Fin 12 → ℝ) : angleVec u 8 = u 0 := rfl

/-- ① 的整体形式：九槽表就是源文的 `[a0,a1,a2,a3,a4,a3,a2,a1,a0]`。 -/
theorem angleVec_eq_list (u : Fin 12 → ℝ) :
    angleVec u = ![u 0, u 1, u 2, u 3, Real.pi - 2 * (u 0 + u 1 + u 2 + u 3), u 3, u 2, u 1, u 0] :=
  rfl

/-! ## ② 径向坐标 -/

theorem rhoK_eq (u : Fin 12 → ℝ) (k : Fin 9) :
    rhoK u k = Real.cos (angleVec u k) - Real.sqrt ((u 6) ^ 2 - (Real.sin (angleVec u k)) ^ 2) :=
  rfl

/-! ## ④ `C_k`、`B_k`、`U_k` 的坐标读数 -/

theorem ringCenter_coord0 (u : Fin 12 → ℝ) (k : Fin 9) :
    (ringCenter u k).ofLp 0 = rhoK u k * Real.cos (thetaOf (angleVec u) k) := rfl
theorem ringCenter_coord1 (u : Fin 12 → ℝ) (k : Fin 9) :
    (ringCenter u k).ofLp 1 = rhoK u k * Real.sin (thetaOf (angleVec u) k) := rfl
theorem arcEnd_coord0 (u : Fin 12 → ℝ) (k : Fin 9) :
    (arcEnd u k).ofLp 0 = Real.cos (thetaOf (angleVec u) k + angleVec u k) := rfl
theorem arcEnd_coord1 (u : Fin 12 → ℝ) (k : Fin 9) :
    (arcEnd u k).ofLp 1 = Real.sin (thetaOf (angleVec u) k + angleVec u k) := rfl
theorem Uvec_coord0 (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 0 = (ringCenter u k).ofLp 0 + (ringCenter u (k + 1)).ofLp 0
      - (arcEnd u k).ofLp 0 := rfl
theorem Uvec_coord1 (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 1 = (ringCenter u k).ofLp 1 + (ringCenter u (k + 1)).ofLp 1
      - (arcEnd u k).ofLp 1 := rfl

/-! ## ③ hub 的坐标读数 -/

theorem hub0_coord0 (u : Fin 12 → ℝ) : (hub0 u).ofLp 0 = u 4 := rfl
theorem hub0_coord1 (u : Fin 12 → ℝ) : (hub0 u).ofLp 1 = 0 := rfl
theorem hub1_coord0 (u : Fin 12 → ℝ) : (hub1 u).ofLp 0 = u 5 := rfl
theorem hub1_coord1 (u : Fin 12 → ℝ) : (hub1 u).ofLp 1 = 0 := rfl

/-! ## ⑤ 四条残差的顺序 -/

theorem residual_comp_0 (u : Fin 12 → ℝ) :
    residual u 0 = dist (Uvec u 1) (hub1 u) - u 6 := rfl
theorem residual_comp_1 (u : Fin 12 → ℝ) :
    residual u 1 = dist (Uvec u 2) (hub0 u) - u 6 := rfl
theorem residual_comp_2 (u : Fin 12 → ℝ) :
    residual u 2 = dist (Uvec u 3) (hub0 u) - u 6 := rfl
theorem residual_comp_3 (u : Fin 12 → ℝ) :
    residual u 3 = dist (Uvec u 8) (hub1 u) - u 6 := rfl

/-! ## ⑥ 第五条残差：`m`、`d`、`h` -/

theorem wPoint_coord0 (u : Fin 12 → ℝ) : (wPoint u).ofLp 0 = (u 4 + u 5) / 2 := rfl
theorem wPoint_coord1 (u : Fin 12 → ℝ) :
    (wPoint u).ofLp 1 = Real.sqrt ((u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2) := rfl
theorem residual_comp_4 (u : Fin 12 → ℝ) :
    residual u 4 = dist (wPoint u) (ringCenter u 6) - u 6 := rfl

/-- ⑥ 的 `m`、`d` 与源文一致（`half` 取**精确** `1/2`，非近似）。 -/
theorem m_eq (u : Fin 12 → ℝ) : (u 4 + u 5) / 2 = (u 4 + u 5) * (2 : ℝ)⁻¹ := by ring
theorem d_eq (u : Fin 12 → ℝ) : (u 5 - u 4) / 2 = (u 5 - u 4) * (2 : ℝ)⁻¹ := by ring

/-- ⑤⑥ 的合并读数：五个残差的**完整**形状（与源文 `res5` 的 `out` 列表逐项对应）。 -/
theorem residual_eq_list (u : Fin 12 → ℝ) :
    residual u = ![dist (Uvec u 1) (hub1 u) - u 6,
      dist (Uvec u 2) (hub0 u) - u 6,
      dist (Uvec u 3) (hub0 u) - u 6,
      dist (Uvec u 8) (hub1 u) - u 6,
      dist (wPoint u) (ringCenter u 6) - u 6] := rfl

end N11Formalization
