import N11Formalization.ResidualInterval
-- C1270 修复（作者 tower-bc；Lead 裁决"真缺陷，修" ✓）：前 5 分量改用**阶乘（Lag）塔**
--   `residualIntervalLag cCert` —— 原用非 Lag `residualInterval` ✗，其格 0 端点 `.hi = 7.97e-4`，
--   而 `ResidualDerivD` 的 `Aiv/Biv/D` 与端点的消费方（`EtaResCert.Fof`）全是 **Lag** 族 ⇒
--   同格差 **13 个数量级** ⇒ `hηb` 会与 `hFm` 脱钩 ✗✓。替换 1:1（两条 enclosure 定理语句逐字同形 ✓）；
--   前置单件门：`evidence/tower-bc/scratch/C1270_FmCertLagProbe.lean`（sha16 见 NOTES；exit=0 / 输出 0 行 ✓）。
import N11Formalization.ResidualIntervalLag
import N11Formalization.KrawczykMatrix
import N11Formalization.Interval.Vector

/-!
# `Fm` 的**十二分量拼装**：把 `Fin 5` 的残差包络补成消费者要的 `Fin 12`

## 为什么需要本文件（Lead 批准的 ①，缺口由 `evidence/box-rstar/ifc_audit_rstar_premises.py` 定位）

`Precond.TCSystem_unique_root_of_full_data`（进而 `BoxRstar.c891RootSpec_of_right_data`、
`Rstar_lt_R0_of_ball`）要的是 `Fm : Fin 12 → RatInterval`，而现有产出方
`ResidualInterval.residualInterval : (Fin 12 → ℚ) → Fin 5 → RatInterval` 只给 5 个分量
（源残差 `f` 的 5 个分量）。本文件把两者接上：

```
Fm = (residualIntervalLag cCert 的 5 个分量)  ++  (乘子块的 7 个分量)
```

⚠ **C1270 修复（作者 tower-bc；Lead 裁决"真缺陷，修" ✓）**：上面前 5 分量原写作**非 Lag** 的
`ResidualInterval.residualInterval` ✗ —— 与 `ResidualDerivD` 的 `Aiv/Biv/D`（Lag 族）及消费方
`EtaResCert.Fof` 的 Lag 端点**不是同一对象**（同格差 13 个数量级：7.0e-17 vs 7.97e-4）✗✓；
现改为 **`ResidualIntervalLag.residualIntervalLag`**（1:1 替换：两条 enclosure 定理语句逐字同形 ✓），
`Mem` 侧改用 `mem_residualIntervalLag_cCert_TCSystem`（`ResidualIntervalLag.lean` L456 ✓）。
前置单件门：`evidence/tower-bc/scratch/C1270_FmCertLagProbe.lean`（exit=0 / 输出 0 行 ✓，
并附非 Lag 对照 `¬(hi ≤ 1e-9)` ✓）。

**为什么不能用 0 padding 糊过去（承重）**：`Fm` 会被喂进
`incrMatVec Y Fm i = Σ_m Y i m · Fm m`（`m : Fin 12`），即 `Y` 的第 `i` 行与**全部 12 个分量**
相乘；错的 7 个分量会直接改变 `η`（经 `norm_ratMatCLM_le`）进而改变 `hres : η + Kρ < ρ`。
所以后 7 个分量必须按其**定义**给出。

## 后 7 个分量的定义与口径

`TCSystem u` 的后 7 个分量（`TCSystem.lean`）是
`F_{5+i}(u) = e_R[i] − (adjointBlock (first7 u) (last5 u)) i`，
其中 `adjointBlock z λ i = Σ_{k:Fin 5} λ_k · (fderiv ℝ residualFun z (Pi.single i 1)) k`。
在证书盒心 `cCertR` 处，`λ = last5 cCertR` 是**有理数**（证书盒坐标全是精确有理），
而 `∂f_k/∂z_i = (fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k` 是**实数**。
所以正确的区间包络是

```
Fm (5+i) = ofRat (δ_{i6})  −  dot (fun k => λ_k)  (fun k => D k i)
```

其中 `D : Fin 5 → Fin 7 → RatInterval` 是 `∂f_k/∂z_i` 在盒心处的**区间包络**——这正是
interval AD 层要产出的物件。**它一般不是零宽**：只有当 `D` 恰为点区间时才退化为有理数。
（Lead 的措辞「后 7 个以 `ofRat` 给出」只在「`λ` 有理 **且** 导数条目也视为精确有理」时成立；
本文件取的是**更弱也更安全**的形式：`ofRat λ_k` 乘 `D k i`，因此**前提不需要导数条目是有理数**。
另见 `mem_fmCert_of_point`：若 `D` 确实是点区间，`hD` 退化为逐条导数等式。）

## 前提清单（做完只剩一项）

1. `D : Fin 5 → Fin 7 → RatInterval` 与 **`hD : ∀ k i, (D k i).Mem (∂f_k/∂z_i 在盒心处)`**
   —— interval AD 的输出，**未产出**（`IntervalAD.lean` 不在 build 内）。
2. `λ`：本文件用 `lamCert := fun k => cCert (7+k)`，并证明 `hLam_rfl`（`rfl` 级）
   ⇒ **`λ` 不是真实前提**。

所以**唯一实质前提是 `hD`**，见 `mem_fmCert_cert`。**注意** `hD` 的类型天然是
`Fin 5 → Fin 7`（`f_k` 只有 5 个、`z_i` 只有 7 个），**不含** `∂f/∂λ = 0` 的分量——
那部分在 `TCSystem` 里由定义（`f` 不读 `λ`）自动为 0，故不需要任何子句。

## 真实等级

本文件全部 kernel-proved（除上面显式列出的 `hD`），零 `sorry`、零自定义 `axiom`、
零 `native_decide`。**本文件不产出 `hD`**（与 `C1018` 的 gap 判定一致）。
-/

namespace N11Formalization

open RatInterval

/-- `Fin 5` 送入 `Fin 12` 的前段（证明用 `isLt`）。 -/
def to12a (k : Fin 5) : Fin 12 := ⟨(k : ℕ), by have := k.isLt; omega⟩

/-- `Fin 5` 送入 `Fin 12` 的后段（第 `7+k` 个坐标，即 `λ_k`）。 -/
def to12b (k : Fin 5) : Fin 12 := ⟨(k : ℕ) + 7, by have := k.isLt; omega⟩

/-- 变量坐标下标：`Fin 12` 的第 `j` 个（`j ≥ 5`）对应 `z_{j−5}`。
`hj` 是 `j ≥ 5` 的假设——**必须显式传入**，否则 `omega` 看不到下界。 -/
def colidx (j : Fin 12) (hj : 5 ≤ (j : ℕ)) : Fin 7 :=
  ⟨(j : ℕ) - 5, by have := j.isLt; omega⟩

/-- **`Fm` 的第 `5+i` 个分量**（乘子块的区间包络）。 -/
noncomputable def fmAdj (lam : Fin 5 → ℚ) (D : Fin 5 → Fin 7 → RatInterval)
    (j : Fin 12) (hj : 5 ≤ (j : ℕ)) : RatInterval :=
  RatInterval.sub (RatInterval.ofRat (if (j : ℕ) - 5 = 6 then (1 : ℚ) else 0))
    (RatInterval.dot (fun k => lam k) (fun k => D k (colidx j hj)))

/-- **`Fm` 的 12 分量拼装**：前 5 个 = `residualIntervalLag cCert`（**阶乘/Lag 塔**；C1270 修复），后 7 个 = 乘子块的区间包络。 -/
noncomputable def fmCert (lam : Fin 5 → ℚ) (D : Fin 5 → Fin 7 → RatInterval) : Fin 12 → RatInterval :=
  fun j =>
    if h : (j : ℕ) < 5 then residualIntervalLag cCert ⟨(j : ℕ), h⟩
    else fmAdj lam D j (by omega)

/-- **`TCSystem u` 的后 7 个分量展开成有限和**（便于与 `dot_mem` 对接）。
索引本文件统一取 `colidx` / `to12b`，避免 `omega` 处理带 `Fin` 强转的目标。 -/
theorem tcSystem_adjointBlock_eq (u : Fin 12 → ℝ) (j : Fin 12) (hj : ¬ (j : ℕ) < 5) :
    TCSystem u j
      = (if (j : ℕ) = 11 then (1 : ℝ) else 0)
        - ∑ k : Fin 5, u (to12b k)
            * (fderiv ℝ residualFun (first7 u)
                (Pi.single (colidx j (by omega)) 1)) k := by
  rw [TCSystem]
  rw [dif_neg hj]
  show ((if (j : ℕ) = 11 then (1 : ℝ) else 0)
        - (fun i => ∑ k : Fin 5, u (to12b k)
            * (fderiv ℝ residualFun (first7 u) (Pi.single i 1)) k) (colidx j (by omega)))
      = (if (j : ℕ) = 11 then (1 : ℝ) else 0)
        - ∑ k : Fin 5, u (to12b k)
            * (fderiv ℝ residualFun (first7 u)
                (Pi.single (colidx j (by omega)) 1)) k
  rfl

/-- **前 5 个分量的包含性**（由 `ResidualIntervalLag` 的阶乘/Lag 实例给出；C1270 修复后 ✓）。 -/
theorem fmCert_mem_first (lam : Fin 5 → ℚ) (D : Fin 5 → Fin 7 → RatInterval)
    (k : Fin 5) :
    (fmCert lam D (to12a k)).Mem (TCSystem cCertR (to12a k)) := by
  fin_cases k
  · exact mem_residualIntervalLag_cCert_TCSystem (0 : Fin 5)
  · exact mem_residualIntervalLag_cCert_TCSystem (1 : Fin 5)
  · exact mem_residualIntervalLag_cCert_TCSystem (2 : Fin 5)
  · exact mem_residualIntervalLag_cCert_TCSystem (3 : Fin 5)
  · exact mem_residualIntervalLag_cCert_TCSystem (4 : Fin 5)

/-- **后 7 个分量的包含性**（由 `λ` 的有理值与 `∂f_k/∂z_i` 的区间包络给出）。 -/
theorem fmCert_mem_adjoint (lam : Fin 5 → ℚ) (D : Fin 5 → Fin 7 → RatInterval)
    (hLam : ∀ k : Fin 5, (lam k : ℝ) = last5 cCertR k)
    (hD : ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k))
    (j : Fin 12) (hj : ¬ (j : ℕ) < 5) :
    (fmCert lam D j).Mem (TCSystem cCertR j) := by
  have hge : 5 ≤ (j : ℕ) := by omega
  -- 乘子项：`last5 cCertR k = cCert (to12b k)`（`rfl` 级）
  have hcast : ∀ k : Fin 5, last5 cCertR k = cCertR (to12b k) := fun k => rfl
  have hdot : (RatInterval.dot (fun k => lam k) (fun k => D k (colidx j hge))).Mem
      (∑ k : Fin 5, cCertR (to12b k)
        * (fderiv ℝ residualFun (first7 cCertR) (Pi.single (colidx j hge) 1)) k) := by
    have hd := RatInterval.dot_mem (c := fun k : Fin 5 => lam k)
      (A := fun k : Fin 5 => D k (colidx j hge))
      (x := fun k : Fin 5 =>
        (fderiv ℝ residualFun (first7 cCertR) (Pi.single (colidx j hge) 1)) k)
      (fun k => hD k (colidx j hge))
    rw [dotR_eq_sum] at hd
    have hs : (∑ k : Fin 5, (((fun m : Fin 5 => lam m) k : ℚ) : ℝ) *
          ((fun k : Fin 5 =>
            (fderiv ℝ residualFun (first7 cCertR) (Pi.single (colidx j hge) 1)) k) k))
        = ∑ k : Fin 5, cCertR (to12b k)
            * (fderiv ℝ residualFun (first7 cCertR) (Pi.single (colidx j hge) 1)) k :=
      Finset.sum_congr rfl fun k _ => by rw [hLam k, hcast k]
    rw [hs] at hd
    exact hd
  have hdelta : (RatInterval.ofRat (if (j : ℕ) - 5 = 6 then (1 : ℚ) else 0)).Mem
      (if (j : ℕ) = 11 then (1 : ℝ) else 0) := by
    by_cases h6 : (j : ℕ) - 5 = 6
    · have hj11 : (j : ℕ) = 11 := by omega
      rw [if_pos h6, if_pos hj11]
      have h1 : (((1 : ℚ)) : ℝ) = (1 : ℝ) := by norm_num
      rw [← h1]
      exact RatInterval.ofRat_mem (1 : ℚ)
    · have hj11 : ¬ (j : ℕ) = 11 := by omega
      rw [if_neg h6, if_neg hj11]
      have h0 : (((0 : ℚ)) : ℝ) = (0 : ℝ) := by norm_num
      rw [← h0]
      exact RatInterval.ofRat_mem (0 : ℚ)
  have hsub := RatInterval.sub_mem hdelta hdot
  rw [fmCert]
  rw [dif_neg hj]
  rw [show fmAdj lam D j hge
      = RatInterval.sub (RatInterval.ofRat (if (j : ℕ) - 5 = 6 then (1 : ℚ) else 0))
          (RatInterval.dot (fun k => lam k) (fun k => D k (colidx j hge))) from rfl]
  have hmain := tcSystem_adjointBlock_eq cCertR j hj
  rw [hmain]
  exact hsub

/-- **`hFm` 的完整形态（本文件主引理）**：12 个分量全部包住 `TCSystem cCertR`。 -/
theorem mem_fmCert (lam : Fin 5 → ℚ) (D : Fin 5 → Fin 7 → RatInterval)
    (hLam : ∀ k : Fin 5, (lam k : ℝ) = last5 cCertR k)
    (hD : ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)) :
    ∀ k : Fin 12, (fmCert lam D k).Mem (TCSystem cCertR k) := by
  intro j
  by_cases hj : (j : ℕ) < 5
  · rw [fmCert, dif_pos hj]
    exact mem_residualIntervalLag_cCert_TCSystem ⟨(j : ℕ), hj⟩
  · exact fmCert_mem_adjoint lam D hLam hD j hj

/-- `λ` 取证书盒心的**后 5 个坐标的有理值**（`last5 cCertR` 的有理化）。 -/
def lamCert : Fin 5 → ℚ := fun k => cCert (to12b k)

/-- `hLam` 对 `lamCert` 是 **`rfl` 级**的事实 ⇒ `λ` **不是**真实前提。 -/
theorem hLam_rfl : ∀ k : Fin 5, (lamCert k : ℝ) = last5 cCertR k := fun _k => rfl

/-- **唯一实质前提是 `hD`**：`Fm := fmCert lamCert D` 的 12 分量包含性。 -/
theorem mem_fmCert_cert (D : Fin 5 → Fin 7 → RatInterval)
    (hD : ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)) :
    ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem cCertR k) :=
  mem_fmCert lamCert D hLam_rfl hD

/-- **点区间特例**：若 `D` 给的是**精确有理数** `d` 的点区间，则 `hD` 退化为逐条导数等式。 -/
theorem mem_fmCert_of_point (d : Fin 5 → Fin 7 → ℚ)
    (hd : ∀ (k : Fin 5) (i : Fin 7),
      (((d k i : ℚ)) : ℝ) = (fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k) :
    ∀ k : Fin 12,
      (fmCert lamCert (fun k i => RatInterval.ofRat (d k i)) k).Mem (TCSystem cCertR k) :=
  mem_fmCert_cert (fun k i => RatInterval.ofRat (d k i))
    (fun k i => by
      have h := hd k i
      rw [← h]
      exact RatInterval.ofRat_mem (d k i))

end N11Formalization
