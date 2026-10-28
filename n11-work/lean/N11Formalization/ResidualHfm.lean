import N11Formalization.FmAssembly
import N11Formalization.BoxRstar

/-!
# `hFm` 的数据桥（`nd_end_to_end` 的 Fm 侧）

**对象**：`nd_end_to_end`（`NondegProof.lean` L615）的 `hFm`：
`∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k)`。

**本文件给什么**
* `cCertR_eq_certCR`：`ResidualInterval` 的盒心表 `cCertR` 与 `BoxRstar` 的 `certCR`
  **逐位相同**（kernel 核对：`cCert` 用展开分母、`certC` 用 `2 ^ 54`）—— 这是 `hFm` 唯一
  的"命名差"桥梁（`FmAssembly.mem_fmCert_cert` 写的是 `cCertR`，而 `hFm` 要 `certCR`）；
* **`hFm_of_hD`**：把 `hFm` 落成一条定理 —— 前提是 **`hD`**（5×7 导数数据的 `Mem` 前提，
  即 `nd_end_to_end` 自己的 `hD` 形状），结论就是 `hFm` 的原式；
* `cCert_eq_certC`（有理分量版）与 **`cCertR_ne_shifted`**（判别力对照：下标挪一格即不同，
  说明上面的逐位核对不是恒真）。

**三条缺口（如实）**
1. **`hD` 的实例仍缺**：本文件是**条件形态**（`hD` 显式作前提，未伪装无条件）。
   `hD` 的供给 = `ResidualDeriv.lean`（线性脊柱，**已在根**）+ `ResidualDerivNode.lean`
   （`rhoK`/`ringCenter`/`arcEnd`/`Uvec`-CLM，**已在根**）**尚缺**：`Uvec` 的标量求值步、
   `dist`、`−R`、5×7 装配，以及两批具体正性（9 条 `Wk k ≠ 0` + dist radicand）。
2. **`Y`/`Yinv`/`hYinv` 不在本件范围**：根内已记（`BoxRstar.lean` L360、`NondegProof.lean` L578）
   源预条件子是 binary64 **近似逆** ⇒ **精确有理左逆取不到**，该走 `nd_end_to_end_right`/`PrecondRight`。
3. **`hηb`/`hsum` 均无现成供给件**（`hηb` 需 `Y` 数据 + 有理宽度计算；`hsum` 在根内处处是假设）。
-/

noncomputable section

namespace N11Formalization

/-- **两份盒心表逐位相同**（`cCert` 用展开分母 `18014398509481984 = 2^54`，`certC` 用 `2 ^ 54`）。 -/
theorem cCertR_eq_certCR : cCertR = certCR := by
  funext i
  fin_cases i <;> norm_num [cCertR, certCR, cCert, certC]

/-- 有理分量版：`cCert i = certC i`（`i : Fin 12` 逐项）。 -/
theorem cCert_eq_certC (i : Fin 12) : cCert i = certC i := by
  fin_cases i <;> norm_num [cCert, certC]

/-- **判别力对照（`*_rejected` 伴生）**：盒心表把下标挪一格就不同 ⇒ 上面的逐位核对
不是"恒真的空壳"（与 `ResidualIntervalReadout.mut_rho_breaks_containment` 同一纪律）。 -/
theorem cCertR_ne_shifted : cCertR ≠ (fun i : Fin 12 => cCertR (i + 1)) := by
  intro h
  have h0 := congrFun h 0
  norm_num [cCertR, cCert] at h0

/-- **`hFm`（条件形态）**：给定 `hD`（5×7 导数数据 `D` 逐项包住 `fderiv ℝ residualFun`
在盒心处沿 `Pi.single i 1` 的值），12 分量装配 `fmCert lamCert D` 就包住 `TCSystem certCR`。 -/
theorem hFm_of_hD (D : Fin 5 → Fin 7 → RatInterval)
    (hD : ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)) :
    ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k) := by
  intro k
  rw [← cCertR_eq_certCR]
  exact mem_fmCert_cert D hD k

end N11Formalization
