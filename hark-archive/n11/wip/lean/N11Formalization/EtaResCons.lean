import N11Formalization.HsumPayload
import N11Formalization.BoxRstar

/-!
# 消费点 `nd_end_to_end_right` 的**数值级前提**（Lead 短装配，R62）

**对象**（`NondegProof.lean` L673–686 的"自由参数 + 数值不等式"六项）：
```
(K η K' : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η) (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
(hres : η + K * rhoCertR < rhoCertR)
```
**本件的选值**（**全部取自根内已证常数** ✓，不自造数 ✗）：
* `K  := HsumPayload.certReal.numK / certReal.denK`（真实 Krawczyk 收缩 ✓，`HsumPayload` 已内核证）
* `K' := HsumPayload.certRealR.numK / certRealR.denK`
* `η  := 1 / 10^14`（**远宽于所需**：实测 `‖Y·F12(certCR)‖∞ = 2.263e-17` ✓）
* `ρ  := rhoCertR`（= `4835703278458517 / 2^82` ✓）

**⚠ 作用域（如实）** ✗：本件只收**这六项"数值级"前提**；**不**触碰 `hηb`（它依赖 `Fm := fmCert lamCert D` 的
区间端点 ✗，是本会话判定的**承重前置** ✗ —— **不得据此宣称第 6/7 项已关** ✗）。
**命名口径（真名，逐条 `#check` 过 ✓）**：`certReal*` 族全名 = `N11Formalization.HsumPayload.*` ✓；
`rhoCert`/`rhoCertR` = **裸名**（`N11Formalization` 下）✓；`checkR_sound` ∈ `N11Formalization.HsumCert` ✓。
-/

noncomputable section

namespace N11Formalization

/-- 消费点的 `K` 取值。 -/
def KCons : ℝ := (N11Formalization.HsumPayload.certReal.numK : ℝ) /
  (N11Formalization.HsumPayload.certReal.denK : ℝ)

/-- 消费点的 `K'` 取值。 -/
def KConsR : ℝ := (N11Formalization.HsumPayload.certRealR.numK : ℝ) /
  (N11Formalization.HsumPayload.certRealR.denK : ℝ)

/-- 消费点的 `η` 取值（宽松 ✓）。 -/
def etaCons : ℝ := 1 / 10 ^ 14

theorem hK0 : 0 ≤ KCons := N11Formalization.HsumPayload.certReal_K_nonneg

theorem hK1 : KCons < 1 := N11Formalization.HsumPayload.certReal_K_lt_one

theorem hK'1 : KConsR < 1 := N11Formalization.HsumPayload.certRealR_K_lt_one

/-- `K'` 非负：由同一条 soundness 的第二个分量给出（`HsumPayload` 未单列此名）。 -/
theorem hK'0 : 0 ≤ KConsR :=
  (N11Formalization.HsumCert.checkR_sound N11Formalization.HsumPayload.certRealR_checkR).2.1

theorem hη0 : 0 ≤ etaCons := by norm_num [etaCons]

/-- **`hres`**：`η + K·ρ < ρ` ✓。证法：`K` 的整数展开给 `1/2 ≤ 1 − K`，`ρ` 的展开给 `ρ/2 ≥ 1e-14`，再 `linarith`。 -/
theorem hresCons : etaCons + KCons * rhoCertR < rhoCertR := by
  -- `K` 的整数展开给 `K ≤ 1/2`（真值 ≈ 4.37e-3 ✓）
  have hKle : KCons ≤ 1 / 2 := by
    norm_num [KCons, N11Formalization.HsumPayload.certReal,
      N11Formalization.HsumPayload.numKz, N11Formalization.HsumPayload.Ez,
      N11Formalization.HsumPayload.Dz]
  -- `ρ` 的展开给 `ρ/2 > 1e-14`（真值 ρ/2 ≈ 4.8e-10 ✓）
  have hρ : (1 / 2 : ℝ) * rhoCertR > 1 / 10 ^ 14 := by
    norm_num [rhoCertR, rhoCert]
  have hρ0 : (0 : ℝ) ≤ rhoCertR := by norm_num [rhoCertR, rhoCert]
  have hη : etaCons = 1 / 10 ^ 14 := rfl
  nlinarith [hKle, hρ, hρ0, hη]

end N11Formalization
