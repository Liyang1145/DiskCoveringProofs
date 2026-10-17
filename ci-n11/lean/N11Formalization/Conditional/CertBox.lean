import N11Formalization.Conditional.RootSpec

/-!
# 用源证书数据实例化 C891 盒（并把前提降到最少）

本文件做两件事：

1. **用真实证书数据造出 12 维隔离盒** `certBoxLo/certBoxHi = 中心 ± 半宽`
   （中心与半宽来自 `repaired_tc_krawczyk.json`，十六进制字面量的精确 dyadic 值）。
2. **去掉一条不必要的前提**：先前的 `Rstar_lt_R0_via_cert` 需要 C891 的 Krawczyk 包含
   `K(X) ⊆ X`（即「根落在包络内」）。但 `Rstar < 19/50` 只需要「根落在**盒**内」，
   而盒包含性是 `C891RootSpec.exists_unique` 的**字段内容**，不需要额外的 Krawczyk 步骤。
   盒的第 6 坐标上端 = `center₆ + radius ≈ 0.37998385411983865 < 0.38`，余量约 1.615e-5。

   结构收益：**到 `R* < 19/50` 的未证前提从 2 条降到 1 条**（只剩「盒内存在唯一根」）。

### 真实等级
* 本文件所有**数值**结论都是 `kernel-proved`（纯内核有理算术）。
* 本文件所有**主定理**结论都是 `conditional-kernel`：前提是显式的、未形式化的
  `exists_unique` / `hattain` / `hbound`。**不是**无条件主定理。
-/

namespace N11Formalization

/-- 12 维隔离盒的下端：`中心ᵢ − 半宽`（精确有理）。 -/
def certBoxLo : Fin 12 → ℚ := fun i => (decCenterHex i).toQ - decRadiusHex.toQ

/-- 12 维隔离盒的上端：`中心ᵢ + 半宽`。 -/
def certBoxHi : Fin 12 → ℚ := fun i => (decCenterHex i).toQ + decRadiusHex.toQ

/-- 盒的第 6 坐标上端的精确值（内核算术）：`0x1851a7cb8a18fb/2^54 + 0x112e0be826d695/2^82`。 -/
theorem certBoxHi_six_eq :
    certBoxHi 6 = (6845180557269243 : ℚ) / 2 ^ 54 + (4835703278458517 : ℚ) / 2 ^ 82 := by
  simp only [certBoxHi, decCenterHex_six, decCenter6, decRadiusHex, HexFloat.toQ, hexNatVal,
    List.length_cons, List.length_nil, pow_succ, pow_zero, mul_one]
  norm_num

/-- **盒的第 6 坐标上端 `< 19/50`**（纯内核有理算术，余量 ≈ 1.615e-5）。 -/
theorem certBoxHi_six_lt_R0 : certBoxHi 6 < 19 / 50 := by
  rw [certBoxHi_six_eq]
  norm_num

/-- 证书包络（4.3e-15 宽）落在盒的第 6 坐标内 —— 盒比包络更粗，故盒路径不需要 Krawczyk 包含。 -/
theorem certBoxHi_six_gt_enclosure : rootBoxCert.encHi < certBoxHi 6 := by
  rw [certBoxHi_six_eq]
  simp only [RootBoxCert.encHi, rootBoxCert, encHiNum, encHiDen]
  norm_num

/-- **去掉 Krawczyk 前提的数值内核**：盒上端 `< 19/50` ⇒ `R* < 19/50`。 -/
theorem Rstar_lt_R0_of_cert_box (S : C891RootSpec)
    (hHi : S.boxHi = certBoxHi) (hidx : S.radiusIndex = 6) :
    Rstar S < 19 / 50 := by
  refine Rstar_lt_R0_of_bound S ?_
  rw [hHi, hidx]
  have h : certBoxHi 6 < 19 / 50 := certBoxHi_six_lt_R0
  have h1 : (certBoxHi 6 : ℝ) < ((19 : ℚ) / 50 : ℝ) := by exact_mod_cast h
  have h2 : ((19 : ℚ) / 50 : ℝ) = (19 : ℝ) / 50 := by norm_num
  linarith

/-- **`R*` 落在真实证书盒的第 6 坐标内**（盒比 4.3e-15 的包络更粗，但两侧都由源数据给出）。 -/
theorem Rstar_mem_cert_box (S : C891RootSpec)
    (hLo : S.boxLo = certBoxLo) (hHi : S.boxHi = certBoxHi) (hidx : S.radiusIndex = 6) :
    (certBoxLo 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (certBoxHi 6 : ℝ) := by
  have h := Rstar_mem_box S
  rw [hLo, hHi, hidx] at h
  exact h

/-- **条件主定理（真实证书盒实例化）**。前提恰好 3 条，全部显式、全部未形式化：
`S.exists_unique`（C891）、`hattain`（C892）、`hbound`（C923+C921+C922）。 -/
theorem n11_main_of_cert_box (S : C891RootSpec)
    (hLo : S.boxLo = certBoxLo) (hHi : S.boxHi = certBoxHi)
    (hidx : S.radiusIndex = 6)
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r) :
    N11MainStatement (Rstar S) ∧ sInf feasibleRadii = Rstar S ∧ Rstar S < 19 / 50 ∧
      (certBoxLo 6 : ℝ) ≤ Rstar S :=
  ⟨n11_main_conditional S hattain hbound,
    n11_sInf_conditional S hattain hbound,
    Rstar_lt_R0_of_cert_box S hHi hidx,
    (Rstar_mem_cert_box S hLo hHi hidx).1⟩

end N11Formalization
