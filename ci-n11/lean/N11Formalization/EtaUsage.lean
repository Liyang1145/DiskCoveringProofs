import N11Formalization.EtaInstance
import N11Formalization.NondegProof
import N11Formalization.HsumCert
import N11Formalization.FmAssembly
import N11Formalization.ResidualHfm

/-!
# `EtaUsage` — 消费点**用法件**（`eta-instance` 线交付；供最终装配直接引用）

本件给出**两条已实测为绿**的装配配方 ＋ 两个槽的逐字形状核对。判据：**exit=0 且输出 0 行**（本件不打印）。

⚠ **本件证的是"接口"（项形状逐字吻合、前提清单不缺口），不是那些流的数学** ✗：
`hD`（D 行/球级）/`hJ`/`hsum`/`hsumR`（`Jt` 线）作为**假设**传入 ✓（`hFm` 由根内 `hFm_of_hD` 供给 ✓）。

## 装配配方（本轮实测）
```
配方 A（**绿** ✓ 本件 `nd_via_hyp`）：`hηb` 与 `hFm` 作为**参数**（类型逐字写出）传入；
        消费者用 `Fm := fmCert lamCert D`（真对象 ✓）。实测 37 s / exit=0 / 0 行 ✓
配方 B（**绿** ✓ `probe_consumer_only.lean`）：`Fm` 也作为变量 ⇒ 26.3 s / exit=0 / 0 行 ✓
❌ 配方 C（**whnf 超时** ✗✓，三次复现）：把 `eta_hηb` **内联**进消费者的实参位置
   （直接内联 ✗／`show … from eta_hηb` ✗／`let` 绑定 ✗ 均超时；默认 200k 心跳；
    抬到 2M 仍 ✗、>140 s）—— 对照：同位置的**假设变量**为绿 ⇒ 代价在"**常数 `eta_hηb` 的型与实参位期望型的比较**"，
   不在 `Fm` 实参（T2a：只差 `hηb` 一处 ⇒ 绿 37 s ✓）。
⇒ **最终装配请用配方 A/B**（把 `hηb` 当参数/假设传），**不要**在消费者实参位内联 `eta_hηb` ✗。
```
⚠ 三条命名口径（本轮实测）：
1. `EtaResCons` 是**文件名**、不是命名空间 ✗✓（`KCons`/`KConsR`/`etaCons`/`hK0`/`hK1`/`hη0`/`hK'0`/`hK'1`/`hresCons` 全在**裸 `N11Formalization`**）
2. `cCertR_eq_certCR`（桥）与 `hFm_of_hD`（`hFm` 的归约）**也都在裸 `N11Formalization`**（它们的文件内就是 `namespace N11Formalization`）✗✓
3. 本件**不重声明**这两个名（根内已有 ✓）—— 直接引用 ✓
-/

noncomputable section

namespace N11Formalization

/-- **配方 A**：消费者 + 真 `Fm := fmCert lamCert D`；`hηb`（本线的 `eta_hηb` 之形状）与 `hFm`（由 `hFm_of_hD` 供给）作为**参数**。 -/
theorem nd_via_hyp
    (D : Fin 5 → Fin 7 → RatInterval)
    (hFm : ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12,
      (((incrMatVec HsumPayload.certReal.Yof (fmCert lamCert D) i).abs).hi : ℝ) ≤ etaCons)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat HsumPayload.certReal.Yof Jt i j).lo : ℝ)|
        |((krawczykMat HsumPayload.certReal.Yof Jt i j).hi : ℝ)| ≤ KCons)
    (hsumR : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR Jt HsumPayload.certReal.Yof i j).lo : ℝ)|
        |((krawczykMatR Jt HsumPayload.certReal.Yof i j).hi : ℝ)| ≤ KConsR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 :=
  nd_end_to_end_right HsumPayload.certReal.Yof KCons etaCons KConsR
    hK0 hK1 hη0 hK'0 hK'1
    Jt hJ hsum hsumR
    (fmCert lamCert D) hFm hηb hresCons

/-- 同一配方的弱化读数：只取 `Rstar < 19/50`（`obtain` 强制核对结论的 **7 项合取** ✓）。 -/
theorem nd_via_hyp_lt19
    (D : Fin 5 → Fin 7 → RatInterval)
    (hFm : ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12,
      (((incrMatVec HsumPayload.certReal.Yof (fmCert lamCert D) i).abs).hi : ℝ) ≤ etaCons)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat HsumPayload.certReal.Yof Jt i j).lo : ℝ)|
        |((krawczykMat HsumPayload.certReal.Yof Jt i j).hi : ℝ)| ≤ KCons)
    (hsumR : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR Jt HsumPayload.certReal.Yof i j).lo : ℝ)|
        |((krawczykMatR Jt HsumPayload.certReal.Yof i j).hi : ℝ)| ≤ KConsR) :
    ∃ S : C891RootSpec, Rstar S < 19 / 50 := by
  obtain ⟨S, -, -, -, -, -, hlt⟩ := nd_via_hyp D hFm hηb Jt hJ hsum hsumR
  exact ⟨S, hlt⟩

/-- 槽 1（`hηb`）：本线定理的逐字形状（直接引用 ✓）。 -/
example : ∀ i : Fin 12,
    (((incrMatVec HsumPayload.certReal.Yof (fmCert lamCert D) i).abs).hi : ℝ) ≤ etaCons :=
  eta_hηb

/-- 槽 2（`hFm`）：根内 `hFm_of_hD` 的逐字形状（`hD ⇒ 消费点口径的 hFm` ✓）。 -/
example (D : Fin 5 → Fin 7 → RatInterval)
    (hD : ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k)) :
    ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem certCR k) :=
  hFm_of_hD D hD

end N11Formalization
