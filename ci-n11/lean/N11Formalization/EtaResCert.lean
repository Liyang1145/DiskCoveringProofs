import N11Formalization.HsumCert

/-!
# `EtaResCert`: `hηb` / `hη0` / `hres` 的**参数化**整数证书

**靶子形状**（源：`Precond.lean:104-124` 的 `TCSystem_unique_root_of_full_data`）
```
hηb  : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η
hη0  : 0 ≤ η
hres : η + K * ρ < ρ
```
**参数化口径（本件的关键设计，按 Lead 裁决）**：`Fm` 在这里是**显式数据**（12 个区间的两端分子），
**不使用也不假定** `FmAssembly.fmCert`（它是 `fmCert (lam) (D)` 的**参数化**件，其 `hFm` 依赖 `hD`，
下游于 `fm-eval`）✗。所以本件给的是**声明 + 判据 + soundness + `*_rejected` 伴生**，
**具体实例留槽**（把 `Fm` 的真实端点填进来即可，与 `HsumCert` 同型）✓。

**口径**（共同分母模型，与 `HsumCert` 逐字一致）：
`Y i k = numY i k / Dcom`，`Fm k = [loF k / Dcom, hiF k / Dcom]`，`η = numEta/denEta`，
`K = numK/denK`，`ρ = rhoNum/rhoDen`；所有分母为正；共同分母平方 `E = Dcom²`。

**真实等级**：kernel-proved，零 `sorry`、零自定义公理、零 `native_decide`。
**不覆盖**：`Fm` 的出处（即 `hFm`：`Fm ∋ TCSystem c`）——那是 `fm-eval`/`hD` 的义务 ✓。
-/

namespace N11Formalization

/-- η 侧（`hηb`/`hη0`/`hres`）的整数化证书数据（**全部不受信**）。 -/
structure EtaResCert where
  /-- 共同分母（正）；`Y` 与 `Fm` 共用。 -/
  Dcom : ℤ
  /-- `Y` 的分子。 -/
  numY : Fin 12 → Fin 12 → ℤ
  /-- `Fm` 各分量的下端分子（**向量**，不是矩阵）。 -/
  loF : Fin 12 → ℤ
  /-- `Fm` 各分量的上端分子。 -/
  hiF : Fin 12 → ℤ
  /-- `η` 的分子。 -/
  numEta : ℤ
  /-- `η` 的分母（正）。 -/
  denEta : ℤ
  /-- `K` 的分子。 -/
  numK : ℤ
  /-- `K` 的分母（正）。 -/
  denK : ℤ
  /-- `ρ` 的分子。 -/
  rhoNum : ℤ
  /-- `ρ` 的分母（正）。 -/
  rhoDen : ℤ

namespace EtaResCert

/-- 共同分母的平方。 -/
def E (c : EtaResCert) : ℤ := c.Dcom * c.Dcom

/-- `Y` 的 ℚ 语义。 -/
def Yof (c : EtaResCert) : Fin 12 → Fin 12 → ℚ := fun i k => (c.numY i k : ℚ) / (c.Dcom : ℚ)

/-- `Fm` 的区间语义。 -/
def Fof (c : EtaResCert) : Fin 12 → RatInterval :=
  fun k => ⟨(c.loF k : ℚ) / (c.Dcom : ℚ), (c.hiF k : ℚ) / (c.Dcom : ℚ)⟩

/-- `(Σ_k Y_ik·Fm_k).lo` 的分子（`E` 格）。 -/
def loV (c : EtaResCert) (i : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY i k then c.numY i k * c.loF k else c.numY i k * c.hiF k

/-- `(Σ_k Y_ik·Fm_k).hi` 的分子（`E` 格）。 -/
def hiV (c : EtaResCert) (i : Fin 12) : ℤ :=
  ∑ k : Fin 12, if 0 ≤ c.numY i k then c.numY i k * c.hiF k else c.numY i k * c.loF k

/-! ## 1. ℤ 数据 → ℚ 语义（逐项 / 求和） -/

theorem nonneg_Yof (c : EtaResCert) (hD : 0 < c.Dcom) {i k : Fin 12}
    (h : 0 ≤ c.numY i k) : 0 ≤ c.Yof i k := by
  simp only [Yof]
  exact div_nonneg (by exact_mod_cast h) (by exact_mod_cast hD.le)

theorem not_nonneg_Yof (c : EtaResCert) (hD : 0 < c.Dcom) {i k : Fin 12}
    (h : ¬ 0 ≤ c.numY i k) : ¬ 0 ≤ c.Yof i k := by
  intro hq
  simp only [Yof] at hq
  have hDQ : (0 : ℚ) < (c.Dcom : ℚ) := by exact_mod_cast hD
  have hDne : ((c.Dcom : ℤ) : ℚ) ≠ 0 := ne_of_gt hDQ
  have h2 : (0 : ℚ) * (c.Dcom : ℚ) ≤ (c.numY i k : ℚ) := by
    have h3 := mul_le_mul_of_nonneg_right hq hDQ.le
    rw [div_mul_cancel₀ _ hDne] at h3
    simpa using h3
  exact h (by simpa using h2)

theorem loTermV_eq (c : EtaResCert) (hD : 0 < c.Dcom) {i k : Fin 12} :
    RatInterval.loTerm (c.Yof i) c.Fof k
      = ((if 0 ≤ c.numY i k then c.numY i k * c.loF k
            else c.numY i k * c.hiF k : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.loTerm, Fof, E]
  by_cases h : 0 ≤ c.numY i k
  · rw [if_pos h, if_pos (nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.Dcom : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.Dcom : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem hiTermV_eq (c : EtaResCert) (hD : 0 < c.Dcom) {i k : Fin 12} :
    RatInterval.hiTerm (c.Yof i) c.Fof k
      = ((if 0 ≤ c.numY i k then c.numY i k * c.hiF k
            else c.numY i k * c.loF k : ℤ) : ℚ) / (c.E : ℚ) := by
  simp only [RatInterval.hiTerm, Fof, E]
  by_cases h : 0 ≤ c.numY i k
  · rw [if_pos h, if_pos (nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.Dcom : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]
  · rw [if_neg h, if_neg (not_nonneg_Yof c hD h)]
    rw [show c.Yof i k = (c.numY i k : ℚ) / (c.Dcom : ℚ) from rfl]
    push_cast
    rw [div_mul_div_comm]

theorem sum_loV_eq (c : EtaResCert) (hD : 0 < c.Dcom) (i : Fin 12) :
    (∑ k : Fin 12, RatInterval.loTerm (c.Yof i) c.Fof k) = (c.loV i : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => loTermV_eq c hD (i := i) (k := k)), ← Finset.sum_div]
  congr 1
  simp only [loV, Int.cast_sum]

theorem sum_hiV_eq (c : EtaResCert) (hD : 0 < c.Dcom) (i : Fin 12) :
    (∑ k : Fin 12, RatInterval.hiTerm (c.Yof i) c.Fof k) = (c.hiV i : ℚ) / (c.E : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => hiTermV_eq c hD (i := i) (k := k)), ← Finset.sum_div]
  congr 1
  simp only [hiV, Int.cast_sum]

theorem Fof_valid (c : EtaResCert) (hD : 0 < c.Dcom)
    (hvalid : ∀ k : Fin 12, c.loF k ≤ c.hiF k) (k : Fin 12) :
    (c.Fof k).lo ≤ (c.Fof k).hi := by
  simp only [Fof]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hvalid k) (by exact_mod_cast hD.le)

theorem Epos (c : EtaResCert) (hD : 0 < c.Dcom) : (0 : ℚ) < (c.E : ℚ) := by
  have hDQ : (0 : ℚ) < (c.Dcom : ℚ) := by exact_mod_cast hD
  rw [E]
  push_cast
  nlinarith [hDQ]

/-- `max (-a) b` 的 `ℤ → ℚ` 桥。 -/
theorem int_cast_max_neg (a b : ℤ) : ((max (-a) b : ℤ) : ℚ) = max (-(a : ℚ)) (b : ℚ) := by
  rw [int_cast_maxQ]
  push_cast
  ring

/-- **`hηb` 的端点恒等式**：`((incrMatVec Y Fm i).abs).hi = max (-loV i) (hiV i) / E`。 -/
theorem abs_hi_eq (c : EtaResCert) (hD : 0 < c.Dcom)
    (hvalid : ∀ k : Fin 12, c.loF k ≤ c.hiF k) (i : Fin 12) :
    ((incrMatVec c.Yof c.Fof i).abs).hi
      = (max (-(c.loV i)) (c.hiV i) : ℚ) / (c.E : ℚ) := by
  have hlo := RatInterval.dot_lo_eq (c := c.Yof i) (A := c.Fof) (fun k => Fof_valid c hD hvalid k)
  have hhi := RatInterval.dot_hi_eq (c := c.Yof i) (A := c.Fof) (fun k => Fof_valid c hD hvalid k)
  rw [RatInterval.finRange_map_sum] at hlo hhi
  show max (-(RatInterval.dot (c.Yof i) c.Fof).lo) (RatInterval.dot (c.Yof i) c.Fof).hi
    = (max (-(c.loV i)) (c.hiV i) : ℚ) / (c.E : ℚ)
  rw [hlo, hhi, sum_loV_eq c hD i, sum_hiV_eq c hD i]
  rw [show -((c.loV i : ℚ) / (c.E : ℚ)) = -(c.loV i : ℚ) / (c.E : ℚ) by ring]
  exact (max_div_right (Epos c hD).le (-(c.loV i : ℚ)) (c.hiV i : ℚ)).symm

/-! ## 2. checker（纯 ℤ，九条判据） -/

/-- **纯函数 checker**：`Dcom > 0`；`denEta/denK/rhoDen > 0`；`0 ≤ numEta`；`K < 1`；
`Fm` 区间合法；`∀i, max(−loV i)(hiV i)·denEta ≤ numEta·E`（= `hηb`）；
`numEta·denK·rhoDen + numK·rhoNum·denEta < rhoNum·denEta·denK`（= `hres`）。 -/
def etaCheck (c : EtaResCert) : Bool :=
  decide (0 < c.Dcom) && decide (0 < c.denEta) && decide (0 < c.denK) && decide (0 < c.rhoDen)
    && decide (0 ≤ c.numEta) && decide (c.numK < c.denK)
    && decide (∀ k : Fin 12, c.loF k ≤ c.hiF k)
    && decide (∀ i : Fin 12, max (-(c.loV i)) (c.hiV i) * c.denEta ≤ c.numEta * c.E)
    && decide (c.numEta * c.denK * c.rhoDen + c.numK * c.rhoNum * c.denEta
        < c.rhoNum * c.denEta * c.denK)

/-! ## 3. soundness：`hηb ∧ hη0 ∧ hres` -/

theorem etaCheck_sound {c : EtaResCert} (h : c.etaCheck = true) :
    (∀ i : Fin 12,
        (((incrMatVec c.Yof c.Fof i).abs).hi : ℝ) ≤ (c.numEta : ℝ) / (c.denEta : ℝ))
      ∧ (0 ≤ (c.numEta : ℝ) / (c.denEta : ℝ))
      ∧ ((c.numEta : ℝ) / (c.denEta : ℝ)
          + ((c.numK : ℝ) / (c.denK : ℝ)) * ((c.rhoNum : ℝ) / (c.rhoDen : ℝ))
          < (c.rhoNum : ℝ) / (c.rhoDen : ℝ)) := by
  simp only [etaCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hdenEta⟩, hdenK⟩, hrhoDen⟩, hnumEta⟩, hK1⟩, hvalid⟩, hη⟩, hres⟩ := h
  have hDQ : (0 : ℚ) < (c.Dcom : ℚ) := by exact_mod_cast hD
  have hEtaQ : (0 : ℚ) < (c.denEta : ℚ) := by exact_mod_cast hdenEta
  have hKQ : (0 : ℚ) < (c.denK : ℚ) := by exact_mod_cast hdenK
  have hRhoQ : (0 : ℚ) < (c.rhoDen : ℚ) := by exact_mod_cast hrhoDen
  have hEpos := Epos c hD
  -- 每个 i：max(-loV, hiV)/E ≤ numEta/denEta
  have hbQ : ∀ i : Fin 12,
      (max (-(c.loV i)) (c.hiV i) : ℚ) / (c.E : ℚ) ≤ (c.numEta : ℚ) / (c.denEta : ℚ) := by
    intro i
    have hcross : (max (-(c.loV i)) (c.hiV i) : ℚ) * (c.denEta : ℚ)
        ≤ (c.numEta : ℚ) * (c.E : ℚ) := by
      rw [← int_cast_max_neg (c.loV i) (c.hiV i)]
      exact_mod_cast hη i
    exact (div_le_div_iff₀ hEpos hEtaQ).mpr hcross
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [abs_hi_eq c hD hvalid i]
    exact_mod_cast hbQ i
  · have h0 : (0 : ℚ) ≤ (c.numEta : ℚ) / (c.denEta : ℚ) :=
      div_nonneg (by exact_mod_cast hnumEta) hEtaQ.le
    exact_mod_cast h0
  · have hcross : (c.numEta : ℚ) * (c.denK : ℚ) * (c.rhoDen : ℚ)
        + (c.numK : ℚ) * (c.rhoNum : ℚ) * (c.denEta : ℚ)
        < (c.rhoNum : ℚ) * (c.denEta : ℚ) * (c.denK : ℚ) := by
      exact_mod_cast hres
    have hne1 : (c.denEta : ℚ) ≠ 0 := ne_of_gt hEtaQ
    have hne2 : (c.denK : ℚ) ≠ 0 := ne_of_gt hKQ
    have hne3 : (c.rhoDen : ℚ) ≠ 0 := ne_of_gt hRhoQ
    have h1 : (c.numEta : ℚ) / (c.denEta : ℚ)
        + ((c.numK : ℚ) / (c.denK : ℚ)) * ((c.rhoNum : ℚ) / (c.rhoDen : ℚ))
        < (c.rhoNum : ℚ) / (c.rhoDen : ℚ) := by
      field_simp
      linarith [hcross]
    exact_mod_cast h1

/-! ## 4. 具体实例（机制演练）：通过 / 被拒（**具体实例留槽**：把 Fm 的真实端点填进来即可） -/

/-- 演练数据：`Dcom = 100`，`Y = I`，`Fm_0 = [0,1]`（其余 `[0,0]`），`η = 1`，`K = 1/10`，`ρ = 2`。 -/
def numY1 : Fin 12 → Fin 12 → ℤ := fun i k => if i = k then 100 else 0

def loF1 : Fin 12 → ℤ := fun _ => 0

def hiF1 : Fin 12 → ℤ := fun k => if k = 0 then 100 else 0

/-- 诚实实例：真实 `max_i ((incrMatVec Y Fm i).abs).hi = 1`，声称 `η = 1`；`η + K·ρ = 1.2 < ρ = 2` ✓ -/
def certEtaOK : EtaResCert :=
  { Dcom := 100, numY := numY1, loF := loF1, hiF := hiF1, numEta := 1, denEta := 1,
    numK := 10, denK := 100, rhoNum := 2, rhoDen := 1 }

/-- 说谎实例：把 `η` **压成 0**（真实需要 `≥ 1`）—— 其余数据逐字相同。 -/
def certEtaLIE : EtaResCert :=
  { Dcom := 100, numY := numY1, loF := loF1, hiF := hiF1, numEta := 0, denEta := 1,
    numK := 10, denK := 100, rhoNum := 2, rhoDen := 1 }

/-- 另一条说谎：`hres` 被破坏（`ρ` 压到 `1`，则 `η + K·ρ = 1.1 > 1`）。 -/
def certEtaLIE2 : EtaResCert :=
  { Dcom := 100, numY := numY1, loF := loF1, hiF := hiF1, numEta := 1, denEta := 1,
    numK := 10, denK := 100, rhoNum := 1, rhoDen := 1 }

/-- 机制读数：真实 `max_i max(−loV i)(hiV i)`（`E` 格）第 0 行为 `10000`，其余 `0`。 -/
theorem certEtaOK_hiV (i : Fin 12) :
    max (-(certEtaOK.loV i)) (certEtaOK.hiV i) = if i = 0 then 10000 else 0 := by
  fin_cases i <;> decide

/-- **诚实实例通过内核检查**。 -/
theorem certEtaOK_check : certEtaOK.etaCheck = true := by decide

/-- **说谎实例 1（`η` 压成 0）被内核拒绝**。 -/
theorem certEtaLIE_rejected : certEtaLIE.etaCheck = false := by decide

/-- **说谎实例 2（`hres` 被破坏）被内核拒绝**。 -/
theorem certEtaLIE2_rejected : certEtaLIE2.etaCheck = false := by decide

/-- 诚实实例的 `hηb`：`∀ i, ((incrMatVec Y Fm i).abs).hi ≤ η = 1`。 -/
theorem certEtaOK_hηb :
    ∀ i : Fin 12, (((incrMatVec certEtaOK.Yof certEtaOK.Fof i).abs).hi : ℝ)
      ≤ (certEtaOK.numEta : ℝ) / (certEtaOK.denEta : ℝ) :=
  (etaCheck_sound certEtaOK_check).1

/-- 诚实实例的 `hη0`：`0 ≤ η`。 -/
theorem certEtaOK_hη0 : 0 ≤ (certEtaOK.numEta : ℝ) / (certEtaOK.denEta : ℝ) :=
  (etaCheck_sound certEtaOK_check).2.1

/-- 诚实实例的 `hres`：`η + K·ρ < ρ`。 -/
theorem certEtaOK_hres :
    (certEtaOK.numEta : ℝ) / (certEtaOK.denEta : ℝ)
      + ((certEtaOK.numK : ℝ) / (certEtaOK.denK : ℝ))
        * ((certEtaOK.rhoNum : ℝ) / (certEtaOK.rhoDen : ℝ))
      < (certEtaOK.rhoNum : ℝ) / (certEtaOK.rhoDen : ℝ) :=
  (etaCheck_sound certEtaOK_check).2.2

end EtaResCert

end N11Formalization
