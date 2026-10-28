import N11Formalization.FmAdjReadout
import N11Formalization.EtaResCert
import N11Formalization.HsumPayload
import N11Formalization.EtaResCons

/-!
# `EtaFmEnclosure`：消费点 `hηb` 的**取整包络层**（`eta-instance` 线的具名义务 ③）

生成器：`evidence/eta-instance/gen_eta_enclosure.py`（数据**逐字解析**自
`evidence/tower-bc/scratch/fmCert12_data2.lean`，不手抄 ✗）。

**三层口径（本件 = L1 + L2 + L3；`hηb` 组装在下一件）**：
```
L1 数据层：`EtaDcom = 2^320`（= 根内 `HsumPayload.D` **同网格** ⇒ `numY` 原样可用 ✓）；
          `etaLoF = ⌊lo·Dcom⌋`、`etaHiF = ⌈hi·Dcom⌉`（`Fin 12 → ℤ`）
L2 取整包络层：`etaLoF k / Dcom ≤ (fmCert lamCert D k).lo` 且 `(fmCert lamCert D k).hi ≤ etaHiF k / Dcom`
          ⇒ 包络**只大不小** ⇒ `FmW ⊇ 真 Fm`（**仍 sound** ✓，不是放宽端点 ✗）
L3 组装：`FmW : Fin 12 → RatInterval`（= 将来 `EtaResCert.Fof` 的取值，`rfl` 级 ✓）+ `enc_all`
后续（下一件）：**单调性层**（`incrMatVec` 对区间参数向外单调）+ `etaCheck` 实例 `decide` ⇒ `hηb` **关于真 `Fm`** ✓
```

**独立复核**：`evidence/eta-instance/check_fmdata.py` ==> `check_fmdata.report.txt`
（用**我自己的 12 个精确端点**（前 5 = `FmLagReadout.res_*`，后 7 = `FmAdjReadout.BC_fm_j*`）逐位复核：
`ENCLOSURE 12/12 = True`，且 `loF/etaHiF` 与 floor/ceil **精确命中** ✓）。

**L2 的证法（口径）**：读出（kernel-proved）把 `(fmCert … k).lo/.hi` 换成**字面量** ⇒
`div_le_div_iff₀` 化**纯 ℤ 交叉相乘** ⇒ `norm_num`（不走 ℚ 上的 `decide` ✗、不用 `native_decide` ✗）。
-/

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## L1 数据层（copy 自 `tower-bc` 的数据件；逐位复核见 `check_fmdata.py`） -/

/-- 共同分母：**写成 `2^320` 的字面量**（与根内 `HsumPayload.Dz` 逐位同值）。

⚠ 实测口径：写成 `2 ^ 320` 会让 `norm_num` 因**指数阈值 256** 不求值并**逐条 warning** ⇒
`exit=0` 但**输出非 0 行** ⇒ 破判据 ✗（同事 `tower-bc` 先踩过）⇒ 这里直接写**字面量**（既不 warning、也不必抬全局阈值 ✓）。 -/
def EtaDcom : ℤ :=
  2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576

/-- 与根内 payload 同值（`rfl` 级核对）。 -/
theorem EtaDcom_eq_payload : EtaDcom = HsumPayload.Dz := rfl

/-- 12 个 `Fm` 分量的外舍下端（分子，`/EtaDcom`）。 -/
def etaLoF : Fin 12 → ℤ :=
  ![149112480823043781133040164101172009726492324001266527570000565927355660291072529, 90769857500939113922284748143413226743752649651836798280263894156746764713504059, 797569262492592655972733233243583262853625616545100586245725322241466472852707704, -14655799488801676666842654510386149592897382863129849276356833260467970686293216, 102701021495945740019454883534967123448819873338188939401694115387866526530889431, -3611946710315292664926709713527136453939861502708026307942948110004608814302802096, -3388271459968215054340261594729145920873845229611050646551307237184781729128478177, -3517648587335301766448475668844084970367714762632731866206037964512017938517781564, -3618890898328137273432268905008550821994033907912365465861520131196561938373298727, -6615946985871032848265868243884639446372601407308146237716837831499350880148173, 21060968790828602580050951512282379151803190905725538700410424997855225713757842, -1968740679606456802577173897994187985306015831244018368098489713071526047365225232]

/-- 12 个 `Fm` 分量的外舍上端（分子，`/EtaDcom`）。 -/
def etaHiF : Fin 12 → ℤ :=
  ![149138051071297714447759742306429285343106816663508758571536225543842966018853850, 90804500490226256740444192815660179830706723817272040750555314627458548060214652, 797796471122257062540232193795726495648796831412766759189289121713302286962587536, -14630306926742552825641922480035162641772648648742036507607420012510240318813623, 102705984402163003652064124175619605197536000337277274537344804517650162321949453, -3610934286619536324693357784597929852008732985533359170943835838984152231808703004, -3387266676552991566747209481349888826029985101771753067974809360236769755477674181, -3516664399171616533572810165742865773740887218513441937936822006288621143804805250, -3617939774669361285765613977158824663702777910224352463444934218241929868083574270, -6602757483388776722477787621896198634193532409576821491829308380144266400839475, 21087900814193775048002488134682193283083267696997802869121749811560328222701608, -1968051269829468317559918642241318027877461909899679698185448549468446372832269871]

theorem EtaDcom_pos : (0 : ℤ) < EtaDcom := by norm_num [EtaDcom]

theorem etaLoF_le_hiF : ∀ k : Fin 12, etaLoF k ≤ etaHiF k := by
  intro k
  fin_cases k <;> decide

/-! ## L3 组装（先给 `FmW`，便于 L2 的陈述） -/

/-- **外舍区间向量**（= 将来 `EtaResCert.Fof` 的取值，逐字同形 ⇒ `rfl` 级 ✓）。 -/
def FmW : Fin 12 → RatInterval := fun k =>
  ⟨((etaLoF k : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ),
   ((etaHiF k : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)⟩

theorem FmW_lo (k : Fin 12) : (FmW k).lo = ((etaLoF k : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := rfl

theorem FmW_hi (k : Fin 12) : (FmW k).hi = ((etaHiF k : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := rfl

/-! ## L2 的前置：`fmCert` 前 5 分量 = `residualIntervalLag cCert`（`dif_pos` + `rfl`） -/

theorem BC_fm_eq_lag_0 : fmCert lamCert D (0 : Fin 12) = residualIntervalLag cCert 0 := by
  rw [fmCert, dif_pos (by decide : (((0 : Fin 12) : ℕ)) < 5)]
  rfl

theorem BC_fm_eq_lag_1 : fmCert lamCert D (1 : Fin 12) = residualIntervalLag cCert 1 := by
  rw [fmCert, dif_pos (by decide : (((1 : Fin 12) : ℕ)) < 5)]
  rfl

theorem BC_fm_eq_lag_2 : fmCert lamCert D (2 : Fin 12) = residualIntervalLag cCert 2 := by
  rw [fmCert, dif_pos (by decide : (((2 : Fin 12) : ℕ)) < 5)]
  rfl

theorem BC_fm_eq_lag_3 : fmCert lamCert D (3 : Fin 12) = residualIntervalLag cCert 3 := by
  rw [fmCert, dif_pos (by decide : (((3 : Fin 12) : ℕ)) < 5)]
  rfl

theorem BC_fm_eq_lag_4 : fmCert lamCert D (4 : Fin 12) = residualIntervalLag cCert 4 := by
  rw [fmCert, dif_pos (by decide : (((4 : Fin 12) : ℕ)) < 5)]
  rfl

/-! ## L2 取整包络（**我的具名义务**）：逐分量 `loF/Dcom ≤ lo` 与 `hi ≤ hiF/Dcom` -/

theorem enc_lo_0 : ((etaLoF 0 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (0 : Fin 12)).lo := by
  rw [BC_fm_eq_lag_0, FmLagReadout.res_0_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_0 : (fmCert lamCert D (0 : Fin 12)).hi
    ≤ ((etaHiF 0 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_eq_lag_0, FmLagReadout.res_0_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_1 : ((etaLoF 1 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (1 : Fin 12)).lo := by
  rw [BC_fm_eq_lag_1, FmLagReadout.res_1_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_1 : (fmCert lamCert D (1 : Fin 12)).hi
    ≤ ((etaHiF 1 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_eq_lag_1, FmLagReadout.res_1_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_2 : ((etaLoF 2 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (2 : Fin 12)).lo := by
  rw [BC_fm_eq_lag_2, FmLagReadout.res_2_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_2 : (fmCert lamCert D (2 : Fin 12)).hi
    ≤ ((etaHiF 2 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_eq_lag_2, FmLagReadout.res_2_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_3 : ((etaLoF 3 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (3 : Fin 12)).lo := by
  rw [BC_fm_eq_lag_3, FmLagReadout.res_3_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_3 : (fmCert lamCert D (3 : Fin 12)).hi
    ≤ ((etaHiF 3 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_eq_lag_3, FmLagReadout.res_3_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_4 : ((etaLoF 4 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (4 : Fin 12)).lo := by
  rw [BC_fm_eq_lag_4, FmLagReadout.res_4_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_4 : (fmCert lamCert D (4 : Fin 12)).hi
    ≤ ((etaHiF 4 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_eq_lag_4, FmLagReadout.res_4_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_5 : ((etaLoF 5 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (5 : Fin 12)).lo := by
  rw [BC_fm_j5_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_5 : (fmCert lamCert D (5 : Fin 12)).hi
    ≤ ((etaHiF 5 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j5_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_6 : ((etaLoF 6 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (6 : Fin 12)).lo := by
  rw [BC_fm_j6_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_6 : (fmCert lamCert D (6 : Fin 12)).hi
    ≤ ((etaHiF 6 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j6_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_7 : ((etaLoF 7 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (7 : Fin 12)).lo := by
  rw [BC_fm_j7_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_7 : (fmCert lamCert D (7 : Fin 12)).hi
    ≤ ((etaHiF 7 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j7_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_8 : ((etaLoF 8 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (8 : Fin 12)).lo := by
  rw [BC_fm_j8_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_8 : (fmCert lamCert D (8 : Fin 12)).hi
    ≤ ((etaHiF 8 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j8_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_9 : ((etaLoF 9 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (9 : Fin 12)).lo := by
  rw [BC_fm_j9_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_9 : (fmCert lamCert D (9 : Fin 12)).hi
    ≤ ((etaHiF 9 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j9_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_10 : ((etaLoF 10 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (10 : Fin 12)).lo := by
  rw [BC_fm_j10_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_10 : (fmCert lamCert D (10 : Fin 12)).hi
    ≤ ((etaHiF 10 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j10_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_lo_11 : ((etaLoF 11 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ)
    ≤ (fmCert lamCert D (11 : Fin 12)).lo := by
  rw [BC_fm_j11_lo]
  rw [div_le_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem enc_hi_11 : (fmCert lamCert D (11 : Fin 12)).hi
    ≤ ((etaHiF 11 : ℤ) : ℚ) / ((EtaDcom : ℤ) : ℚ) := by
  rw [BC_fm_j11_hi]
  rw [le_div_iff₀ (by norm_num [EtaDcom] : (0 : ℚ) < ((EtaDcom : ℤ) : ℚ))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

/-! ## L3 打包：`FmW ⊇ 真 Fm`（逐分量 `Contains`） -/

theorem enc_0 : RatInterval.Contains (FmW 0) (fmCert lamCert D (0 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_0
  · rw [FmW_hi]
    exact enc_hi_0

theorem enc_1 : RatInterval.Contains (FmW 1) (fmCert lamCert D (1 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_1
  · rw [FmW_hi]
    exact enc_hi_1

theorem enc_2 : RatInterval.Contains (FmW 2) (fmCert lamCert D (2 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_2
  · rw [FmW_hi]
    exact enc_hi_2

theorem enc_3 : RatInterval.Contains (FmW 3) (fmCert lamCert D (3 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_3
  · rw [FmW_hi]
    exact enc_hi_3

theorem enc_4 : RatInterval.Contains (FmW 4) (fmCert lamCert D (4 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_4
  · rw [FmW_hi]
    exact enc_hi_4

theorem enc_5 : RatInterval.Contains (FmW 5) (fmCert lamCert D (5 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_5
  · rw [FmW_hi]
    exact enc_hi_5

theorem enc_6 : RatInterval.Contains (FmW 6) (fmCert lamCert D (6 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_6
  · rw [FmW_hi]
    exact enc_hi_6

theorem enc_7 : RatInterval.Contains (FmW 7) (fmCert lamCert D (7 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_7
  · rw [FmW_hi]
    exact enc_hi_7

theorem enc_8 : RatInterval.Contains (FmW 8) (fmCert lamCert D (8 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_8
  · rw [FmW_hi]
    exact enc_hi_8

theorem enc_9 : RatInterval.Contains (FmW 9) (fmCert lamCert D (9 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_9
  · rw [FmW_hi]
    exact enc_hi_9

theorem enc_10 : RatInterval.Contains (FmW 10) (fmCert lamCert D (10 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_10
  · rw [FmW_hi]
    exact enc_hi_10

theorem enc_11 : RatInterval.Contains (FmW 11) (fmCert lamCert D (11 : Fin 12)) := by
  refine ⟨?_, ?_⟩
  · rw [FmW_lo]
    exact enc_lo_11
  · rw [FmW_hi]
    exact enc_hi_11

theorem enc_all : ∀ k : Fin 12, RatInterval.Contains (FmW k) (fmCert lamCert D k) := by
  intro k
  fin_cases k
  · exact enc_0
  · exact enc_1
  · exact enc_2
  · exact enc_3
  · exact enc_4
  · exact enc_5
  · exact enc_6
  · exact enc_7
  · exact enc_8
  · exact enc_9
  · exact enc_10
  · exact enc_11

/-!
## L4 单调性层：区间点积 / `abs.hi` 对区间参数**向外**单调

工具全部根内已有（`dot_lo_eq`/`dot_hi_eq`/`finRange_map_sum`/`loTerm`/`hiTerm` ⇒ HsumCert；
`abs A = ⟨…, max (-A.lo) A.hi⟩` ⇒ Vector）⇒ 本层**零新数学**（只是把单调性显式化）。
-/

theorem etaLoTerm_mono {c : Fin 12 → ℚ} {A B : Fin 12 → RatInterval} (k : Fin 12)
    (h1 : (B k).lo ≤ (A k).lo) (h2 : (A k).hi ≤ (B k).hi) :
    loTerm c B k ≤ loTerm c A k := by
  unfold loTerm
  by_cases hc : 0 ≤ c k
  · rw [if_pos hc, if_pos hc]
    exact mul_le_mul_of_nonneg_left h1 hc
  · rw [if_neg hc, if_neg hc]
    exact mul_le_mul_of_nonpos_left h2 (not_le.mp hc).le

theorem etaHiTerm_mono {c : Fin 12 → ℚ} {A B : Fin 12 → RatInterval} (k : Fin 12)
    (h1 : (B k).lo ≤ (A k).lo) (h2 : (A k).hi ≤ (B k).hi) :
    hiTerm c A k ≤ hiTerm c B k := by
  unfold hiTerm
  by_cases hc : 0 ≤ c k
  · rw [if_pos hc, if_pos hc]
    exact mul_le_mul_of_nonneg_left h2 hc
  · rw [if_neg hc, if_neg hc]
    exact mul_le_mul_of_nonpos_left h1 (not_le.mp hc).le

theorem etaDot_lo_mono (c : Fin 12 → ℚ) {A B : Fin 12 → RatInterval}
    (hAB : ∀ k, Contains (B k) (A k)) (hA : ∀ k, Valid (A k)) :
    (dot c B).lo ≤ (dot c A).lo := by
  have hB : ∀ k, (B k).lo ≤ (B k).hi := fun k =>
    le_trans (hAB k).1 (le_trans (hA k) (hAB k).2)
  rw [dot_lo_eq c B hB, dot_lo_eq c A hA, finRange_map_sum, finRange_map_sum]
  exact Finset.sum_le_sum fun k _ => etaLoTerm_mono k (hAB k).1 (hAB k).2

theorem etaDot_hi_mono (c : Fin 12 → ℚ) {A B : Fin 12 → RatInterval}
    (hAB : ∀ k, Contains (B k) (A k)) (hA : ∀ k, Valid (A k)) :
    (dot c A).hi ≤ (dot c B).hi := by
  have hB : ∀ k, (B k).lo ≤ (B k).hi := fun k =>
    le_trans (hAB k).1 (le_trans (hA k) (hAB k).2)
  rw [dot_hi_eq c A hA, dot_hi_eq c B hB, finRange_map_sum, finRange_map_sum]
  exact Finset.sum_le_sum fun k _ => etaHiTerm_mono k (hAB k).1 (hAB k).2

/-- **单调性主引理**：`A`（窄）逐分量含于 `B`（宽）⇒ `incrMatVec Y · i` 的 `abs.hi` 单调。 -/
theorem etaAbs_hi_mono (Y : Fin 12 → Fin 12 → ℚ) {A B : Fin 12 → RatInterval}
    (hAB : ∀ k, Contains (B k) (A k)) (hA : ∀ k, Valid (A k)) (i : Fin 12) :
    ((incrMatVec Y A i).abs).hi ≤ ((incrMatVec Y B i).abs).hi := by
  have hlo := etaDot_lo_mono (Y i) hAB hA
  have hhi := etaDot_hi_mono (Y i) hAB hA
  show max (-(dot (Y i) A).lo) (dot (Y i) A).hi ≤ max (-(dot (Y i) B).lo) (dot (Y i) B).hi
  exact max_le_max (neg_le_neg hlo) hhi

/-! ## L4b 真 `Fm = fmCert lamCert D` 的 12 条合法性（由读出字面量比较 ⇒ **无条件** ✓，不依赖 `hD`） -/

theorem etaValid_0 : Valid (fmCert lamCert D (0 : Fin 12)) := by
  show (fmCert lamCert D (0 : Fin 12)).lo ≤ (fmCert lamCert D (0 : Fin 12)).hi
  rw [BC_fm_eq_lag_0, FmLagReadout.res_0_lo, FmLagReadout.res_0_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_1 : Valid (fmCert lamCert D (1 : Fin 12)) := by
  show (fmCert lamCert D (1 : Fin 12)).lo ≤ (fmCert lamCert D (1 : Fin 12)).hi
  rw [BC_fm_eq_lag_1, FmLagReadout.res_1_lo, FmLagReadout.res_1_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_2 : Valid (fmCert lamCert D (2 : Fin 12)) := by
  show (fmCert lamCert D (2 : Fin 12)).lo ≤ (fmCert lamCert D (2 : Fin 12)).hi
  rw [BC_fm_eq_lag_2, FmLagReadout.res_2_lo, FmLagReadout.res_2_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_3 : Valid (fmCert lamCert D (3 : Fin 12)) := by
  show (fmCert lamCert D (3 : Fin 12)).lo ≤ (fmCert lamCert D (3 : Fin 12)).hi
  rw [BC_fm_eq_lag_3, FmLagReadout.res_3_lo, FmLagReadout.res_3_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_4 : Valid (fmCert lamCert D (4 : Fin 12)) := by
  show (fmCert lamCert D (4 : Fin 12)).lo ≤ (fmCert lamCert D (4 : Fin 12)).hi
  rw [BC_fm_eq_lag_4, FmLagReadout.res_4_lo, FmLagReadout.res_4_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_5 : Valid (fmCert lamCert D (5 : Fin 12)) := by
  show (fmCert lamCert D (5 : Fin 12)).lo ≤ (fmCert lamCert D (5 : Fin 12)).hi
  rw [BC_fm_j5_lo, BC_fm_j5_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_6 : Valid (fmCert lamCert D (6 : Fin 12)) := by
  show (fmCert lamCert D (6 : Fin 12)).lo ≤ (fmCert lamCert D (6 : Fin 12)).hi
  rw [BC_fm_j6_lo, BC_fm_j6_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_7 : Valid (fmCert lamCert D (7 : Fin 12)) := by
  show (fmCert lamCert D (7 : Fin 12)).lo ≤ (fmCert lamCert D (7 : Fin 12)).hi
  rw [BC_fm_j7_lo, BC_fm_j7_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_8 : Valid (fmCert lamCert D (8 : Fin 12)) := by
  show (fmCert lamCert D (8 : Fin 12)).lo ≤ (fmCert lamCert D (8 : Fin 12)).hi
  rw [BC_fm_j8_lo, BC_fm_j8_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_9 : Valid (fmCert lamCert D (9 : Fin 12)) := by
  show (fmCert lamCert D (9 : Fin 12)).lo ≤ (fmCert lamCert D (9 : Fin 12)).hi
  rw [BC_fm_j9_lo, BC_fm_j9_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_10 : Valid (fmCert lamCert D (10 : Fin 12)) := by
  show (fmCert lamCert D (10 : Fin 12)).lo ≤ (fmCert lamCert D (10 : Fin 12)).hi
  rw [BC_fm_j10_lo, BC_fm_j10_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_11 : Valid (fmCert lamCert D (11 : Fin 12)) := by
  show (fmCert lamCert D (11 : Fin 12)).lo ≤ (fmCert lamCert D (11 : Fin 12)).hi
  rw [BC_fm_j11_lo, BC_fm_j11_hi]
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < _)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < _)]
  norm_cast

theorem etaValid_all : ∀ k : Fin 12, Valid (fmCert lamCert D k) := by
  intro k
  fin_cases k
  · exact etaValid_0
  · exact etaValid_1
  · exact etaValid_2
  · exact etaValid_3
  · exact etaValid_4
  · exact etaValid_5
  · exact etaValid_6
  · exact etaValid_7
  · exact etaValid_8
  · exact etaValid_9
  · exact etaValid_10
  · exact etaValid_11

/-! ## L5 `EtaResCert` 实例（`Y` = 根内真实 payload 分子，同 `2^320` 网格；`Fm` = 外舍 `FmW`） -/

/-- 消费口径的 `EtaResCert` 实例：`numY` 直接用 `HsumPayload.numYz`（**零重标定** ✓）。 -/
def cEta : EtaResCert :=
  { Dcom := EtaDcom
    numY := HsumPayload.numYz
    loF := etaLoF
    hiF := etaHiF
    numEta := 1
    denEta := 100000000000000
    numK := HsumPayload.numKz
    denK := HsumPayload.Ez
    rhoNum := 4835703278458517
    rhoDen := 4835703278458516698824704 }

theorem cEta_Fof : cEta.Fof = FmW := rfl

theorem cEta_Yof : cEta.Yof = HsumPayload.certReal.Yof := rfl

/-- `η` 的取值 = `EtaResCons.etaCons`（与 `hresCons` 配套 ✓）。 -/
theorem cEta_eta : (cEta.numEta : ℝ) / (cEta.denEta : ℝ) = etaCons := by
  norm_num [cEta, etaCons]

/-- **`etaCheck` 通过内核检查**（纯 ℤ 交叉相乘 ⇒ `decide`；`E = EtaDcom² = 2^640`，与 `HsumPayload` 同量级 ✓）。 -/
theorem cEta_check : cEta.etaCheck = true := by decide

/-! ## L6 最终 `hηb`（**关于真 `Fm = fmCert lamCert D`** ✓；C1270 对象同一性守住 ✓） -/

/-- **消费点 `hηb` 的具体实例**：`∀ i, ((incrMatVec Y (fmCert lamCert D) i).abs).hi ≤ η`，`η = etaCons`。

证明路线（三层）：`FmW ⊇ 真 Fm`（L2/L3，kernel ✓）⇒ 单调性（L4）⇒ `etaCheck` 对 `FmW` 的界（L5，`decide` ✓）。 -/
theorem eta_hηb : ∀ i : Fin 12,
    (((incrMatVec HsumPayload.certReal.Yof (fmCert lamCert D) i).abs).hi : ℝ) ≤ etaCons := by
  intro i
  have hW := (EtaResCert.etaCheck_sound cEta_check).1 i
  have hmono := etaAbs_hi_mono HsumPayload.certReal.Yof (fun k => enc_all k) etaValid_all i
  have hW' : (((incrMatVec HsumPayload.certReal.Yof FmW i).abs).hi : ℝ) ≤ etaCons := by
    rw [cEta_Fof, cEta_Yof, cEta_eta] at hW
    exact hW
  exact le_trans (by exact_mod_cast hmono) hW'

/-- 消费口径的**同一件事**：`hηb` 与消费点的 `hFm` 面对同一个 `Fm` ✓（`hFm` 由 `FmAssembly.mem_fmCert_cert D hD` 供给）。 -/
theorem eta_hηb_pair (hFm : ∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem cCertR k)) :
    (∀ k : Fin 12, (fmCert lamCert D k).Mem (TCSystem cCertR k)) ∧
      (∀ i : Fin 12,
        (((incrMatVec HsumPayload.certReal.Yof (fmCert lamCert D) i).abs).hi : ℝ) ≤ etaCons) :=
  ⟨hFm, eta_hηb⟩

end N11Formalization

