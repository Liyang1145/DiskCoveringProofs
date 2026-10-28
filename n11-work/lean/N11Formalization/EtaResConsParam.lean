import N11Formalization.HsumPayload
import N11Formalization.BoxRstar
import N11Formalization.EtaResCons

/-!
# `EtaResConsParam` — `EtaResCons` 三条数值前提的**参数化候选件**(R267-T11,etares-param)

**对象**:`N11Formalization.EtaResCons` 的 `hK1` / `hK'1` / `hresCons`(消费点
`nd_end_to_end_right` 的六项数值前提中随 K/K' 重声明而变的那些)。

**改造口径(如实)**:
* 消费点侧 `nd_end_to_end_right (Y) (K η K' : ℝ) …` 本来就对 `K/K'/η` 全称量化——
  ℝ 层参数化早已存在;**没被参数化的是数值判据的解除**:旧件把旧
  `numKz/numKRz/Ez`(经 `certReal/certRealR`)与 `rhoCert` 展开内嵌在证明里。
* 本件把三条改成:数据级参数 `(numK denK : ℤ)`(K = numK/denK、denK > 0)+ **逐条数值假设**,
  ℝ 层结论与旧三条**同形**。旧数字 → 假设的对照(逐条):
  - `hK1 : KCons < 1`:旧数字在 `certReal.check` 的 `decide`(ℤ `numKz < Ez` 等)里,
    本件换成显式假设 `hlt : numK < denK`(新值判据 = brief §0 的 `max_i rowZ_B i < D_B²`);
  - `hK'1 : KConsR < 1`:同形,`numKRz < Ez`,换成 `hltR`(同一引理另喂);
  - `hresCons`:旧 `hKle : KCons ≤ 1/2`(L54–57 的 `norm_num [KCons, certReal, numKz, Ez, Dz]`,
    **内嵌旧 K ≤ 1/2 展开**)换成显式假设 `hle : 2 * numK ≤ denK`;ρ/η 侧的旧数字
    (`rhoCert = 4835703278458517/2^82`、`etaCons = 1/10^14`)**不变**,
    对应假设 `hρ0/hη` 由旧件同款 `norm_num` 原样解除。
* **不能泛化的(精确)**:`hlt/hle` 是纯数据命题,对新值 `numK_B/numKR_B` 不可证也不该证——
  它们由 T7 端点 + `k_budget.py` 复算后在**新 payload 件**里 `decide`(ℤ,合法)解除;
  旧 payload 的具名定理(`certReal_K_lt_one` 等)对 `numK_B ≠ numKz` 直接不适用,
  这正是 brief §0「K 必须重声明」的形式化对应物。
* **校准实例(§3)**:参数化引理在**旧数据**上精确重现旧三条(`hK1_old_calib` 等三条),
  证明接口没走样;Lead 落根时可整段删除 §3。
* 另附 `k_le_half_of_int`(K ≤ 1/2 的数据级引理,对 `numKR_B` 同样适用)与
  `k_nonneg_of_int`(`hK0/hK'0` 的数据级来源,喂满消费点六前提)。

**新值实例化计划(详见 evidence/etares-param/T11-REPORT.md)**:
等 T7 的 49 格端点(98 个 ℚ 字面量)+ `k_budget.py` 复算出 `numK_B/numKR_B`(D_B = 2^320 不变,
E = D_B² = 旧 `Ez` 不变)后:
1. `hK1_B := k_lt_one_of_int numK_B Ez (by decide) (by decide)` —— 唯一真判据
   `max_i rowZ_B i < D_B²` 即第二个 `decide`(或由新 payload 的 `check_sound .2.2` 免费给出);
2. `hK'1_B := k_lt_one_of_int numKR_B Ez (by decide) (by decide)`(或 `checkR_sound .2.2`);
3. `hresCons_B := hresCons_of_int numK_B Ez etaCons rhoCertR (by decide) (by decide)
   (by norm_num [rhoCertR, rhoCert]) (by norm_num [etaCons, rhoCertR, rhoCert])`
   —— 唯一新增数值判据 = `2 * numK_B ≤ Ez`(K_B ≤ 1/2)。
-/

namespace N11Formalization.EtaResConsParam

/-! ## 1. 数据级 → ℝ 级(K := numK/denK,`denK > 0`;判据全在 ℤ,结论在 ℝ) -/

/-- `0 ≤ numK`、`0 < denK` ⇒ `0 ≤ K`(= `HsumCert.check_sound` 第二分量的无条件数据级形态)。 -/
theorem k_nonneg_of_int (numK denK : ℤ) (hden : 0 < denK) (h0 : 0 ≤ numK) :
    (numK : ℝ) / (denK : ℝ) ≥ 0 := by
  have h1 : 0 ≤ (numK : ℚ) / (denK : ℚ) :=
    div_nonneg (by exact_mod_cast h0) (by exact_mod_cast hden.le)
  exact_mod_cast h1

/-- `numK < denK`(`denK > 0`)⇒ `K < 1`。新值下这就是唯一真判据 `max_i rowZ_B i < D_B²`。 -/
theorem k_lt_one_of_int (numK denK : ℤ) (hden : 0 < denK) (hlt : numK < denK) :
    (numK : ℝ) / (denK : ℝ) < 1 := by
  have hKQ : (0 : ℚ) < (denK : ℚ) := by exact_mod_cast hden
  have h1 : (numK : ℚ) / (denK : ℚ) < 1 := by
    rw [div_lt_one hKQ]
    exact_mod_cast hlt
  exact_mod_cast h1

/-- `2 * numK ≤ denK`(`denK > 0`)⇒ `K ≤ 1/2`。旧 `hresCons` L54–57 内嵌展开的假设化。
(全 ℝ 层:ℤ→ℚ 中转会撞 `Rat.divInt` 归一形与 ofInt/ofNat 常数原子不一致,实测必红。) -/
theorem k_le_half_of_int (numK denK : ℤ) (hden : 0 < denK) (hle : 2 * numK ≤ denK) :
    (numK : ℝ) / (denK : ℝ) ≤ 1 / 2 := by
  have hdenR : (0 : ℝ) < (denK : ℝ) := by exact_mod_cast hden
  have h2R : (2 : ℝ) * (numK : ℝ) ≤ (denK : ℝ) := by exact_mod_cast hle
  refine (div_le_div_iff₀ hdenR (by norm_num : (0 : ℝ) < 2)).mpr ?_
  linarith

/-! ## 2. `hres` 的参数化(ℝ 层,纯线性;旧 L63 `nlinarith` 的内容) -/

/-- `0 ≤ ρ`、`K ≤ 1/2`、`η < ρ/2` ⇒ `η + K·ρ < ρ`。
旧 `hresCons` 的算术骨架;K ≤ 1/2 是**充分**路线(brief §0 余量 113 倍,如实)。 -/
theorem hres_of (K η ρ : ℝ) (hρ0 : 0 ≤ ρ) (hKle : K ≤ 1 / 2) (hη : η < ρ / 2) :
    η + K * ρ < ρ := by
  have h1 : K * ρ ≤ (1 : ℝ) / 2 * ρ := mul_le_mul_of_nonneg_right hKle hρ0
  linarith

/-- 一步到位的新值形态:`hresCons_of_int numK denK η ρ …` 直接吃 ℤ 判据。 -/
theorem hresCons_of_int (numK denK : ℤ) (η ρ : ℝ)
    (hden : 0 < denK) (hle : 2 * numK ≤ denK) (hρ0 : 0 ≤ ρ) (hη : η < ρ / 2) :
    η + (numK : ℝ) / (denK : ℝ) * ρ < ρ :=
  hres_of _ _ _ hρ0 (k_le_half_of_int numK denK hden hle) hη

/-! ## 2bis. `K'` 侧同件复用(Lead 已裁,R267:`nd_end_to_end_right` 六槽形状不动,
`K'` 只需 `K' < 1`;`K_B ≤ 1/2 ∧ K'_B ≤ 1/2` 是 hresCons/hK1 式证明的**内部条件**。
故 `k_le_half_of_int` 为**辅助供给引理**:重证 `hresCons_B` 时作输入使用,不进消费接口)。

`k_lt_one_of_int` / `k_le_half_of_int` 对 `numKR_B` 原样适用,无需另写。 -/

/-! ## 3. 校准实例(**旧值**):参数化引理在旧数据上精确重现 `EtaResCons` 三条。
Lead 落根时本节可整段删除;删除后本件不依赖旧 payload 数字。 -/

/-- 校准:`hK1` 的参数化重现(旧 `numKz/Ez`)。 -/
theorem hK1_old_calib : KCons < 1 :=
  k_lt_one_of_int N11Formalization.HsumPayload.numKz N11Formalization.HsumPayload.Ez
    (by decide) (by decide)

/-- 校准:`hK'1` 的参数化重现(旧 `numKRz/Ez`)。 -/
theorem hK'1_old_calib : KConsR < 1 :=
  k_lt_one_of_int N11Formalization.HsumPayload.numKRz N11Formalization.HsumPayload.Ez
    (by decide) (by decide)

/-- 校准:`hresCons` 的参数化重现(ρ/η 侧假设用旧件同款 `norm_num` 解除)。 -/
theorem hresCons_old_calib : etaCons + KCons * rhoCertR < rhoCertR :=
  hresCons_of_int N11Formalization.HsumPayload.numKz N11Formalization.HsumPayload.Ez
    etaCons rhoCertR
    (by decide) (by decide)
    (by norm_num [rhoCertR, rhoCert]) (by norm_num [etaCons, rhoCertR, rhoCert])

end N11Formalization.EtaResConsParam
