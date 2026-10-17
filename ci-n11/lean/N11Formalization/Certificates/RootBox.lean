import N11Formalization.HexFloat

/-!
# 根证书切片：不可信数据 → checker → soundness → 具体通过 → 实数不等式（GUIDE §5）

**结构**（GUIDE §5 的推荐结构）：
* 不可信生成器（Python）只产出**数据**：源 JSON 的十六进制字面量、其解码结果、
  以及精确有理包络的整数分子/分母；
* 本文件定义纯函数 `RootBoxCert.check : RootBoxCert → Bool` 并**证明其语义（soundness）**；
* 最后用 `decide` 在内核里**证明具体数据通过**。

checker 只使用 `ℤ`/结构相等判据，因此 `decide` 是**真正的内核求值**
（注意：`ℚ` 的顺序/相等实例在内核里不可归约，所以本文件的 checker 不做 `ℚ` 比较——
所有有理比较都换成交叉相乘后的整数比较）。

### 数据来源（只读）
`research-2026/team-current/lead/repaired_tc_krawczyk.json` 的 `certificate` 字段，
sha256 见 `manifests/source-hashes.json`。

### 真实等级
本文件全部 `proved-exact`（内核检查）：字面量→精确有理数的语义、checker 的 soundness、
具体实例通过。但**不**证明 C891 的核心命题（"盒内存在唯一根"）——那在
`Conditional/RootSpec.lean` 中作为显式前提，尚未形式化。
-/

namespace N11Formalization

/-- 根盒证书：全部字段都是**不受信的输入数据**，其含义由 `check` 与随后的定理确定。 -/
structure RootBoxCert where
  /-- 盒半宽的源字面量。 -/
  radiusHex : String
  /-- 12 个坐标中心的源字面量。 -/
  centerHex : Fin 12 → String
  /-- 生成器声称的解码结果（会被 `checkProp` 与源字面量重新绑定）。 -/
  radius : HexFloat
  centers : Fin 12 → HexFloat
  /-- R 坐标精确包络下端的分子。 -/
  loNum : ℤ
  /-- 下端的（正整数）分母。 -/
  loDen : ℤ
  /-- 上端分子。 -/
  hiNum : ℤ
  /-- 上端分母。 -/
  hiDen : ℤ
  /-- R* 在 12 维坐标中的位置。 -/
  radiusIndex : Fin 12

namespace RootBoxCert

/-- 包络下端（有理解释）。 -/
def encLo (c : RootBoxCert) : ℚ := (c.loNum : ℚ) / (c.loDen : ℚ)

/-- 包络上端。 -/
def encHi (c : RootBoxCert) : ℚ := (c.hiNum : ℚ) / (c.hiDen : ℚ)

/-- **纯函数 checker**：只用 `ℤ` 判据，故 `decide` 可以真的把它跑出来。 -/
def check (c : RootBoxCert) : Bool :=
  decide (0 < c.loDen) &&
    decide (0 < c.hiDen) &&
    decide (c.loNum * c.hiDen ≤ c.hiNum * c.loDen) &&
    decide (50 * c.hiNum < 19 * c.hiDen)

/-- **checker 语义（soundness）**：整数交叉相乘判据 ⇒ 有理包络的有序性与阈值不等式。

这是把"不受信的整数数据"变成"关于有理数（进而实数）的命题"的那一步。 -/
theorem check_sound {c : RootBoxCert} (h : c.check = true) :
    0 < c.loDen ∧ 0 < c.hiDen ∧ c.encLo ≤ c.encHi ∧ c.encHi < 19 / 50 := by
  have h' := h
  simp only [RootBoxCert.check, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨hlo, hhi⟩, hord⟩, h50⟩ := h'
  have hloQ : (0 : ℚ) < (c.loDen : ℚ) := by exact_mod_cast hlo
  have hhiQ : (0 : ℚ) < (c.hiDen : ℚ) := by exact_mod_cast hhi
  refine ⟨hlo, hhi, ?_, ?_⟩
  · exact (div_le_div_iff₀ hloQ hhiQ).mpr (by exact_mod_cast hord)
  · have h50Q : (50 : ℚ) * (c.hiNum : ℚ) < 19 * (c.hiDen : ℚ) := by exact_mod_cast h50
    rw [RootBoxCert.encHi, div_lt_iff₀ hhiQ]
    linarith

/-- **checker 的主要语义（soundness，ℝ 版本）**：证书通过 ⇒ 任何落在包络内的实数 `< 19/50`。 -/
theorem check_sound_lt_R0 {c : RootBoxCert} (h : c.check = true) :
    ∀ R : ℝ, (c.encLo : ℝ) ≤ R → R ≤ (c.encHi : ℝ) → R < 19 / 50 := by
  intro R h1 h2
  obtain ⟨_, hhi, _, hlt⟩ := check_sound h
  have h3 : (c.encHi : ℝ) < ((19 : ℚ) / 50 : ℝ) := by exact_mod_cast hlt
  have h4 : ((19 : ℚ) / 50 : ℝ) = 19 / 50 := by norm_num
  linarith

end RootBoxCert

/-! ## 具体实例：源证书 `repaired_tc_krawczyk.json` 的原样数据 -/

/-- 源字面量：盒半宽。 -/
def srcRadiusHex : String := "0x1.12e0be826d695p-30"

/-- 生成器给出的解码结果。 -/
def decRadiusHex : HexFloat := ⟨false, [1], [1, 2, 14, 0, 11, 14, 8, 2, 6, 13, 6, 9, 5], -30⟩

/-- 源字面量：12 个坐标中心。 -/
def srcCenterHex : Fin 12 → String :=
  !["0x1.7cefd3e2947ffp-2",
    "0x1.5d05f6e5b8555p-2",
    "0x1.1f8fc82272cc5p-2",
    "0x1.88344da9606cbp-2",
    "0x1.178767aa02a21p-2",
    "-0x1.3207919fda6aep-3",
    "0x1.851a7cb8a18fbp-2",
    "-0x1.d2440d1cffcb4p-4",
    "-0x1.a3cad4ddf3cb9p-6",
    "-0x1.b382ad399e43dp-8",
    "-0x1.4536865654152p-6",
    "-0x1.b0b66f60b890dp-6"]

/-- 生成器给出的 12 个解码结果。 -/
def decCenterHex : Fin 12 → HexFloat :=
  ![
    ⟨false, [1], [7, 12, 14, 15, 13, 3, 14, 2, 9, 4, 7, 15, 15], -2⟩,
    ⟨false, [1], [5, 13, 0, 5, 15, 6, 14, 5, 11, 8, 5, 5, 5], -2⟩,
    ⟨false, [1], [1, 15, 8, 15, 12, 8, 2, 2, 7, 2, 12, 12, 5], -2⟩,
    ⟨false, [1], [8, 8, 3, 4, 4, 13, 10, 9, 6, 0, 6, 12, 11], -2⟩,
    ⟨false, [1], [1, 7, 8, 7, 6, 7, 10, 10, 0, 2, 10, 2, 1], -2⟩,
    ⟨true, [1], [3, 2, 0, 7, 9, 1, 9, 15, 13, 10, 6, 10, 14], -3⟩,
    ⟨false, [1], [8, 5, 1, 10, 7, 12, 11, 8, 10, 1, 8, 15, 11], -2⟩,
    ⟨true, [1], [13, 2, 4, 4, 0, 13, 1, 12, 15, 15, 12, 11, 4], -4⟩,
    ⟨true, [1], [10, 3, 12, 10, 13, 4, 13, 13, 15, 3, 12, 11, 9], -6⟩,
    ⟨true, [1], [11, 3, 8, 2, 10, 13, 3, 9, 9, 14, 4, 3, 13], -8⟩,
    ⟨true, [1], [4, 5, 3, 6, 8, 6, 5, 6, 5, 4, 1, 5, 2], -6⟩,
    ⟨true, [1], [11, 0, 11, 6, 6, 15, 6, 0, 11, 8, 9, 0, 13], -6⟩]

/-- R 坐标包络下端 = `3799838531198365386519224092526518708251264519719264915339 / 10^58`。 -/
def encLoNum : ℤ := 3799838531198365386519224092526518708251264519719264915339

def encLoDen : ℤ := 10000000000000000000000000000000000000000000000000000000000

/-- R 坐标包络上端 = `379983853119840840792600803019497105915164117416364409067 / 10^57`。 -/
def encHiNum : ℤ := 379983853119840840792600803019497105915164117416364409067

def encHiDen : ℤ := 1000000000000000000000000000000000000000000000000000000000

/-- 证书实例（数据全部来自源文件，未经修改）。 -/
def rootBoxCert : RootBoxCert where
  radiusHex := srcRadiusHex
  centerHex := srcCenterHex
  radius := decRadiusHex
  centers := decCenterHex
  loNum := encLoNum
  loDen := encLoDen
  hiNum := encHiNum
  hiDen := encHiDen
  radiusIndex := 6

/-- **具体数据通过内核检查**：`decide` = 内核求值这个 `Bool`，不是外部 exit 0。 -/
theorem rootBoxCert_check : rootBoxCert.check = true := by decide

/-- 由具体证书得到的实数不等式链末段。 -/
theorem rootBoxCert_encHi_lt_R0 : rootBoxCert.encHi < 19 / 50 :=
  (RootBoxCert.check_sound rootBoxCert_check).2.2.2

/-! ### 语义绑定与盒包含性的独立读数（每条都是内核定理） -/

/-- 索引 6 的解码结果，单独取名（向量索引可由 `rfl` 归约）。 -/
def decCenter6 : HexFloat := ⟨false, [1], [8, 5, 1, 10, 7, 12, 11, 8, 10, 1, 8, 15, 11], -2⟩

theorem decCenterHex_six : decCenterHex 6 = decCenter6 := rfl

/-- 盒半宽字面量的精确值。 -/
theorem decRadiusHex_toQ : decRadiusHex.toQ = (4835703278458517 : ℚ) / 2 ^ 82 := by
  simp only [decRadiusHex, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil,
    pow_succ, pow_zero, mul_one]
  norm_num

/-- R 坐标中心（索引 6）字面量的精确值。 -/
theorem decCenterHex_six_toQ : (decCenterHex 6).toQ = (6845180557269243 : ℚ) / 2 ^ 54 := by
  rw [decCenterHex_six]
  simp only [decCenter6, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil,
    pow_succ, pow_zero, mul_one]
  norm_num

/-- **源字面量的重新解码与生成器数据逐位相同**（12 个坐标 + 半径）。 -/
theorem src_parse_binding :
    HexFloat.parse srcRadiusHex = some decRadiusHex ∧
      ∀ i : Fin 12, HexFloat.parse (srcCenterHex i) = some (decCenterHex i) := by
  refine ⟨?_, ?_⟩
  · decide
  · intro i
    fin_cases i <;> decide

/-- **盒包含性**：包络落在「中心 ± 半宽」内（Krawczyk 包含 `K(X) ⊆ X` 的坐标形式）。 -/
theorem rootBoxCert_box_containment :
    (decCenterHex 6).toQ - decRadiusHex.toQ ≤ rootBoxCert.encLo ∧
      rootBoxCert.encHi ≤ (decCenterHex 6).toQ + decRadiusHex.toQ := by
  refine ⟨?_, ?_⟩
  · simp only [RootBoxCert.encLo, rootBoxCert, encLoNum, encLoDen, decCenterHex_six, decCenter6,
      decRadiusHex, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil, pow_succ, pow_zero,
      mul_one]
    norm_num
  · simp only [RootBoxCert.encHi, rootBoxCert, encHiNum, encHiDen, decCenterHex_six, decCenter6,
      decRadiusHex, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil, pow_succ, pow_zero,
      mul_one]
    norm_num

end N11Formalization


