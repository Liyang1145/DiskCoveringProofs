import N11Formalization.Precond
import N11Formalization.PrecondRight
import N11Formalization.OpNorm
import N11Formalization.KrawczykMatrix
import N11Formalization.Transport
import N11Formalization.Assembly.TCKrawczyk

/-!
# 球口径 ↔ 盒口径的接口桥：G1 的结论 ⇒ `Rstar` 的盒锁定

## 为什么需要本文件

本工程有两套「12 变量盒」的语言，此前**没有桥**：

* **G1 链**用球口径 `Metric.closedBall c ρ`（`E = Fin 12 → ℝ`，mathlib Pi 范数 = sup 范数）
  与 `Pi.single j 1` 作基；结论在 `Precond.TCSystem_unique_root_of_full_data`
  / `Assembly/TCKrawczyk.exists_unique_TCSystem_of_cert_box`（球内唯一根）。
* **其余部分**用 `C891RootSpec`（`Conditional/RootSpec.lean`）：`sys`、`boxLo/boxHi`、
  `exists_unique`、`radiusIndex = 6`，而 `Rstar S` 由 `Classical.choose` 取出。

本文件把两套语言接通并**钉住** `Rstar`：`Rstar S ∈ [boxLoCert 6, boxHiCert 6]`、
`Rstar S < 19/50`、`0 < Rstar S` —— 由 G1 的**球口径** `∃!` 结论与证书盒的精确有理数据推出。

## 数据来源与单位口径（先声明，后证明）

* `certificates/root-box.json::box.center_exact_rational`：12 个精确有理，本文件写成 `certC`
  （统一以 2 的幂为分母；`certC 6 = 6845180557269243/2^54`）。
  **注意 JSON 里另有 `c*2^82` 的写法**（如 index 6 的 `1837489164292903359479808`）——
  那是 `c·2^82`，不是 `c`；本文件用 `c` 本身（分母 2 的幂），逐坐标由
  `boxLo_boxHi_center_radius` 的算术核对。
* `box.halfwidth_exact_rational` = `4835703278458517/2^82` = `rhoCert`：
  既是**球的半径**，也是**盒的半宽**（`hi_i − lo_i = 2ρ`，逐坐标精确成立）。
* `box.lo_exact_rational` / `hi_exact_rational` = `boxLoCert` / `boxHiCert`（本文件的 `def`）。
* 无量纲。`Rstar` = 零基第 6 坐标（`radiusIndex = 6`），是 `TCSystem` 唯一零点的 `R` 分量。

## 已修正的一处转写 bug（值得留痕）

本文件初版的 `certC 8` 写成 `-7385064427961529 / 2^56`，而 JSON 该坐标是
`-7385064427961529 / 288230376151711744` = `-7385064427961529 / 2^58`（`center_hex = -0x1.a3cad4ddf3cb9p-6`）。
二者相差因子 4，会让第 8 坐标的 `boxLo/boxHi` 对应关系变成**假命题**——内核报错形状正是
「`⊢ False`」（`norm_num` 把两侧归一化后发现不相等）。
**教训**：盒的**全部 12 个坐标**都必须逐步核对，只核对 `index 6` 会漏掉这类错误；
而只要有一维盒角算错，`hbox`（`S.boxLo = boxLoCert`）就是假的，桥整体失效。
`evidence/box-rstar/verify_box_rstar.py` §2/§3 逐条独立复算 12 个坐标以封堵此风险。

## schema 审查（如实报告）

`C891RootSpec` 的字段**够用，无需增改**：

| 需要的结论 | schema 中承接的位置 |
|---|---|
| `sys = TCSystem`（钉住系统，防漂移） | 字段 `sys` + 本文件 `hspec` |
| 盒内 `∃!`（G1 的结论形状） | 字段 `exists_unique`（本文件由**球口径** `∃!` 经 `root_spec_certBox` 转成盒口径） |
| `Rstar = 第 6 坐标` | 字段 `radiusIndex`（值 `6`） |
| `boxLo/boxHi = 证书数据` | 字段 `boxLo`/`boxHi` + 本文件 `hbox` |
| 盒 → `Rstar` 的投影 | **已存在**（`C891RootSpec.root_mem` / `Rstar_mem_box`） |

唯一「缺」的是**桥本身**（此前无球↔盒接口定理），本文件补上；schema 无需改动。

## 前提口径（R10 之后的正确形状）

`hYinv`（**精确有理左逆** `Yinv·Y = I`）在源数据上**取不到**：源证书的预条件子是
`Y = np.linalg.inv(np.array(Jmid, dtype=float))`（`repair_tc_krawczyk.py:44`），是 binary64
**近似逆**。故本文件的主入口 `c891RootSpec_of_right_data` 用**另一侧**的收缩不等式——
`PrecondRight.injective_ratMatCLM_of_right_enclosure`（`‖I − J·Y‖ ≤ K' < 1`）——
它同样只需要**有限有理数据**（`krawczykMatR` 的逐元素包络 + 行和界），且乘法顺序是
`J·Y`（与 `hsum` 的 `Y·J` **相反**，不是同一个矩阵）。
左侧形态的入口 `c891RootSpec_of_krawczyk` 保留，供「确实持有精确左逆」的输入使用。

## 真实等级

本文件全部 kernel-proved（除显式前提），零 `sorry`、零自定义 `axiom`、零 `native_decide`。
数值部分（球↔盒对应、`boxHiCert 6 < 19/50`、`boxLoCert 6 > 0`、读数对读）**无条件**；
G1 的解析/数值前提**显式保留为定理参数**，不隐藏、不冒充已证。
-/

namespace N11Formalization

/-! ## 1. 证书盒的 Lean 数据（全部取 JSON 的精确有理数） -/

/-- 证书盒的**半宽 = 球半径** `ρ = 0x1.12e0be826d695p-30 = 4835703278458517/2^82`
（`certificates/root-box.json::box.halfwidth_exact_rational`）。 -/
def rhoCert : ℚ := 4835703278458517 / 2 ^ 82

/-- 证书盒**中心** `certC`：`certificates/root-box.json::box.center_exact_rational`（12 个精确有理，
统一写成 2 的幂为分母）。各坐标的指数由 `boxLo_boxHi_center_radius` 逐一核对。

**命名说明**：本文件用 `certC` / `certCR`（而不是 `cCert` / `cCertR`）以避开与
`ResidualInterval.lean`（fm-eval 的定义）在**共享根 import 图**里的同名冲突；
其余标识符（`rhoCert` / `boxLoCert` / `boxHiCert` / `RootSpecBall`）已核过全库唯一。 -/
def certC : Fin 12 → ℚ :=
  ![6701511529285631 / 2 ^ 54,
    6140082802885973 / 2 ^ 54,
    5058838003133637 / 2 ^ 54,
    6899731189335755 / 2 ^ 54,
    4917524862872097 / 2 ^ 54,
    -2691864528343895 / 2 ^ 54,
    6845180557269243 / 2 ^ 54,
    -2050658785296173 / 2 ^ 54,
    -7385064427961529 / 2 ^ 58,
    -7661580961047613 / 2 ^ 60,
    -2860603688525993 / 2 ^ 57,
    -7612361213708557 / 2 ^ 58]

/-- 证书盒下端 `boxLoCert`：**直接抄** `certificates/root-box.json::box.lo_exact_rational`
（统一写成 `2^82` 为分母；数值语义 `= certC i − ρ` 由 `boxLo_boxHi_center_radius` 证明）。 -/
def boxLoCert : Fin 12 → ℚ :=
  ![1798923298417342433274219 / 2 ^ 82,
    1648215922234750999800171 / 2 ^ 82,
    1357971481365603998574955 / 2 ^ 82,
    1852132483251062452070763 / 2 ^ 82,
    1320038024120705549412715 / 2 ^ 82,
    -722591886991921657599637 / 2 ^ 82,
    1837489159457200081021291 / 2 ^ 82,
    -550469530967087572768405 / 2 ^ 82,
    -123900825917530290181781 / 2 ^ 82,
    -32135004506949125854869 / 2 ^ 82,
    -95985936781297890809493 / 2 ^ 82,
    -127714233188113900295829 / 2 ^ 82]

/-- 证书盒上端 `boxHiCert`：**直接抄** `certificates/root-box.json::box.hi_exact_rational`。 -/
def boxHiCert : Fin 12 → ℚ :=
  ![1798923308088748990191253 / 2 ^ 82,
    1648215931906157556717205 / 2 ^ 82,
    1357971491037010555491989 / 2 ^ 82,
    1852132492922469008987797 / 2 ^ 82,
    1320038033792112106329749 / 2 ^ 82,
    -722591877320515100682603 / 2 ^ 82,
    1837489169128606637938325 / 2 ^ 82,
    -550469521295681015851371 / 2 ^ 82,
    -123900816246123733264747 / 2 ^ 82,
    -32134994835542568937835 / 2 ^ 82,
    -95985927109891333892459 / 2 ^ 82,
    -127714223516707343378795 / 2 ^ 82]

/-- 证书球的**球心**（有理中心 `certC` 提升到 `ℝ`）。 -/
def certCR : Fin 12 → ℝ := fun i => (certC i : ℝ)

/-- 证书球的**半径**（`rhoCert` 提升到 `ℝ`）。 -/
def rhoCertR : ℝ := (rhoCert : ℝ)

/-! ## 2. 单位口径：`ρ` 是球半径，盒半宽 = `ρ`（`ℚ` 级等式，**12 个坐标逐一**） -/

/-- **单位口径（核心对应关系）**：`boxLoCert i = certC i − ρ` 且 `boxHiCert i = certC i + ρ`，
**逐坐标精确**（`norm_num` 的真内核有理算术）。
这条把 JSON 的 `lo`/`hi` 数组与「球半径 `ρ`」的口径显式钉在一起：
**`ρ` 是球半径**，盒的半宽 `hi_i − lo_i = 2ρ`。

`fin_cases i <;> refine ⟨?_, ?_⟩` 之后每个分支的**单一目标**才能被 `norm_num` 闭合
（把 12 个坐标一次性塞给 `simp`/`norm_num` 会在数组元素内部乱转，实测不通）。 -/
theorem boxLo_boxHi_center_radius (i : Fin 12) :
    boxLoCert i = certC i - rhoCert ∧ boxHiCert i = certC i + rhoCert := by
  fin_cases i <;>
    refine ⟨?_, ?_⟩ <;> norm_num [boxLoCert, boxHiCert, certC, rhoCert]

/-- 盒的宽度逐坐标 `= 2ρ`。 -/
theorem boxHiCert_sub_boxLoCert (i : Fin 12) : boxHiCert i - boxLoCert i = 2 * rhoCert := by
  have h := boxLo_boxHi_center_radius i
  linarith [h.1, h.2]

/-- `ρ > 0`（半宽非退化）。 -/
theorem rhoCert_pos : 0 < rhoCert := by norm_num [rhoCert]

/-- 半径提升到 `ℝ` 仍为正。 -/
theorem rhoCertR_pos : 0 < rhoCertR := by
  dsimp only [rhoCertR]; exact_mod_cast rhoCert_pos

/-! ## 3. 读数与本工程已知常数的对照（内核可判定的精确有理等式） -/

/-- **`certC 6`（`Rstar` 所在坐标的中心）的精确值** = JSON `center_exact_rational[6]`。 -/
theorem certC_six_eq : certC 6 = 6845180557269243 / 2 ^ 54 := rfl

/-- **`boxHiCert 6` 的精确值**（= JSON `hi_exact_rational[6]`，分子逐位相同）。 -/
theorem boxHiCert_six_eq : boxHiCert 6 = 1837489169128606637938325 / 2 ^ 82 := rfl

/-- **`boxLoCert 6` 的精确值**（= JSON `lo_exact_rational[6]`）。 -/
theorem boxLoCert_six_eq : boxLoCert 6 = 1837489159457200081021291 / 2 ^ 82 := rfl

/-- **第 8 坐标的修正后读数**（转写 bug 的定点读数）：`certC 8 = -7385064427961529/2^58`，
且**不是** `-7385064427961529/2^56`（后者是错值，差值 = `3·(7385064427961529/2^58) ≠ 0`）。

对齐方式与 `boxLo/boxHiCert`（分母 `2^82`）一致。 -/
theorem certC_eight_eq : certC 8 = -7385064427961529 / 2 ^ 58 := rfl

/-- **`tcRootSpec` 的半径坐标恒为 6**（下游拿到 `C891RootSpec` 后一律不需再证）。 -/
theorem tcRootSpec_radiusIndex (boxLo boxHi : Fin 12 → ℚ)
    (h : ∃! z : Fin 12 → ℝ,
      (∀ i : Fin 12, (boxLo i : ℝ) ≤ z i ∧ z i ≤ (boxHi i : ℝ)) ∧ TCSystem z = 0) :
    (tcRootSpec boxLo boxHi h).radiusIndex = 6 :=
  rfl

/-- **第 8 坐标的正确/错误值区分**（bug 的回归读数，方向已实测纠正）：

`-7385064427961529 < 0`，故把该坐标误写成 `n/2^56` 会得到一个**更小**（更负）的值：
`n/2^56 = 4·(n/2^58) < n/2^58`（`n < 0`），差额恰好 `3·|n|/2^58` 的量级。
这正是 `norm_num` 判定「盒角对应关系为假」的量化原因——
错值的 `boxLoCert 8` 会**偏小** `3·(7385064427961529/2^82)`（用 `2^82` 公共分母看），
于是「`boxLoCert 8 = certC 8 − ρ`」这条等式在错值下**不成立**。 -/
theorem certC_eight_transcription_gap :
    (-7385064427961529 : ℚ) / 2 ^ 56 < (-7385064427961529 : ℚ) / 2 ^ 58 ∧
      (-7385064427961529 : ℚ) / 2 ^ 58 - (-7385064427961529 : ℚ) / 2 ^ 56
        = 3 * (7385064427961529 / 2 ^ 58) :=
  ⟨by norm_num, by norm_num⟩

/-- `2` 的幂次的十进制形式（供外部对读，内核可判定）。 -/
theorem pow_two_readings :
    (2 : ℚ) ^ 54 = 18014398509481984 ∧ (2 : ℚ) ^ 82 = 4835703278458516698824704 :=
  ⟨by norm_num, by norm_num⟩

/-- **索引 6 的 ℝ 读数行显式 cast 形式（上界）**：把 `↑(n/2^82)` 化成 `↑n / 2^82`，
使下游的 ℝ 不等式链不再受 `↑` 归约差异影响。
（两侧都写成显式 `ℚ` 子项，避免 `2^82` 被推成 `ℕ` 幂。） -/
theorem boxHiCert_six_real_eq :
    (((1837489169128606637938325 : ℚ) / ((2 : ℚ) ^ 82) : ℚ) : ℝ)
      = ((1837489169128606637938325 : ℚ) : ℝ) / (((2 : ℚ) : ℝ)) ^ 82 := by
  exact_mod_cast (by ring : (1837489169128606637938325 : ℚ) / (2 : ℚ) ^ 82
    = 1837489169128606637938325 / (2 : ℚ) ^ 82)

/-- 索引 6 的 ℝ 读数行显式 cast 形式（下界）。 -/
theorem boxLoCert_six_real_eq :
    (((1837489159457200081021291 : ℚ) / ((2 : ℚ) ^ 82) : ℚ) : ℝ)
      = ((1837489159457200081021291 : ℚ) : ℝ) / (((2 : ℚ) : ℝ)) ^ 82 := by
  exact_mod_cast (by ring : (1837489159457200081021291 : ℚ) / (2 : ℚ) ^ 82
    = 1837489159457200081021291 / (2 : ℚ) ^ 82)

/-- 十进制对读：`certC 6`、`boxLoCert 6`、`boxHiCert 6`、`ρ` 的十进制开头与
`certificates/root-box.json` 的 `decimal` 字段一致（独立复算见
`evidence/box-rstar/verify_box_rstar.py` §3b：44/45/53 位十进制**四舍五入**逐位相同）。 -/
theorem box_rstar_readings :
    (6845180557269243 / 2 ^ 54 : ℚ) < 379983854 / 10 ^ 9 ∧
    (1837489159457200081021291 / 2 ^ 82 : ℚ) < 379983853 / 10 ^ 9 ∧
    (379983852 / 10 ^ 9 : ℚ) < 1837489159457200081021291 / 2 ^ 82 ∧
    (1837489169128606637938325 / 2 ^ 82 : ℚ) < 379983855 / 10 ^ 9 ∧
    (379983854 / 10 ^ 9 : ℚ) < 1837489169128606637938325 / 2 ^ 82 ∧
    (4835703278458517 / 2 ^ 82 : ℚ) < 1000000001 / 10 ^ 18 ∧
    (1000000000 / 10 ^ 18 : ℚ) < 4835703278458517 / 2 ^ 82 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## 4. 核心桥：`C891RootSpec` 的 `exists_unique` 字段（盒口径） -/

/-- **G1 的球口径结论形状**（命名化，避免每条定理都重复 12 个参数）：
在证书球 `closedBall certCR rhoCertR` 上 `TCSystem` 有唯一零点。 -/
def RootSpecBall : Prop :=
  ∃! x : Fin 12 → ℝ, x ∈ Metric.closedBall certCR rhoCertR ∧ TCSystem x = 0

/-- **盒/球成员等价（`boxLoCert`/`boxHiCert` 实例）**：逐坐标谓词与证书闭球相同。

这是「球口径 ↔ 盒口径」的**定义层桥**：两侧是**同一个命题**，只是把 `certC ± ρ`
与 `boxLoCert`/`boxHiCert` 两种写法互换（由 `boxLo_boxHi_center_radius` 的 `ℚ` 级等式），
再套用 `Assembly/TCKrawczyk.lean` 的 `mem_closedBall_iff_box`。 -/
theorem mem_closedBall_cert_iff {x : Fin 12 → ℝ} :
    x ∈ Metric.closedBall certCR rhoCertR
      ↔ (∀ i : Fin 12, (boxLoCert i : ℝ) ≤ x i ∧ x i ≤ (boxHiCert i : ℝ)) := by
  rw [mem_closedBall_iff_box (c := certCR) (ρ := rhoCertR) rhoCertR_pos.le]
  refine forall_congr' fun i => ?_
  have hl : ((boxLoCert i : ℚ) : ℝ) = certCR i - rhoCertR := by
    dsimp only [certCR, rhoCertR]; exact_mod_cast (boxLo_boxHi_center_radius i).1
  have hh : ((boxHiCert i : ℚ) : ℝ) = certCR i + rhoCertR := by
    dsimp only [certCR, rhoCertR]; exact_mod_cast (boxLo_boxHi_center_radius i).2
  rw [hl, hh]

/-- 证书球的**球心落在球内**（供右侧收缩取点用；由盒上界承载的包含性读数）。 -/
theorem certCR_mem_ball : certCR ∈ Metric.closedBall certCR rhoCertR := by
  rw [Metric.mem_closedBall, dist_self]
  exact rhoCertR_pos.le

/-- **核心桥（G1 的球口径 `∃!` ⇔ `C891RootSpec.exists_unique` 的盒口径 `∃!`）**。

由 `Precond.TCSystem_unique_root_of_full_data`（或任何球口径的 G1 结论）产出的
`∃! x, x ∈ closedBall certCR rhoCertR ∧ TCSystem x = 0`，与 `C891RootSpec` 需要的
`∃! z, (∀ i, boxLo i ≤ z i ≤ boxHi i) ∧ sys z = 0`（`sys = TCSystem`、
`boxLo/boxHi = boxLoCert/boxHiCert`）**完全等价**——两者的约束谓词就是同一个命题。 -/
theorem root_spec_certBox (h : RootSpecBall) :
    ∃! z : Fin 12 → ℝ,
      (∀ i : Fin 12, (boxLoCert i : ℝ) ≤ z i ∧ z i ≤ (boxHiCert i : ℝ)) ∧ TCSystem z = 0 := by
  obtain ⟨x, hxball, hxuniq⟩ := h
  exact ⟨x, ⟨mem_closedBall_cert_iff.mp hxball.1, hxball.2⟩,
    fun w hw => hxuniq w ⟨mem_closedBall_cert_iff.mpr hw.1, hw.2⟩⟩

/-! ## 5. `Rstar` 的盒锁定 -/

/-- **第 6 坐标的锁定**（盒口径直接读数，不需要 `radiusIndex`）：由 `S.root ∈ box`
与坐标投影得到。 -/
theorem root_six_mem_cert_box {S : C891RootSpec} (_hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) :
    (boxLoCert 6 : ℝ) ≤ S.root 6 ∧ S.root 6 ≤ (boxHiCert 6 : ℝ) := by
  have h := (S.root_mem).1 6
  rwa [hbox.1, hbox.2] at h

/-- **`Rstar` 的盒锁定（核心交付）**：`Rstar S ∈ [boxLoCert 6, boxHiCert 6]`。

`S.root ∈ box`（字段 `exists_unique` 的内容）与第 6 坐标投影。
真实等级：kernel-proved，无条件（除 `S` 的显式前提 `exists_unique` 与 `hspec`/`hbox`/`hidx`）。 -/
theorem Rstar_mem_of_krawczyk {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    (boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ) := by
  have h := root_six_mem_cert_box hspec hbox
  dsimp only [Rstar]
  rw [hidx]; exact h

/-! ### 7.1 索引 6 的 ℝ 读数行（cast 归一的两种口径）

`boxHiCert 6` 是 `ℚ`，下游的 ℝ 不等式里 `↑(n / 2^82)` 与 `↑n / (↑2)^82` 在语法上不同、
在定义上相同。这里把**两种口径都给全**，避免下游被迫做 `↑` 归约。 -/

/-- 上界，**未拆 cast** 的口径（与 `Rstar_mem_of_krawczyk` 的输出逐字一致）。 -/
theorem Rstar_le_boxHiCert_six_cast {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    Rstar S ≤ (((1837489169128606637938325 : ℚ) / 2 ^ 82 : ℚ) : ℝ) :=
  (Rstar_mem_of_krawczyk hspec hbox hidx).2

/-- 上界，**已拆 cast** 的口径（`↑n / 2^82`）。 -/
theorem Rstar_le_boxHiCert_six {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    Rstar S ≤ (1837489169128606637938325 : ℝ) / 2 ^ 82 := by
  have h := Rstar_le_boxHiCert_six_cast hspec hbox hidx
  rw [boxHiCert_six_real_eq] at h
  simpa using h

/-- 下界，**未拆 cast** 的口径。 -/
theorem boxLoCert_six_le_Rstar_cast {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    (((1837489159457200081021291 : ℚ) / 2 ^ 82 : ℚ) : ℝ) ≤ Rstar S :=
  (Rstar_mem_of_krawczyk hspec hbox hidx).1

/-- 下界，**已拆 cast** 的口径（`↑n / 2^82`）；配合 `boxLoCert_six_pos` 给出 `0 < Rstar S`。 -/
theorem boxLoCert_six_le_Rstar {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    (1837489159457200081021291 : ℝ) / 2 ^ 82 ≤ Rstar S := by
  have h := boxLoCert_six_le_Rstar_cast hspec hbox hidx
  rw [boxLoCert_six_real_eq] at h
  simpa using h

/-! ## 6. 把 G1 结论喂进 schema：由球口径 `∃!` 造出 `C891RootSpec` -/

/-- **任意球口径 G1 结论 ⇒ 证书盒实例的 `C891RootSpec`**（盒/系统/半径坐标三条等式同时给出）。

这是「喂进 schema」的**通用入口**：只要拿到任一条球口径 G1 结论
（`Assembly/G1Final.TCSystem_unique_root_of_final_data`、
`Assembly/G1Interval.TCSystem_unique_root_of_interval_data`、
`Assembly/TCKrawczyk.exists_unique_TCSystem_of_cert_box` 都可用），
即可得到 `sys = TCSystem ∧ boxLo = boxLoCert ∧ boxHi = boxHiCert` 的 `C891RootSpec`。 -/
theorem c891RootSpec_of_ball (h : RootSpecBall) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert :=
  ⟨tcRootSpec boxLoCert boxHiCert (root_spec_certBox h), rfl, rfl, rfl⟩

/-- **带半径坐标的加强版**：与 `c891RootSpec_of_ball` 同一个见证，但**同时给出**
`radiusIndex = 6`。下游从 `∃` 里解构出 `S` 后不再需要重新证半径坐标。 -/
theorem c891RootSpec_of_ball_with_idx (h : RootSpecBall) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 :=
  ⟨tcRootSpec boxLoCert boxHiCert (root_spec_certBox h), rfl, rfl, rfl, rfl⟩

/-- **`Precond.TCSystem_unique_root_of_full_data` ⇒ `C891RootSpec`（左侧收缩/有理左逆形态，
半径固定为证书半径 `rhoCertR`）**。

前提：有理预条件子 + **左逆** `Yinv·Y = I` + Jacobian 区间包络 + `I − Y·J` 行和界 +
残差包络 + 七个非退化条件 + `η + K·rhoCertR < rhoCertR`。
**注意**：`hYinv`（精确有理左逆）在源数据上**取不到**（源 `Y` 是 binary64 近似逆）；
若只有源数据，请改用 `c891RootSpec_of_right_data`（R10 的右侧收缩路线）。 -/
theorem c891RootSpec_of_krawczyk {K η : ℝ}
    (Y Yinv : Fin 12 → Fin 12 → ℚ)
    (hYinv : ∀ i j : Fin 12, ∑ k : Fin 12, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0))
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η)
    (hndRho : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ Metric.closedBall certCR rhoCertR, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert :=
  c891RootSpec_of_ball
    (by
      have h := TCSystem_unique_root_of_full_data (ρ := rhoCertR) Y Yinv hYinv rhoCertR_pos
        hK0 hK1 hη0 hndRho hndW hndU1 hndU2 hndU3 hndU8 hndWp Jt hJ hsum Fm hFm hηb hres
      simpa only [RootSpecBall] using h)

/-- **R10 的正确入口：右侧收缩 ⇒ `C891RootSpec`**（前提全部是有限有理数据）。

* 单射性：`PrecondRight.injective_ratMatCLM_of_right_enclosure` —— `‖I − J·Y‖ ≤ K' < 1`
  （`I − J·Y` 的逐元素有理包络 `krawczykMatR` + 行和界 `hsumR`）。
  **乘法顺序是 `J·Y`**，与 `hsum` 的 `Y·J` 是**两个不同的矩阵**。
  `I − J·Y` 的包络只需在球内**一点**（取球心 `certCR`，含在球内）成立即可给出单射性
  （单射是矩阵 `Y` 的性质，与取点无关），故 `hJR` 只要求球心一处。
* 唯一根：`krawczyk_unique_root_of_entry_bounds`（`Assembly/G1.lean`）+ `opNorm` 一侧的
  逐元素包络 `hJ`/`hsum`（`I − Y·J`，行和 ≤ `K < 1`）+ 残差界 `hres`。
* 可微性由 `Transport.differentiableAt_TCSystem_of_conditions` 从七个非退化条件自动给出
  （G1 义务 (2) 已付清，见 `STATUS` M24/M23）。 -/
theorem c891RootSpec_of_right_data {K η K' : ℝ}
    (Y : Fin 12 → Fin 12 → ℚ)
    (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η) (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
    (hndRho : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ Metric.closedBall certCR rhoCertR, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ Metric.closedBall certCR rhoCertR, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ Metric.closedBall certCR rhoCertR, wPoint x ≠ ringCenter x 6)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (hsumR : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR Jt Y i j).lo : ℝ)| |((krawczykMatR Jt Y i j).hi : ℝ)| ≤ K')
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem certCR k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * rhoCertR < rhoCertR) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 := by
  -- (1) 单射性：右侧收缩（`I − J·Y`），只需球心一点
  have hYinj : Function.Injective (ratMatCLM Y) :=
    injective_ratMatCLM_of_right_enclosure Y (fderiv ℝ TCSystem certCR) hK'0 hK'1 Jt
      (fun k j => hJ certCR certCR_mem_ball k j) hsumR
  -- (2) 残差界：`‖Y (F c)‖ ≤ η`
  have hres' : dist certCR (certCR - ratMatCLM Y (TCSystem certCR)) + K * rhoCertR < rhoCertR := by
    rw [dist_sub_eq_norm]
    have h1 := norm_ratMatCLM_le (Y := Y) (Fm := Fm) (v := TCSystem certCR) hFm hη0 hηb
    linarith
  refine c891RootSpec_of_ball_with_idx ?_
  dsimp only [RootSpecBall, certCR, rhoCertR]
  exact krawczyk_unique_root_of_entry_bounds TCSystem (ratMatCLM Y) hYinj certCR rhoCertR K
    rhoCertR_pos hK0 hK1
    (fun x hx => differentiableAt_TCSystem_of_conditions x (hndRho x hx) (hndW x hx)
      (hndU1 x hx) (hndU2 x hx) (hndU3 x hx) (hndU8 x hx) (hndWp x hx))
    (fun i j => ((krawczykMat Y Jt i j).lo : ℝ))
    (fun i j => ((krawczykMat Y Jt i j).hi : ℝ))
    (fun x hx i j => ⟨RatInterval.mem_lo_le
        (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := Jt)
          (fun k j => hJ x hx k j) i j),
      RatInterval.mem_le_hi (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := Jt)
        (fun k j => hJ x hx k j) i j)⟩) hsum hres'

/-! ## 7. 推论（下游真正要用的）：`Rstar < 19/50` 与 `Rstar` 的下界 -/

/-- **盒上端 `< 19/50`**（C922 阈值）：**数据决定的事实，成立**。
余量 `19/50 − boxHiCert 6 = 1951917140742690376563/120892581961462917470617600 > 0`
（十进制 `≈ 1.6145880e-5`）。若该不等式不成立则本工程整条 `Rstar < R0` 路线失效——
实测成立，故如实登记为 proved。 -/
theorem boxHiCert_six_lt_R0 : boxHiCert 6 < 19 / 50 := by
  rw [boxHiCert_six_eq]; norm_num

/-- 盒上端 `< 19/50` 的**交叉相乘整数形式**（整数判据，见证精确有理不等式）。 -/
theorem boxHiCert_six_lt_R0_cross :
    50 * 1837489169128606637938325 < 19 * (2 ^ 82 : ℤ) := by norm_num

/-- 盒上端 `< 19/50` 的 **ℝ 版本**（下游与 `Rstar` 的 ℝ 不等式链直接对接的读数）。 -/
theorem boxHiCert_six_lt_R0_real : (boxHiCert 6 : ℝ) < 19 / 50 := by
  have h : (boxHiCert 6 : ℝ) < (((19 : ℚ) / 50 : ℚ) : ℝ) := by
    exact_mod_cast boxHiCert_six_lt_R0
  norm_num at h
  exact h

/-- **盒下端 `> 0`**（`Rstar` 的**下界**读数；与上界一样是数据决定的事实）。 -/
theorem boxLoCert_six_pos : (0 : ℚ) < boxLoCert 6 := by
  rw [boxLoCert_six_eq]; norm_num

/-- **主推论（上界）**：`Rstar S < 19/50` —— 用盒上端的**精确有理不等式** `boxHiCert 6 < 19/50`
与 `Rstar ≤ boxHiCert 6` 得到。这是 C922 口径下下游真正要用的读数。 -/
theorem Rstar_lt_R0_of_krawczyk {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    Rstar S < 19 / 50 :=
  lt_of_le_of_lt (Rstar_mem_of_krawczyk hspec hbox hidx).2 boxHiCert_six_lt_R0_real

/-- **主推论（下界，条件形式）**：`0 < Rstar S`。与上界同理，由盒下端的精确有理不等式
`0 < boxLoCert 6` 与 `boxLoCert 6 ≤ Rstar S` 得到；这条正是「半径为正」的下界读数。 -/
theorem Rstar_pos_of_krawczyk {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    0 < Rstar S :=
  lt_of_lt_of_le (by exact_mod_cast boxLoCert_six_pos : (0 : ℝ) < (boxLoCert 6 : ℝ))
    (Rstar_mem_of_krawczyk hspec hbox hidx).1

/-- **合起来的读数（一条定理拿走全部下游读数）**：盒锁定两端 + `Rstar < 19/50` + `0 < Rstar`。 -/
theorem Rstar_readings_of_krawczyk {S : C891RootSpec} (hspec : S.sys = TCSystem)
    (hbox : S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    (boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ) ∧ Rstar S < 19 / 50 ∧
      0 < Rstar S :=
  ⟨(Rstar_mem_of_krawczyk hspec hbox hidx).1, (Rstar_mem_of_krawczyk hspec hbox hidx).2,
    Rstar_lt_R0_of_krawczyk hspec hbox hidx, Rstar_pos_of_krawczyk hspec hbox hidx⟩

/-- **任意球口径 G1 结论直接给出 `Rstar < 19/50`**（下游不必自己处理 cast 口径）。
把 `c891RootSpec_of_ball_with_idx` 与 `Rstar_lt_R0_of_krawczyk` 拼成一步读数，
即「G1 结论 ⇒ C922 阈值」的最直接形态。 -/
theorem Rstar_lt_R0_of_ball (h : RootSpecBall) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ Rstar S < 19 / 50 := by
  obtain ⟨S, h1, h2, h3, hidx⟩ := c891RootSpec_of_ball_with_idx h
  exact ⟨S, h1, h2, h3, Rstar_lt_R0_of_krawczyk h1 ⟨h2, h3⟩ hidx⟩

/-- **端到端（球口径 G1 结论 ⇒ `C891RootSpec` + `Rstar < 19/50` + `0 < Rstar`）**：
把 §6 与 §7 串起来，任意球口径 G1 结论直接产出下游要用的全部读数。

半径坐标由 `c891RootSpec_of_ball` 的**构造式**给出（`tcRootSpec` 恒取 `radiusIndex = 6`），
故 `Rstar` 就是第 6 坐标；`∃` 解构只给出 `sys/boxLo/boxHi` 三条等式，半径坐标另由
`tcRootSpec_radiusIndex` 取。 -/
theorem Rstar_readings_of_ball (h : RootSpecBall) :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      Rstar S < 19 / 50 ∧ 0 < Rstar S := by
  obtain ⟨S, h1, h2, h3, hidx⟩ := c891RootSpec_of_ball_with_idx h
  exact ⟨S, h1, h2, h3, Rstar_lt_R0_of_krawczyk h1 ⟨h2, h3⟩ hidx,
    Rstar_pos_of_krawczyk h1 ⟨h2, h3⟩ hidx⟩

end N11Formalization
