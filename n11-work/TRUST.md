# TRUST —— 可信基础与依赖审计（GUIDE §6）

## 1. 内核与库

| 项 | 值 | 来源 |
|---|---|---|
| Lean | `4.33.1`，commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`，x86_64-w64-windows-gnu | `lean --version`（实测） |
| Lake | `5.0.0-src+819816b` | `lake --version`（实测） |
| mathlib | rev `0df444a360eaa60ab8c11dca51a86af692955474`（configFile `lakefile.lean`，toolchain `v4.33.1`） | `lake-manifest.json`、`git rev-parse HEAD`（实测） |
| 依赖包 | batteries `4488d40d…`、aesop `3448c0bc…`、Qq `92c15be1…`、proofwidgets `4be2e3d5…`、importGraph `16f02aa7…`、Cli `6130a478…`、plausible `b7eb3304…`、LeanSearchClient `5f4d51b8…` | 同上 |
| 工程 | `research-2026/n11-formalization/lean/`（`packagesDir = .lake/packages`，junction → `E:\n11-formalization-deps\packages`） | `manifests/toolchain.json` |

**隔离说明**：依赖是 `E:\lean-lab\projects\research\.lake\packages` 的**独立副本**（robocopy，
7.04 GB），不与该旧工程共写构建目录。首次 `lake build` 复用已编译 oleans，无任何下载。

## 2. 逻辑基础（`#print axioms` 实测）

主条目传递依赖仅为 `propext`、`Classical.choice`、`Quot.sound`（mathlib 惯例可接受）。
`rootBoxCert_check`（具体证书通过）仅依赖 `[propext]` —— 是**纯内核求值**。

**没有**出现：`sorryAx`、自定义 `axiom`、`Lean.ofReduceBool`、`native_decide` 桥、
`Classical.choice` 之外的不可计算公理。完整清单见 `evidence/lead/PRINT-AXIOMS.txt`。

### 2.1 关于 `Rstar` 用 `Classical.choice` 的一点说明

`Rstar S := (Classical.choose S.exists_unique) S.radiusIndex`。
`S.exists_unique` 是**结构字段（假设）**，不是公理；因此 `#print axioms` 不会出现自定义公理，
但这**不等于**"根存在性已证"。它依然是 `Conditional/RootSpec.lean` 的显式前提，
其证明义务归属于 C891，见 §3。

## 3. 未形式化的承重义务（当前阻断项，按**锐化口径**重列）

主命题 = 两条标量不等式（`n11MainStatement_iff_two_bounds`）：
`sInf feasibleRadii ≤ Rstar` ∧ `Rstar ≤ sInf feasibleRadii`。故阻断项为：

| # | 义务 | 对应源结论 | Lean 中的位置 |
|---|---|---|---|
| 0 | **语义桥**：`sys`（`res5` 表达式树）= 源文 §2 几何定义 | C891 前置 | 未定义（**最高风险**，见 §5.1） |
| 1 | 12 变量 TC/KKT 系统在给定二进有理盒内**存在唯一根** | C891 | `C891RootSpec.exists_unique` |
| 2 | 根落在包络/盒内（Krawczyk 包含） | C891 | `Rstar_lt_R0_via_cert` 的 `hlo`/`hhi` |
| 3 | 在 `Rstar` 处的覆盖构型 ⇒ `sInf ≤ Rstar` | C892 | `n11_main_conditional` 的 `hattain` |
| 4 | `Rstar ≤ sInf`（C923 归约 + C921 全域下界 + C922 同根阈值） | C923/C921/C922 | `n11_main_conditional` 的 `hbound` |

**已无条件付清**（不建议再列为义务）：`sInf` 的非空/下有界/闭/达到性；
"存在**某个**最优构型"；`Rstar` 的盒上端 `< 19/50`。

**因此当前最终验收未达成**：`n11_main_conditional` / `n11_main_of_cert_box` 是条件结论，
不是 `N11MainStatement (Rstar …)` 的无条件内核证明。

### 3.1 反漂移控制件（由 stmt-audit 独立证明）

- `n11MainStatement_at_sInf_is_free`：`N11MainStatement (sInf feasibleRadii)` **无条件为真且不含源常数**
  ⇒ 禁止把「`r_D(11) = sInf`」形式当源定理。
- `Audit/CertBoxPinning.certBox_does_not_identify_Rstar`：同盒同索引的两个合法实例 `Rstar` 相差 `≈2e-9`
  ⇒ `C891RootSpec` 是 schema，`Rstar` 数值身份未定，必须由义务 #0/#1 钉住。
- `Audit/InterfaceSharpening.exists_instance_with_Rstar_ne_sInf`：`Rstar S = sInf` 非自动。

### 3.2 区间内核侧的口径订正与判定（interval-core）

- **判定**：`exp` / `log` / `atan2` **不需要**。理由：`residual` 及其依赖
  `rhoK/ringCenter/arcEnd/Uvec/wPoint/hub0/hub1` 只用 `Real.sin`、`Real.cos`、`Real.sqrt`、`Real.pi`
  与四则运算与 `dist`（= `sqrt`），后 7 块的 Jacobian 用 `fderiv`（区间化同样只需 sin/cos/sqrt），
  故三者不在 `K(B) ⊆ B` 的依赖闭包内。精确待办仍留在 `evidence/interval/INTERVAL-GAPS.md` §1/§2/§4 备用。
- **口径订正**：claim **C984** 正文把公理三元组误敲成 `[propext, Classical.choice, Classical.choice, Quot.sound]`
  （重复一个名字）。**以 `evidence/interval/PRINT-AXIOMS.txt` 为准**（145 条全为
  `[propext, Classical.choice, Quot.sound]`），正文的三元组不改变任何证明内容。
- **实现限制**：对 `sinI_mem` 的**具体点实例化**在 Lean 4.33.1 下 `isDefEq` 心跳耗尽（800k 仍超时），
  已记入 `Trig.lean` 注释与报告；该项不作为交付读数，其内容由 `read_sinI_interval`/`_fallback` 等覆盖。
- **R4（`Range.lean`）**：`inWindow A k` 是**逐 k 的有理不等式谓词**，**不是**可判定的有限搜索；
  回退区已量化（`windowFallback_of_width_gt_two`：盒宽 > 2 ⇒ 一律回退 `intv (−1) 1`）。
  `inWindow` 的**有限候选集显式界**仍缺（现只有宽度侧 `hi − lo ≤ 2`），列为未决义务。
  另：`reducedBox_mem` 实际**不需要** `inWindow` 前提（比要求更强的读数，已在文件注明）。
- **台账事故（自曝并更正，保留留痕）**：interval-core 第一条独立复核事件**误挂在 C981**
  （id 打错；C981 属他人的网络证书族 claim，与本事无关）。同一内容已正确落在 **C989**，
  并在其 note 写明更正。**C981 上那条事件应视为悬挂事故，不计对该 claim 的复核**；
  append-only 事件无法删除，故在此登记口径。
- **口径提示**：`Interval/Phase.lean` 里 interval-core 关于 `k : ℤ` 封装"未交付"的记录
  已被 Lead 的 `IntervalZ.lean` 补齐（根因与解法见该文件头），不影响其数学内容。

## 4. 外部数据的可信边界（GUIDE §5）

| 数据 | 来源（sha256） | 可信路径 | 残余风险 |
|---|---|---|---|
| 12 个中心 + 半径的十六进制字面量 | `repaired_tc_krawczyk.json` 的 `certificate`（`0154400192cf677e22d8f06b14dda67a4fe1c53500f3f8551c492c69b07ffdc5`） | 字面量 --parse--> 数字表 --toQ--> 精确有理数，全部内核检查；`src_parse_binding` 逐位绑定 | 无（对"这些字面量的值"而言） |
| R 坐标包络端点 | 同件 `radius_coordinate_enclosure`（精确十进制，转入 `ℤ` 分子/分母） | 交叉相乘判据 + `div_le_div_iff₀`/`div_lt_iff₀` | **该包络本身是 Krawczyk 计算的外部输出**；"确为 R* 的包络"由义务 #2 承担 |
| `max_K_shift` / `contraction_inf` | 同件 | 仅作为读数引用 | 未形式化，也未用作前提 |
| C922 的 4.8531e-31 区间 | `exact_root_threshold.json`（`2a06ce96f5fa2490f4526cfce9e2151bb3f272aaed77a8c2d5bf6fe4c645415d`） | **root-audit 已用精确有理外向舍入 + 自建超越函数引理表独立重认证**（见 §5.2） | 见 §5.1、§5.2 |

**未** 使用：宿主 math 库浮点结果作为实数公理；哈希代替语义绑定；`#eval`/Python PASS 作为证明。

## 5. 根证书链的独立审计结论（root-audit，2026-09-26）

证据：`evidence/root/ROOT-CERT-AUDIT.md`、`certificates/root-box.json`、`certificates/ROOT-SPEC.md`、
`evidence/root/{provenance,audit_replay,domain_cert}.json`、`evidence/root/rativ.py`。

### 5.1 最高风险：**语义桥**（必须先于区间工作）

被认证的盒心依赖一个 12 变量残差向量，其第 5 行 `res5` 的**表达式树**必须等于
源文 §2 的几何定义。目前只做到**数值一致**（root-audit 从 md 文字独立重写 `res5`，
12/12 落在旧 `F_center` 的 `1e-56` 级包络内，最大越界 0）。

风险已被放大证实：把 `π` 换成 binary64 使 `F` 偏 `4.7e-15`，而 **Krawczyk 包含照样通过**。
⇒ **包含判据检测不到 1e-16 量级的"函数搞错了"**。形式化侧必须先做语义桥
（把 `res5` 的表达式树与其几何定义在同一 Lean 定义下证等），**再**做区间/Krawczyk。

### 5.2 可用结论（把 Lean 义务从 6 步压到 2 步）

- 6 步收缩**不能**化成纯有理（盒上 Jacobian 必须包含 `sin/cos/sqrt/π` 值域），
  但可化成「精确有理外向舍入 + 有限可枚举的超越函数引理表」；root-audit 已实现该表
  （Machin π 宽 `2^-260`、象限归约 + 中心化中值 `sin/cos`、整数 `isqrt` 的 `sqrt`），
  **链内无浮点区间库**，并复现记录值：C891 单步宽 `4.302141e-15`；6 步终点宽 `4.853078e-31`；
  每步 `max_width` 与记录逐项吻合；与记录端点差 `~1e-40`（其区间含于记录区间内）。
- `R* < 19/50` 只需第 1 步（裕度 `1.61468801591592074e-5`）；
  **`R* < T` 只需第 2 步**（裕度 `1.9326256593863664131773e-17`）⇒ 第 3–6 步对 n=11 定理**不必要**。
- 不需要 Brouwer：`Q < 1` 且 `g = id − Y·F₁₂` 映盒入盒 ⇒ **Banach** 直接给存在唯一。
- **建议的第一个内核可查目标**：`K(B) ⊆ B` 且 `Q ≤ 0.0043719716348663187201 < 1`（第 1 步，纯有理不等式）
  ＋第 2 步收缩得 `Rstar < T`。数据与精确端点全在 `certificates/root-box.json`。
- 精度口径：本次 S4/S5/domain_cert 就算术而言是 `proved-exact`（精确有理 + 外向舍入），
  但仍**条件依赖 6 条已声明的分析前提**（MVT、交错级数余项、`|sin|≤1`、Machin π、`isqrt` 界），
  **不覆盖语义前提**。`root-box.json` 的 `declared_premises`/`proved`/`not_proved` 三项分开列全。
- 另发现第三条独立引擎 `r20_tc_iv3`（SymPy 严格树走 + 自有 `Y` + 精确有理断言）：
  确认存在唯一，`Q=0.00433242`，但**不产出窄 R 坐标**，故不是 4.85e-31 的第二来源。
- `analytic-11` 的 1500 位读数 = `numeric`（无方向舍入，不构成证明），其值落在该区间内。

## 6. 复现

```powershell
cd research-2026/n11-formalization
.\verify.ps1                                  # 全工程，期望 exit 0（8721 jobs）
.\verify.ps1 -File lean\PrintAxioms.lean      # #print axioms（67 行，0 error/0 sorryAx/0 nativeDecide）
# 根证书链（独立复现，cwd = 工作区根，约 13.6 s）：
py -3 -X utf8 -B research-2026/n11-formalization/evidence/root/rativ.py
py -3 -X utf8 -B research-2026/n11-formalization/evidence/root/run_audit.py
py -3 -X utf8 -B research-2026/n11-formalization/evidence/root/domain_cert.py
py -3 -X utf8 -B research-2026/n11-formalization/evidence/root/make_payload.py
```

### 3.3 R9 的量化发现与派工（`Fm` 的 trig 精度缺口）

- **发现（claim C1002，proved-exact 的算术事实）**：`Interval/Trig.lean` 的 sin/cos 是**低阶** Taylor
  （`q − q³/6 ∓ |q|⁵/100`、`1 − q²/2 ∓ |q|⁴·5/96`），在证书盒心角值上包络宽度达 `1.676e-4`（sin）/
  `2.272e-3`（cos）；而 `hres` 需 `η < 9.956e-10` ⇒ **缺口 ≈ 1.68e5 倍**。
  根因是残差的**灾难性相消**（量级 0.38 的项相减得 ~1e-17）。
- **独立复算（claim C1003，`numeric`，interval-core）**：N=3 超阈值 **1.83e6** 倍（负对照成立）、
  **N=9 首次满足**（`3.872e-11`）、N=19 余量 2.5e17 倍。与 C1002 一致。
- **明确边界**：这是**当前内核的方法极限**，**不是** G1/C891 的反例，**不是**对已交付 M5b（R2/R3/R4）的否定；
  `sqrt`（精确外向舍入）与 `π`（20 位）**不是**瓶颈；`Jt`（Jacobian 包络）只需 ~1e-3，**当前内核够用**。
- **复核归位**：interval-core 的复核事件落在 **C1000**，其 note 明示对象为 `mem_krawczykMat`（属 C1000）
  **与** `norm_ratMatCLM_le`（属 **C1001**）两者——跨两条 claim，已在两处生效，不需要再挂。
- **派工**：高阶 Taylor 有理界的**内核版**，范围收窄为 **N=19 固定阶**（`20 ≡ 0 mod 4` ⇒ 第 20 阶导数是 `sin`），
  外加"内核里复现旧界不够"的负对照。

---

## 7. 口径纪律：**"我算的是哪个定义的哪个量"**（R69 立项，第 4 次同族事故后）

**触发**：本工程已出现 **4 次同族事故**，机制相同：**算的量与声称的量口径不同**，而读数本身"看起来正常"。

| # | 事故 | 口径差在哪 | 后果 | claim/出处 |
|---|---|---|---|---|
| 1 | 旧预条件表 8/35 格错 | `h = 1e-3` 差分截断（而非精确区间） | 最大偏 `0.4517` | **C1051** |
| 2 | `mp.mpf(iv.pi.a)` 把 π 压到 15 位 | 浮点二次舍入**向内** ⇒ 破坏外向性 | 宽度显示成 0 | **C1061** |
| 3 | 窄窗口三角核的点分离型读数恒 0 | 窗内 `\|x\| ≤ 1` vs 实际 `θ` 达 ±2.77 rad | **静默空转**（不报错） | `box-rstar` 自查 / `C1100` |
| 4 | `Y = J⁻¹` 算得 `K = 8.0e-60` vs 源链 `K = 0.00437…` | **`K` 定义中 `Y` 是近似逆、`J` 是盒上区间 Jacobian**；用了精确逆 + 点 Jacobian | 差 **57 个数量级** | R68 裁决 |

**⇒ 纪律（对所有成员、对每一个数值/区间/证书读数）**：
1. **写清三件**：(a) **量名与定义**（照抄源文/既有 Lean 定义，不凭印象）；(b) **参数**（盒/点/步长/精度/算术：精确有理？区间？浮点？）；(c) **与谁的哪个量比较**。
2. **仪器必须先校准**：新写的计算工具，**必须先复算 ≥1 个已由内核/独立路径验证的已知值且逐位相同**，才允许产出读数（`d-nodes` 的镜像 7/7 逐位、`box-rstar` 的 7/7 一致、`jt-build` 的 5/5 逐位，都是标准做法）。
3. **读数必须绑定内容**（`C⁷`）：附输入文件与自身脚本的 SHA256 前 16 位；**读数文件的时间戳必须晚于它所解释的代码**（本轮实战：`d-nodes` 的 Lag 宽度读数在 00:11:40，代码在 00:04:40 ⇒ 可归因；我早先读到 23:56 的旧版，其 max 仍是非 Lag 的 `4.787e+00`）。
4. **"更弱"不是"矛盾"**（`C1094`）：对**下界 > 0** 型断言，唯一有判别力的比较是"**该下界是否 > 0**"；给出更小的正下界与对方**可同时为真**。**"我证不出" ≠ "对方错了"**。
5. **禁止从口径错位的读数推结论**（尤其**不得**推"预算变宽松/收紧"）—— 口径先对齐，再谈结论。


### 7.1 「包络/界」型前提的**量词范围**机械核对（R78 增补，源自 `hnd-lean` 的 `SCOPE-AUDIT.md`）

**为什么单独立一节**：本工程同族事故里，**"同一量名、不同量词范围"** 是与"口径错位"并列的第二大来源，
且它**比口径错位更隐蔽** —— 因为**类型相同**，插进槽位**不会报错**，只是在语义上**静默失去覆盖** ✗。

**核对表判据（照走四步）**：① 打开**消费者**的 `文件:行`，**逐字**读它要的量词与范围；② 打开**供给侧**，逐字读它给的量词与范围；③ 判定 `同口径 / 窄（供给比消费者小 ⇒ 必须补覆盖）/ 宽（安全，但要确认能否真搬用）/ 无数值`；④ **危险点必须区分 (S) 静默类 与 (E) 报错类** —— (S) 才是真正危险的。

**`SCOPE-AUDIT.md`（`D609693A1BF31258`）的两条结论（可直接引用）**：
- **(C1)** G1 链上「范围不一致」**只有一处**：`Jt` 的逐元素包络（`hJ`/`henc`）—— 供给侧只到**盒心点**、消费侧是**球上全称** ⇒ **修它即可把该族风险清零**；其余全部**同口径**或**设计即点**（`hFm` 的消费者本来就只要盒心一点，且已闭合 ✓）。
- **(C2) 静默类 (S) 危险点共 4 处**：① `hJ`/`henc`（球 vs 心，**类型相同**）；② **`hsum` vs `hsumR`** —— **`Y·J` 与 `J·Y` 是两个不同矩阵、两个同名 `K`**；③ `hηb`/`hres`/`hK`（两条 `K` 口径，`η` 容差差 `≈4.4e-13` = 相对 `4.4e-4`）。(E) 报错类：#3 逐点定理 vs 球上槽位、`hYinv` 无供给 ⇒ **不会静默**、风险低。

**R78 Lead 的机械复核（对 (C2)② 的现场检查）**：`BoxRstar.lean:429` 把 **`hsumR`** 用在 **`I − J·Y`** 的槽（`injective_ratMatCLM_of_right_enclosure` ✓）、`:447` 把 **`hsum`** 用在 **`I − Y·J`** 的槽（Krawczyk 步 ✓），且源码**自己文档化**了这个相反顺序（L67、L394–395）⇒ **当前代码干净、无转置** ✓ —— 但该"潜在类"确实存在（两者形状相同 ⇒ 转置会静默通过 ✗），故**必须留在本节备查** ✓。

**两条操作规则（`hnd-lean` 建议、Lead 采纳）**：
1. **任何"包络/界"型前提，写进槽位之前先抄一遍消费者的量词与范围**（不许凭"名字像"就插 ✗）；
2. **每次有供给**升级（如球上 `hJ` 落地）**必须复跑本核对表**，把状态从「未闭合/在飞」改为「已闭合」，并**复核量词**（不是改状态就完事）。

### 7.2 「断言/守卫也是仪器，也要有判别力」（R96 增补，源自 `d-nodes` 对 Lead 的一条更正）

**事件**：Lead 在 R93 给出一条"防护规则"——**"同层不得既展开某定义、又指望它的字面量引理"**——`d-nodes` 据此写了 `assert_no_shadow`；该断言随即对 `DEFS_B` 报错（`DEFS_B` 列有 `dAngle/dTheta/dThetaCoef/dThetaSum`）。**但层 B 事实上通过了**（`LB_drhoIv_3_0`/`4_0` 已闭合）⇒ **Lead 的前提是假的** ✗。

**⇒ 正确表述（已采纳）**：**缺陷不是"列了被覆盖的定义"，而是"在那个层的 simp 顺序/优先级与上下文下，定义先被展开、以致字面量引理的模式再也匹配不上"** ✓。断言只能针对**实证过的那一对**（例如层 C 的 `drhoIv` 等 **与** `LB_drhoIv_*` 同时出现），并**必须在代码里注明它是启发式而非定理** ✓；**不得用它否决一个已被实证可行的配置** ✗。

**⇒ 由此立为常设口径**：**断言/守卫也是仪器** ⇒ 必须满足本节 §7 的全部要求（**先校准、写清量名与参数、绑定内容**），**并且本身要有判别力**：
- **断言不报警 ≠ 安全**（它可能根本不覆盖该缺陷类）；
- **断言乱报警 = 错工具**（它会拦下**可行**的配置 ✗）—— 这与 `box-rstar` 早期"静默空转的三角核"**同族**：**仪器没有判别力时，它的读数与结论都不可用** ✓。

**自检**：任何新加的断言/守卫，**必须同时给出 (i) 一个应通过的实证可行配置、(ii) 一个应被拦下的真实缺陷配置**；两者缺一，则该断言**尚未校准** ✓。

---

# §7 TRUST 更新（**R186–R258 末，Lead**）—— 可信基础、九族假设的逐族状态、非定理读数、新工具要求

## 7.1 基线与根 cone 成员（Lead 两次连续串行实测）
```
根 lean/N11Formalization.lean = **8EB2CD279AF4578D / 77 imports / exit=0 / 0 error / 0 warning / jobs=8801**（1st、2nd 相同 ✓✓）
本会话入根 18 片：G3/SliceL0..L6 ｜ Interval/ArcsinBracket（1e-12 版）｜ LeafAgg ｜ F1/BallD35Hrad,C1,C2,C4,C5,C6,C7,C8,C9,C10
原位替换（**同路径 ⇒ jobs 不变 + 内容变**，文档化签名 ✓）：ResidualDerivJTHess.lean  44AD15CA689393D7(17640B) → **27F2CFC9EF8D81B9(19563B)**
  替换后 Lead **立即两次连续串行重建** ⇒ exit=0/0/0/jobs=8801 ⇒ **未弄红** ✓（声明级复核：secondPartial_add / secondPartial_sub 确实在声明里 ✓）
```
## 7.2 `#print axioms` 实测（本会话新增件）
```
全部标准三元组 [propext, Classical.choice, Quot.sound]（F1 侧十件共 70 条画像、G3 各片、LeafAgg 等）✓
更干净者（可作"剖面"证据）：chainOK_sound = **[propext, Quot.sound]**（无 Classical.choice）｜
  runSum_append = **[propext]** ｜ blkLIE_rejected = **[propext]** ｜ **ms3LIE_rejected = 不依赖任何公理（纯计算）** ✓✓
零 sorryAx ／ 零自定义 axiom ／ 零 native_decide（红件的画像一律不引用 ✗ —— 失败编译的 sorryAx 是占位 ✓）
```
## 7.3 ★**验收缺口的逐族清单**（把"判据二未达成"变成可数对象）✓✓
主入口 = `BoxRstar.lean` L362 `c891RootSpec_of_krawczyk {K η : ℝ}`，其假设（L363–382）分九族；**逐族状态与供给件（全部在根 cone 内）**：
```
已付 ✓✓（球级、内核证成）
  hndRho   ← NondegProof.nd_hndRho (L433)      ：∀ x ∈ closedBall certCR rhoCertR, ∀ j : Fin 9, …
  hndW     ← NondegProof.nd_hndW (L443)
  hndU1/2/3/8 ← NondegProof.nd_hndU{1,2,3,8}_via_dist (L777/786/795/804)   —— 均为 **∀ x ∈ ball** 形状 ✓
  hndWp    ← NondegProof.nd_hndWp_via_dist (L813)  ｜ 打包件 nd_all_via_dist (L823) ✓
  （另有盒级版 nd_hndRho/nd_hndW/nd_hndU*/nd_hndWp + nd_all、以及 nd_end_to_end(_right)/nd_plug_*_data 收口件 ✓）
部分/待实例化 ✗
  Fm/hFm   ← FmAssembly.fmCert + **mem_fmCert (L168) / mem_fmCert_cert (L186) / mem_fmCert_of_point (L193)**（件在根 L51 ✓）⇒ 缺"用证书 D 实例化"这一步
  hηb      ← Precond.incrMatVec（件在根 L28 ✓）⇒ 缺 η 界
未付 ✗
  Jt/hJ    ← **12×12 球级 Mem**；现状：残差行已全（r<5：c=up7 j ← C9、c=up5 m ← C10，均无条件）；
             **KKT×λ = (c)（根因已定位到一条：hg.comp 的合成式形状）**；**KKT×z 49 格 ⇒ 需 Hess**（H3/H4；叶子 ring2/Wy2 在造）
  hsum     ← `Σ_j max|(krawczykMat Y Jt i j).lo/hi| ≤ K`；**35 格宽度仍 numeric、kernel 内不可消费** ✗
算术侧（须内核可消费）
  hK0/hK1/hη0/hres ← K = **0.0043719716348663187201**、ρ = **1e-9**、阈值 **fmThreshold := 9956/10^13**（ResidualIntervalReadout L909）；hres 需 η < 9.956e-10
```
## 7.4 ✓✓ 一条**老缺口已闭**（TRUST §3.3 的"Fm 的 trig 精度缺口"应标 superseded）
```
`IntervalsHigh.lean` L272/278/325 **内核判定**：sinHiN−sinLoN@3843/10000、@3720/10000、cosHiN−cosLoN@3843/10000 **均 < 9956/10^13** ✓✓
（件头 L22 记录：已低于阈值 **约 80 倍**；m=14 给 |x|^29 = 9.0e-13、约 1100 倍余量 ✓）
⇒ **该项从"未形式化的承重义务"移入"已付"**；旧 §3.3 条目**留痕但不作现役结论** ✗
```
## 7.5 可信边界：**非定理读数**（不得当定理用）
```
· **`Hess` 宽度预算 `w* ≈ 0.383`**（evidence/jth-assembly/K-BUDGET.md）—— **校准过的敏感度读数，是**预算**不是证明** ✗；
  **实测宽度仍缺**（ring2/Wy2 未落 ⇒ 无可测对象；两流均拒绝用根外件造读数 ✓）
· 成本读数一律**绑定前件**：0.2695 s/证（拼接 checker + 37 项 + 无 maxRecDepth）**只对它自己的对象成立** ✗（与 5–10 s/叶 不可互推 ✓）
· **体量成本 ≠ 实例化成本**（124130 项 ≈ 15 分钟 ✓ vs 实例化是墙 ✗）—— 两个独立因子，须分列报 ✓
· **"装配处 elaborator 会展开项列表"** ⇒ 代价 ∝ 项数、与块大小/链式/尺度 D 全无关（四条形状一堵墙 ✓）
```
## 7.6 新工具要求（本会话升格，可执行判据）
```
**每个 checker/判定器必须附一条 `*_rejected` 伴生定理**（给出**具体说谎见证**并证明被拒）—— **sound 与 vacuous 的分界** ✓✓
范例：chainOK_sound + **ms3LIE_rejected（不含任何公理）** ｜ runSum_append + **blkLIE_rejected（[propext]）**
**待补** ✗：checkA（SliceL8）、leafCheck（LeafAgg）—— 目前只证了"接受真输入"（已指派 g3-recon）
```
## 7.7 复现（最小命令集）
```
根闸:        cd lean ; lake build            → 期望 exit=0 / 0 error / 0 warning / jobs=8801（**跑两次** ✓）
单件:        cd lean ; lake env lean <文件绝对路径>   → **成功时输出为空（0 B）** ⇒ 读法 = "0 B + 同一次调用 EXIT=0" ✓
接根四步:    ① Copy-Item 后逐字节 sha256 比对 ② **整库 Unicode 感知精确整行共查**（注意注释块假阳 ✗）
             ③ 改根表 + 写 provenance 注释 ④ **两次连续串行 lake build 核 jobs +N**
在飞件:      一律只在 evidence/ 下（不进 srcDir、不影响根闸）✓
```

---

# §7.3bis ★**口径层次纠正（Lead 自查）**：判据二的**真入口**不是 `c891RootSpec_of_krawczyk`，而是 `nd_end_to_end`
```
**我 §7.3 的表**低了一层** ✗：那张表列的是 `BoxRstar.c891RootSpec_of_krawczyk`（L362）的九族假设；
**真正的主线总装定理 = `NondegProof.lean` **L615 `nd_end_to_end`**（**在根 cone 内、已内核证成** ✓✓）**，
它**内部已自带七条 hnd\*（经 `nd_plug_full_data` L584）** ⇒ **判据二的真缺口 = 供它的那串**数据**** ✓✓
**`RootSpecBall` 也不是打包结构**（我上一轮猜错 ✗）：`BoxRstar` L243 一行 `def RootSpecBall : Prop := ∃! x, x ∈ closedBall certCR rhoCertR ∧ TCSystem x = 0`（= 球口径唯一性命题 ✓）
```
**`nd_end_to_end` 的**精确假设清单**（逐项 = 判据二的待办项）**：
| 数据项 | 形状 | 现状 |
|---|---|---|
| `Y Yinv` + `hYinv` | 有理预条件子 + 左逆 | **未定位**（`Precond*` 一带待穷尽搜） |
| `K η` + `hK0 hK1 hη0` | 收缩常数（算术侧） | **未定位**（常数在根：K=0.0043719716348663187201、ρ=1e-9） |
| `hres` | `η + K*ρ < ρ`（ρ = rhoCertR） | **未定位**（阈值 `fmThreshold := 9956/10^13`，`ResidualIntervalReadout` L909） |
| `Jt` + **`hJ`** | **12×12 球级 Mem** | **进行中**：残差行已全（C9+C10 无条件 ✓）；KKT×λ = (c)（**收敛到 1 条新引理 + 2 处形状修正**）；KKT×z 49 格 ⇒ 需 `Hess`（H3/H4；**其盒心模板 = `fderiv_TCSystem_kkt_z` L520** ✓） |
| `hsum` | `∀ i, Σ_j max|krawczykMat Y Jt i j| ≤ K` | **未付** ✗（35 格宽度仍 numeric、kernel 内不可消费） |
| `Fm` + **`hFm`** | 残差五分量证书 + 其 Mem | **根内已有现成件** ✓：`FmAssembly.lean`（**根 L51**）`fmCert` + `mem_fmCert`(L168)/`mem_fmCert_cert`(L186)/`mem_fmCert_of_point`(L193) ⇒ **只差实例化** |
| **`hηb`** | `∀ i, ((incrMatVec Y Fm i).abs).hi ≤ η` | **未定位**（`Precond.incrMatVec` 在根 L28 ✓） |
⇒ **⇒ 判据二 = 把这条**已证的**总装定理实例化**；缺口是**有限的数据项**，而不是"主定理还没装"** ✓✓
**已派 `fm-eval`**（该义务的原主流）攻 `hFm`/`hηb`/`Y` 三片，**先查后写、找不到就报"缺什么/新数学还是装配"** ✓

---

# §4bis **外部数据的可信边界**（Lead 更新，R259）—— `Y` 的 binary64 近似逆：路线与口径裁决

**① 事实（`fm-eval` 独立复核 + Lead 采信；且与根内自己的记载一致）** ✓
```
`BoxRstar.lean:360` 与 `NondegProof.lean:578` 均写明：**源预条件子是 binary64 近似逆**
⇒ **精确有理左逆 `Yinv·Y = I` **取不到**** ✗（**源数据即二进制浮点，不是精确有理数**）
⇒ 根内**查无任何 `Yinv` 声明/数据/供给件** ✓（`fm-eval` 穷尽搜 ✓；Lead 亦未搜到 ✓）
```
**② 路线裁决：走**右侧收缩**** ✓✓
```
**`nd_end_to_end_right`（`NondegProof` L650 `nd_plug_right_data` 已就位 ✓）** ⇒ 数据项 **`Y/Yinv/hYinv` 作废** ✗，
**改为 `Y` + 右侧数据（`hsumR` / `K'`）** ✓（代价 = 多一条 `hsumR` ✓；与 `BoxRstar.c891RootSpec_of_right_data`（R10 入口）同侧 ✓）
```
**③ 数据口径裁决：bit-精确转写 + **显式可信边界**（不许静默）** ✓✓
```
(a) **转写**：`Y` 取该 binary64 值的**精确 dyadic 有理数** —— **binary64 都可精确表示为有理数** ⇒ **这不是近似** ✓
(b) **但"出处"是未验证输入** ✗：`"Y 是源 Jacobian 的计算近似逆"` **不是定理** ⇒ **必须作为显式**可信数据边界**记录在此** ✓
    —— **不得**在 Lean 里做成隐式假设 ✗、**更不得**做成自定义 `axiom` ✗（**"无未证研究公理"是硬验收** ✓）
(c) **本节的效力范围**：此条**只是信任声明，不是证明** ✗ —— **任何依赖它的定理仍是**条件式/外部数据依赖**的** ✓
    （**口径**：**外部数据不因下游算术精确而变成已证** ✓ —— 与"numeric 前提不因下游精确而成定理"同族 ✓）
```
**④ 影响**：判据二的数据项清单更新为 —— `Y`(bit 转写) + `hsumR`/`K'`（右侧）｜ `K/η/hres`｜ `Jt`+`hJ`｜ `hsum`｜ `Fm`+`hFm`（**已归约到已证的 `hD`** ✓）｜ `hηb` ✓

---

## ⚠ **头条计数更正（Lead 自查，R261）**：球级列不是 25/144，而是 **60/144**

**原写法（错/过期）** ✗：**"球级列 25/144 有付 / 119 未付"** —— 我在 4 本台账与几乎每份报告里重复过它。
**更正后（根内实测）** ✓✓：
```
球级 `Jt` 格 = `∀ x ∈ closedBall certCR rhoCertR`（或 `pad12 z ∈ ball`）下的 `(Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k)`，**共 12×12 = 144 格**
**已证** ✓：`mem_Jt_res_z_ball`（C9 L90；(k : Fin 5)(j : Fin 7) ⇒ 残差行 × z 列 = **35 格**）＋ `JT_lam_res_ball`（C10 L82；(k m : Fin 5) ⇒ 残差行 × λ 列 = **25 格**）＝ **60 格**
**未付** ✗：`Jt` 的 **KKT 行**（r ≥ 5）= 7 行 × 12 列 = **84 格** = **KKT×z 49 格（需 `Hess`）** ＋ **KKT×λ 35 格（= (c)）**
⇒ **⇒ 更正：60/144 有付 / 84 未付**；**且 84 = 49 + 35 恰好等于两条流手上的两半** ✓✓（**一致性核对** ✓）
```
**错因（记我头上）** ✗：**"25" 是 λ 列那一半的数**（C10），我把它当成了球级总计数 —— **即把"某一子块"的数当"全列"的数** ✓
**⇒ 口径**：**计数类头条数字必须**每次引用时重算**（或至少标明它是哪个子块的数）** ✓✓ —— 与"被引用的状态串必须是与当下绑定的读数"同族（**这是它在我身上第 N 次生效** ✗✓）
**⇒ 影响范围**：`STATUS` ／ `TRUST §7.3bis/§4bis` ／ `SOURCE-MAP §9.5` ／ `HANDOFF §10` 中的该数字**均以本更正为准** ✓

---

## ⚠⚠ **头条计数的第二次更正（Lead 自查，R261b）—— 上一次更正本身过宽** ✗✓

**第一次更正（R261）** 我写成 "**球级列 60/144 有付**" —— **仍不准确** ✗：
```
`hJ`（`BoxRstar` L375）的量词是 **∀ x ∈ closedBall certCR rhoCertR** ⇒ **一般 12 维点（λ 可 ≠ 0）** ✓
而 C9/C10 的两条已证件都是 **`pad12 z` 形状**（我只核了签名 ✓）：
  `mem_Jt_res_z_ball (k : Fin 5) (j : Fin 7) (z : Fin 7 → ℝ)`（C9 L90）—— **λ=0 切片**上的残差行 × z 列 = 35 格
  `JT_lam_res_ball (z : Fin 7 → ℝ)`（C10 L82）—— **λ=0 切片**上的残差行 × λ 列 = 25 格
⇒ **它们只覆盖 λ=0 那一层切片** ✗ —— 而 `x ∈ ball` **不蕴含** `pad12 (first7 x) ∈ ball` ✗（压 λ 到 0 会移动点 ⇒ 范数变）
**⇒ 正确写法（双计数，按消费方参数化）** ✓✓：
  · **λ=0 切片（`pad12 z ∈ ball`）**：**60/144 已证** ✓（C9+C10）
  · **一般 `x ∈ ball`（= `hJ` 的消费方形状）**：**待判** ✗ —— 由 `f1-step2` 判 **(甲) 够 / (乙) 需一般化重述**（已派，附 λ-无关线索）
```
**错因（记我头上，第 2 次同一族）** ✗：**我第一次更正时只改了数、没核**参数化是否覆盖消费方的自由度**** ——
**而这正是 `f1-step2` 刚教我的那条口径**（"参数化必须对着消费方检查" ✓✓）⇒ **我把它写进口径却没先用在计数上** ✗✓
**⇒ 口径强化**：**凡"计数/覆盖"类断言，必须先写清**消费方的参数化**，再数 —— 否则数本身无意义** ✓✓
**⇒ 影响**：`STATUS` / `TRUST` / `SOURCE-MAP` / `HANDOFF` 中一切"球级 X/144"字样**以本双计数为准** ✓；
**并撤回 R261 的单值 "60/144" 表述**（**不是撤回更正本身** —— 更正"25 是子块数"那部分仍成立 ✓）

---

## ⚠⚠⚠ **头条计数的第三次更正（Lead，R262）—— 这次是向下的、也是唯一诚实的方向**：消费方形状 = **0 / 144**

**事实（`f1-step2` 判决 + **Lead 独立核过源文**）** ✓✓✗
```
**球的 λ=0 切片在球内是**空集**** ✗✗：`BoxRstar.lean` L91–103 `def certC` 的 λ 分量（coord 7..11）=
  `-2050658785296173/2^54`、`-7385064427961529/2^58`、`-7661580961047613/2^60`、`-2860603688525993/2^57`、`-7612361213708557/2^58`
   ⇒ ≈ **−0.11383, −0.02562, −0.00665, −0.01985, −0.02641** ⇒ **max|λ_cert| ≈ 0.1138** vs **ρ = rhoCertR = 1e-9** ⇒ **差 ~8 个数量级** ✓
⇒ 球内任何点都有 `|λ_i − λ_cert,i| ≤ ρ`（某 i）⇒ **λ 全为 0 的点不存在** ⇒ **`pad12 z ∈ ball` **零实例**** ✓✓
```
**⇒ 正确的消费方形状计数** ✗：
```
**`∀ x ∈ closedBall certCR rhoCertR`（= `hJ` 的消费方形状）下：0 / 144 有付 ／ 144 未付** ✗
（**不是 25**（那是 λ 列子块）✗；**不是 60**（那是 λ=0 薄片上的格数，而该薄片在球内为空 ✗））
```
**⇒ 对 C9/C10 的准确刻画** ✗✓：**它们**不是假****，而是**对消费方**空泛（vacuously true）**** ——
`pad12 z ∈ ball` **不可满足** ⇒ 两条定理的真假无碍，但**对 `hJ` 的贡献 = 0** ✗（**"真空真" ≠ "已付"** ✓）
**⇒ 三次更正的教训（Lead 自记）** ✗：**25**（子块的数当全列）→ **60**（空切片上的数当全列）→ **0**（正确）——
**两次都把"某一参数化层上的数"当成了消费方的数** ✗ ⇒ **强化口径（第 3 版）**：
> **计数类断言必须**三件齐备**：①消费方参数化 ②**该参数化在定义域内是否可满足**（空域 ⇒ 计数为 0）③计数** ✓✓
**⇒ 修法（便宜、近逐字）** ✓✓：所有区间 `Mem` 供给件本吃**任意** 12 维 `x ∈ ball`（`ndBox_mem hx`／`wkBox_mem hx`／`WpIvBox_mem hx`／`radIvBox_mem k hx` ✓），
**C8 的三条非退化供给本就是一般 `x` 陈述** ✓ ⇒ 只需 `pad12 z ∈ ball` → **`x ∈ ball`**、`z` → **`first7 x`** ⇒ **60 格一次搬到消费方形状**（计数 0 → 60 ✓）
⇒ **三段账**：**重述 60** ＋ **(c) 35** ＋ **`Hess` 49** = **144** ✓✓（已批准 `f1-step2` 先做重述——它是计数上单笔最大增益 ✓）
**⇒ 并记一条**几何事实**（`f1-step2` 给的，我已采信）** ✓：**"球在 z 方向的投影 ⊂ `ndBox` 的前 7 维"是真的**（`ndBox_mem` 对任意 `x ∈ ball` 成立 ✓）⇒
**包络从不是卡点** —— **(甲) 所需的几何引理是**假的**** ✗（**这才是 (甲)/(乙) 判决的实质** ✓）

---

## §8 独立复核记录（Lead，R278 —— "中央结论用不同表示/不同推理各查一遍"的落地）✓✓

**对象**：`lean/N11Formalization/HsumPayload.lean`（`a82270b7397bff30`，真实 `(Y,J)` payload + 真实 `hsum`/`hsumR`）

**为什么需要**：它的 `certReal_check`/`certRealR_checkR` 由**内核 `decide`** 核过 ✓ —— 但 `decide` 用的是 **Lean 内的整数行和定义**
（`HsumCert.loNumD`/`hiNumD`/`rowZ`）⇒ 若那些定义本身写错，`decide` 只会忠实核错对象 ✗ ⇒ **需要一条**不读那些定义**的独立路径**。

**独立路径（`evidence/lead/verify_hsumpayload.py`，可复现）**：
```
只从 Lean 源**解析整数**（Dz 321 bit／numYz／loNumz／hiNumz／numKz／numKRz／Ez = Dz² 641 bit），
用**独立精确有理实现**（fractions.Fraction，区间乘**按符号分支**，与根内 Interval/Core.lean:178 的四角 min/max 同口径）重算
```
**读数（三路一致）**：
| 量 | 我的独立复算 | Lean（`decide` 核过） | 源字段（`root-box.json`） |
|---|---|---|---|
| `K`（左，`I−Y·J` 最大行和） | **4.3719716348663189078860e-03** | **同一有理** ✓ | 22 位十进制相同，**精确有理不同** ✗（差 ~1e-22 ✓） |
| `K'`（右，`I−J·Y`） | **4.9754871529404153321363e-03** | **同一有理** ✓ | —— |
| `fmThreshold ≤ ρ(1−K)` | **True**（比 0.9999718485575584） | —— | —— |

**⇒ 结论**：payload 的整数数据与内核读数**一致** ✓✓；`hres` 的承重算术**成立** ✓✓；
**并确认**：**必须用 `certReal.numK`**（payload 的精确 `K` 与其记录值**不是同一个有理**，差 ~1e-22 ⇒ 配错即假 ✗✓）。
**⇒ 未改变任何 scope**：`Y`/`J` 的**出处仍是外部计算** ✗（见 `TRUST §4bis`）—— 本条只复核**给定整数上的读数** ✓
