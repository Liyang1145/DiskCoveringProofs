# Q1-CLASS-COVERAGE-FINAL —— q1 各 start 的类覆盖核对 + 所有 saved upper 严格 < π 的审计

> 路由 cline2/deepseek-v4.1f；只写 `r20-alternative/`；**未重跑长内核、未改任何 lead 脚本/产物、未重审 atan2**。
> 按 lead 指示（team-message-c5df34ee）：**重建枚举（不信文档轨道）**、查 certificate JSON、列每类证据与**真 upper**。
> 复现：`py -3 -B -X utf8 research-2026/team-current/r20-alternative/q1_class_coverage_enum.py`（只读 JSON + 独立枚举）。

## 0. 口径与输入

- 源（只读）：`lead/Q1-DEGREE5-EXCLUSION.md`、`lead/Q1-BALANCED-EXCLUSION.md`、`lead/COMPATIBLE-POSITION-EXCLUSION.md`；
  certificate JSON：`shared_factor_certificate_{0,1,2,3}_3.json`、`compatible_position_certificate.json`、
  `shared_moment_dense_certificate_{0,2}_4.json`、`compatible_position_fraction.json`。
- 枚举的定义（**本件独立重建**，与生成脚本的约定一致但独立实现）：
  9 环 = 循环 `0..8`，耳 `(0,1,2)`，去掉耳中点 `1` 得核心 8 循环 `core = [0,2,3,4,5,6,7,8]`；
  `start s` = 将 core 循环旋转到以 `s` 开头后取前导块：
  - **degree-(5,7)**：degree-5 hub 站点 = 4 站块 `c[:4]`（3 条边 ✓），degree-7 hub 站点 = `c[3:]+c[:1]`（6 站 ✓）；
  - **balanced (6,6)**：两 hub 各 4 条边 ⇒ 各 5 站块 `c[:5]` 与 `c[4:]+c[:1]` ✓。
- 生成元：**环反射** `R(i) = (2−i) mod 9`（对站点集合作用）；**hub 交换** `(a,b) → (b,a)`——
  仅在**两 hub 度数相等**时是图自同构（合法）；(5,7) 情形度数不等，交换不是自同构 ✓。
- 轨道用 union-find 闭合（本件自写，不含任何来自文档的轨道表）✓。

## 1. 枚举结果（独立重建 vs 文档）

| 情形 | 本件轨道（R 单独） | 本件轨道（R + hub 交换） | 文档声明 | 判读 |
|---|---|---|---|---|
| **q1 (5,7)** | `{0,6}`,`{1,5}`,`{2,4}`,`{3}`,`{7}` | 同左（交换**不**增加识别） | `{0,6},{1,5},{2,4},{3},{7}` | **一致 ✓** |
| **balanced (6,6)** | `{0,5}`,`{1,4}`,`{2,3}`,`{6,7}` | `{0,1,4,5}`,`{2,3,6,7}` | `{0,1,4,5},{2,3,6,7}` | **一致（须含 hub 交换）✓** |

**⚠ 承重提示（本件新增的显式依赖）**：balanced 的类划分**必须**用 hub 交换；
`R` 单独只给 4 个类，那么已保存的两张证书（start 0、start 2）只覆盖 `{0,5}` 与 `{2,3}`，
**漏掉 `{1,4}` 与 `{6,7}`** ✗。而 hub 交换在 (6,6) 情形合法**仅因为两 hub 度数相等** ——
这一条是 balanced 覆盖的**前提**（文档写了"reflection and hub exchange"，本件把它标为显式依赖 ✓）。

## 2. 类覆盖（谁被证书覆盖，谁靠对称传播）

**(5,7)**（证书 5 张，覆盖 {0,1,2,3,7}）：

| 类 | 证书 | 传播 |
|---|---|---|
| `{0,6}` | `shared_factor_certificate_0_3.json` | 6 = R(0) ✓ |
| `{1,5}` | `shared_factor_certificate_1_3.json` | 5 = R(1) ✓ |
| `{2,4}` | `shared_factor_certificate_2_3.json` | 4 = R(2) ✓ |
| `{3}` | `shared_factor_certificate_3_3.json` | 自固定 ✓ |
| `{7}` | `compatible_position_certificate.json` | 自固定 ✓ |

⇒ **8/8 个 start 全覆盖** ✓（无证书文件的 start 为 4,5,6，全部由 R 传播 ✓）。

**(6,6)**（证书 2 张，覆盖 {0,2}）：

| 类 | 证书 | 传播（R + hub 交换） |
|---|---|---|
| `{0,1,4,5}` | `shared_moment_dense_certificate_0_4.json` | 1,4,5 ✓ |
| `{2,3,6,7}` | `shared_moment_dense_certificate_2_4.json` | 3,6,7 ✓ |

⇒ **8/8 个 start 全覆盖** ✓（依赖 §1 的 hub 交换前提）。

## 3. 所有 saved upper **真实严格 < π**（精确有理比较，无浮点判定）

比较方式：把 JSON 里的十进制串解析为 `Fraction`，判 `hi < 314159/100000 = 3.14159`，
再用记录的 `pi` 区间下界复核 `hi < π_lo(recorded)` ✓（并验证记录的 `pi` 区间**含** π：
`π = 3.14159265358979323846264338327950288…` ∈ `[3.14159265358979323846264335039, …40209]` ✓）。

| 类 | certificate | start/span | **真 upper（全精度）** | hi < 3.14159 < π | strict 标志 | 因子数 |
|---|---|---|---|---|---|---|
| (5,7) start0 | `shared_factor_certificate_0_3.json` | 0 / 3 | `[3.13537180357528556126941781148, 3.13537180357528556126941843187]` | ✓ | True | 29 |
| (5,7) start1 | `shared_factor_certificate_1_3.json` | 1 / 3 | `[3.11671983052145319122885714691, 3.11671983052145319122885771559]` | ✓ | True | 29 |
| (5,7) start2 | `shared_factor_certificate_2_3.json` | 2 / 3 | `[3.09070695189895955907801785461, 3.09070695189895955907801857839]` | ✓ | True | 29 |
| (5,7) start3 | `shared_factor_certificate_3_3.json` | 3 / 3 | `[3.08927774407683435426158557633, 3.08927774407683435426158619672]` | ✓ | True | 29 |
| (5,7) start7 | `compatible_position_certificate.json` | 7 / 3 | `[3.139627044416903102133305523983082865172, …503042719]` | ✓ | True | 24 系数 / N=65536 |
| (6,6) start0 | `shared_moment_dense_certificate_0_4.json` | 0 / 4 | `[3.13549360291499034831398630214, 3.13549360291499034831398671573]` | ✓ | True | 29 |
| (6,6) start2 | `shared_moment_dense_certificate_2_4.json` | 2 / 4 | `[3.13981254422259203355720467746, 3.13981254422259203355720550464]` | ✓ | True | 29 |

**独立精确控制（start7 类）**：`compatible_position_fraction.json` 的 `upper_rational = 785349/250000 = 3.141396`
（`N=16384`，精确分数 + 解析凹支撑切线）< `3.14159` < π ✓ —— 与上面的区间证书**互相印证** ✓。

文档中的四舍五入写法（`<3.135372`、`<3.116720`、`<3.090707`、`<3.089278`）与 JSON 真值一致 ✓
（上表给出**全精度真值**，比文档更细）✓。

## 4. 审计中发现的限制 / 需 lead 注意的点

1. **JSON 未记录分解常数**：`shared_*` 证书里只有 `upper`、`coefficients`、`factors`（29 个）；
   **29 个因子 upper 之和 ≈ 6.33–7.58 > 总 upper（3.09–3.14）** ⇒ 分解常数约为 **−3.2**，
   即这些证书的**本质是"抵消型对偶"**，总上界**不是**正局部界之和。
   ⇒ 仅凭 JSON **无法**独立重算总上界（本件只审计"记录值 vs π"与因子结构）；若需完全独立复核，
   需生成器**补输出该常数**（本件不代改）✓。
2. `strict: True` 是**自述标志**；本件已独立用记录区间做了精确有理比较 ✓（结论与标志一致 ✓），
   但**不是**对区间内核的独立复算（按 lead 指示未重跑）✓。
3. `compatible_position_certificate.json` 结构不同（无 `factors`，有 24 个系数 + `N=65536`），
   本件按同一 `upper`/`pi` 口径比较 ✓。
4. 本件的范围**仅是"类覆盖 + 记录上界 < π"**：不含对区间算术内核的再验证、不含 q0、不含 sharp bound，
   也不主张 q1 的排除已获独立复核（那是另一项义务）✓。

## 5. 结论（对 lead 义务的回答）

- **枚举重建**：两族类划分与文档声明**完全一致** ✓；其中 balanced 的划分**确实**需要 hub 交换
  （已作为显式前提标出，且其合法性来自 (6,6) 的**度数相等**）✓。
- **类覆盖**：q1(5,7) 5 张证书覆盖 5 个类（含 3 个自固定/反射固定类）⇒ 8/8 start 覆盖 ✓；
  q1(6,6) 2 张证书覆盖 2 个类 ⇒ 8/8 start 覆盖 ✓。
- **上界严格性**：7 个 saved upper 的 **hi 端全部严格 < 3.14159 < π**（精确有理比较）✓，
  且与 start7 类的**独立精确分数控制**（3.141396）一致 ✓。
- **未做**：未重跑长内核、未重审 atan2、未验证区间内核、未改任何 lead 产物、未注册 claim ✓。
