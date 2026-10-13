# (更正稿) 全树 field 证据审计：`lead/cosine_dbm_local919.json`

> 写作用域：**只**本文件 + 自有 `field_archive_audit.py`（已更正 ✓）。**不再扩审计** ✗——完整 Schur 重算由 lead 的
> `lead/replay_all_fields.py`（**371 fields** 完整重算，job35 ✓）承担；本件**不重复** ✓。未改 lead 文件 ✓。

## §0 撤回（lead 指正；**我上一版的权重检查作废** ✗）

| 我写的（错 ✗） | 真实（源级 ✓） |
|---|---|
| `weights` 条目是 `[lo, hi, rational]` | **`(i, j, w)`**：两个**索引** + 一个**精确权重** ✓ |
| `Σ lo(weights) = 84` 有意义 | 那只是**索引和**，**无意义** ✗ |
| 321 field 是 BnB 树的 **certified 叶** | field 是 **stress**（不是 leaf）✗ |
| Schur 消去 **15** 个内部变量 | **free = 22**（不是 15 ✗） |

**源级证据**（按 lead 要求"读源码而非猜测" ✓）：
* `lead/certify_energy_cell.py`：`schur(raw,name)` 内 `alpha=[sp.Rational(x,S) …]`、`assert sum(alpha)==1 and min(alpha)>0` ✓；
  由 `edges` + `alpha` 组装加权 Laplacian（`LL[v,v]+=a; LL[w,w]+=a; LL[v,w]-=a; LL[w,v]-=a` ✓）；
  随后 `w=F(-M[i,j]); assert w>=0; weights.append((i,j,w))` ✓ ⟹ **`weights = (i,j,w)` 三元组** ✓
  （`i,j` = 保留/free 坐标索引、`w` = 精确 Schur 权重 ✓）。
* `lead/multifield_simplex_pilot.py`：`from simplex_tree_pilot import *` ✓ 且
  `assert [tuple(e) for e in cert['edges']]==edges`（对 `uniform_sector_certificate.json` ✓）⟹ edges 的权威来源 ✓。

## §1 仍然有效的部分（**alpha 检查**；全部 321 field，精确有理）

| 检查 | 结果 |
|---|---|
| `alpha` 长度 = 51 | 违例 **0** ✓ |
| `alpha` 全为**正** | 违例 **0** ✓ |
| `alpha` **精确归一化** `Σ = 1` | 违例 **0** ✓；`max|Σ−1| = 0`（精确 ✓） |

⟹ 与 `certify_energy_cell.py` 的 `assert sum(alpha)==1 and min(alpha)>0` **独立一致** ✓；α 与 weights 的一致性由 §2 的重算承担 ✓（本件不重复 ✗）。

## §2 权重检查：**已作废并让位** ✗（不重复）

我上一版对 weights 的"非负性/和"读数**作废** ✗（schema 读错 ✗）。更正后的 script 已按 `(i,j,w)` 解析 ✓；
但**完整 Schur 重算由 lead 的 `replay_all_fields.py`（371 fields，job35 ✓）承担** ⟹ 本件**不做** 51→36 独立 Schur ✗、
也不做 321×2 逐标签反射映射 ✗（按 lead："不再扩审计" ✓）。

## §3 命名层面观察（**只**作观察，不作推断）

命名含 `reflect` 的 field 共 **74** 个 ✓（`C911-reflected`、`corner0-reflected`… ✓）；首/末 = `C911`(0)、`dbm_local9194414`(320) ✓。
三者（`C911`、`C911-reflected`、`dbm_local9194414`）的 `alpha` 均为正且 `Σ=1`（精确 ✓）；`(i,j,w)` 的 `w` 均可解析 ✓
（更正后 script 的 `weights_nonneg=True`，`w_min = 0` ✓——即存在**恰为 0** 的 Schur 权重 ✓，属正常结构 ✓）。

## §4 结论 / 不声称

* **可断言** ✓：全部 321 field 的 `alpha`（51）正且精确归一化（独立复核 ✓）。
* **已撤回** ✗：weights 的 schema 读法、由其得出的 `sumlo=84`、以及 "leaf"/"15 free" ✓。
* **不声称 / 不重复**：不独立重算权重一致性（lead 已覆盖 371 fields ✓）；不注册 claim、不改 lead 文件、无子 agent ✓。

> 证据：`out/field_archive_audit.json`。口径：**对存档证据做精确有理检查**，不重证任何局部 claim ✓。

---

## §0 存档结构（实测）

* 顶层 4 键：`summary`（含 `counts: {split: 2461, certified: 2333, open: 129}`、`field_count: 321`）、`proposals`、`fields`、`nodes` ✓。
* `fields` = 321 个 dict，各含 `name` + `alpha`（**51** 项）+ `weights`（**36** 项）✓；
  `weights` 项是**区间型** `[lo, hi, 'rational']` ✓（故按 lo/hi 做符号判定 ✓）。
* `nodes` = 4923 个 dict，键 `id, db, status, depth, numeric_lower, pair, midpoint, children` ✓
  ⟹ 这是**分支定界树**（`db` = box 描述、`children` = 子节点 ✓），321 个 field 是其中的**叶**（certified fields ✓）。

---

## §1 批量精确检查（**全部 321 个 field**）

| 检查 | 结果 |
|---|---|
| `alpha` 长度 = 51 | 违例 **0** ✓ |
| `alpha` 全为**正**（有理） | 违例 **0** ✓ |
| `alpha` **归一化** `Σ = 1` | 违例 **0** ✓；`max|Σ−1| = 0`（**精确**，非近似 ✓） |
| `weights` 长度 = 36 | 违例 **0** ✓ |
| `weights` **非负**（按区间下界 `lo ≥ 0`） | 违例 **0** ✓ |

⟹ "每 field 51 个正的归一化 alpha + 36 个非负 weight"在**全部 321 个叶**上成立 ✓（精确有理 ✓）。

---

## §2 反射标签证据（**主检查项之一**）

* field 名里含 `reflect` 的有 **74** 个 ✓（例：`C911-reflected`、`corner0-reflected`、`corner1-reflected`、`corner2-reflected`、`corner3-reflected` ✓）。
* 首/末 field：`C911`（idx 0）与 `dbm_local9194414`（idx 320）✓。
* 与既有约定的一致性（本目录 `ORACLE-SYMMETRY-REDUCTION.md` v2 已证）：label 变换 `raw k → canonical (k−2) mod 9` ✓，
  反射 `ρ(i) = 4−i`（mod 9；`U_k ↦ U_{3−k}`、forward `Δ_i ↦ Δ_{2−i}` ⟹ `y_i ↦ y_{2−i}` ✓）。
  **本审计只核对"命名层面"的成对出现**（74 个 `-reflected` 与对应本体成对 ✓），**未**逐一核对 321×2 个标签置换 ✗
  （那需要 321 次标签映射比对 ✓——可按 §3 的同一 script 扩展，廉价 ✓）。

---

## §3 选定 field 的检查（首 / 末 / 反射）与**未完成项**

选定：`C911`(0)、`C911-reflected`(74)、`dbm_local9194414`(320) ✓。三者均：
`alpha_pos = True` ✓、`Σalpha = 1`（精确 ✓）、`weights_nonneg = True` ✓、`Σ lo(weights) = 84`（三者相同 ✓——观察值 ✓）。

**未完成（诚实标注）✗**：按 alpha 的**独立精确 Schur 重建**（51 alpha → 36 weights）**本轮未做** ✗。
原因：该消元需要该 field 的**系统数据**（incidence/几何），它们**不在 `fields` 条目里** ✗——`fields` 只存
`name/alpha/weights` ✓；`nodes` 只存 BnB 的 `db/midpoint/children` 等 ✓。要把 51→36 的 Schur 消元**独立**重做，
需要二者之一（**接口请求，不是新证明义务**）：
1. 读出其内部构造（`lead/` 里生成这些 field 的脚本的 field-system 构造 ✓）；或
2. field 条目附带其 incidence/几何块（或指向 `db` 的具体语义 ✓）。

**已就绪**：`field_archive_audit.py` 已把 §1/§2/§3 的检查全部自动化 ✓；补上系统数据后，同一 script 加一段
"`M = 51×51` 分块 → Schur 消去 15 个内部变量 → 得 36 weights → 与存档 `weights` 逐项精确比较"即可 ✓（**仍只对
证据做精确检查，不重证局部 claim** ✓）。

---

## §4 结论（本轮可断言的与不可断言的）

* **可断言** ✓：全部 321 个 field 的 `alpha`（51）**正且精确归一化**；`weights`（36）**非负**；74 个 `-reflected` 命名成对存在；
  三个选定 field 的上述性质成立且 `Σlo(weights)` 一致（=84 ✓）。
* **不可断言** ✗：36 个 weights 与 51 个 alpha 的**独立 Schur 一致性**（本轮未做 ✗，原因见 §3）；
  321×2 的**逐标签**反射置换正确性（只做了命名层面的存在性 ✓）。
* **不声称**：不重证局部 claim、不注册 claim、不改 lead 文件 ✓；无子 agent ✓。
