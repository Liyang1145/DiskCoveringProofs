# C920 输入精确性审计（**v2：按 lead 指定的两项检查**）

> 写作用域：**只**本文件 + `c920_input_exactness_audit.py` / `c920_input_exactness_audit_v2.py`
> （**不 import 任何 lead 模块**，只读文件 + 独立 mpmath ✓）。未碰 ear/topology ✗。
> 证据：`out/c920_input_exactness_audit.json`、`out/c920_input_exactness_audit_v2.json`。
> **v1 的目标读错已更正** ✗：`iv` 检查**不是** JSON decimal 诊断 ✓，而是下面的 A ✓。

## §1 A：`iv` singleton + **精确接收 binary64**（`iv.dps = 50`）——**全部通过** ✓✓

对 `kernel_basis_diagnostic.json[0]['R']` 的 16 个 binary64（`R` = 4×4 ✓）：
```
v = iv.mpf(x) ; check v._mpi_[0] == v._mpi_[1]        # singleton（零宽区间）
还原 value = sign · man · 2^exp                        # mpmath mpf tuple = (sign, man, exp, bc)
check Fraction(value) == Fraction(x)
```
**读数：16 个 float；singleton 16/16 ✓；`Fraction(tuple) == Fraction(x)` 16/16 ✓✓。**
（**关键口径**：mpmath 的 mpf 值是 **`man·2^exp`** ✓——初版按 `man·2^(exp−bc)` 还原得 0/16 ✗；实测
`x = 0.1…` 的 tuple `(0, 8895999183877727, −56, 53)` 满足 `8895999183877727·2^-56 == Fraction(x)` ✓。）
⟹ `iv` 在 dps=50 下对每个 binary64 给出 singleton，且其 `(sign, mantissa, exp, bits)` 精确还原原值 ✓。

## §2 A′：`R` 与证书 hex **逐项精确一致** ✓（v1 已完成部分，保留）

`kernel_basis_diagnostic.json[0]['R']`（16 项）与 `relative_stress_ball_certificate.json` 的 **16** 个 hex 条目**逐项精确相等** ✓
（`n_compared = 16`、`first_mismatch = null` ✓），两侧均为**精确 dyadic** ✓（例：首项同为
`5188705913975425/1152921504606846976 = k/2^60` ✓）⟹ basis 输入与证书 hex 同源、**输入层面不含 whitening 依赖** ✓。

## §3 B：carrying edges（45）vs canonical（51）——**face 层通过 ✓ / edge 层待补 ✗**

**源（非 JSON ✓，显式复制 ✓，未 import）**：
* raw：`interval_network_envelope.py` **L21** `F=[[2,9,10],[6,9,10]]+[[k,(k+1)%9, 9 if 2≤k≤5 else 10] for k in [1,2,3,4,5,6,8]]` ✓；
  **L28–30** `edges`：`for k in 0..8: (9+k,k),(9+(k+1)%9,k)`，再 `(9+s,20+j) for s in f` ✓ ⟹ 边数 `18 + 9·3 = 45` ✓✓（与"45 carrying"相符 ✓）。
* canonical：`simplex_tree_pilot.py` **L11** `faces=[[9,k,k+1] k<4]+[[10,k,(k+1)%9] 4≤k<9]+[[9,10,0],[9,10,4]]` ✓（**11 面** ✓，
  中心 ring = **0,4** ✓ 与 canonical 约定一致 ✓）；**L12** `edges = [(9+s,s),(9+s,(s−1)%9) for s<9] + [(9+s,20+j) …]` ✓（**51 边** ✓）。

**已通过（face 层，按 lead 的 sorted site triples 匹配 ✓）**：raw 的 9 个面按 `raw k → can (k−2) mod 9`（hubs 不变 ✓）映射后
**全部落在 canonical 的 11 面内** ✓（`rawF_mapped_all_in_canF = True` ✓；例 raw `[2,9,10] → [0,9,10]` = canonical `(9,10,0)` ✓）。

**待补（edge 层）已补完 ✓✓（见下）**：直接比较 45 条边曾只命中 11/45 ✗，原因是 raw 侧节点编号被误解 ✗；
读源码前 30 行后确定**两文件同一布局** `X = U + C + Z` ⟹ **tie k ↦ 节点 k（0..8）**、**site s ↦ 节点 9+s**（`C` = 9 ring + 2 hub ✓）、**aux j ↦ 20+j** ✓。
**真实映射字典**：
```
ties  k(0..8) -> (k-2) mod 9                    # raw ring k -> can (k-2) mod 9
sites s(0..8) -> (s-2) mod 9 ; hubs 9,10 fixed
aux  20+j     -> {20:29, 21:30, 22:28, 23:20, 24:21, 25:22, 26:23, 27:24, 28:26}
                 （由"映射后的面"在 canonical 面表中的位置决定，按 sorted site triples 匹配 ✓）
```
**读数 ✓✓**：raw **45** 条边（distinct 45 ✓）映射后 **45/45 全部落在 canonical 的 51 条边内** ✓
（`rawE_mapped_all_in_canE = True` ✓）。
**差集（canonical ∖ 映射像，恰 6 条 ✓）**：
```
[[14,25],[15,25],[16,27],[17,27],[19,25],[19,27]]
  = site5–aux25, site6–aux25, site7–aux27, site8–aux27, hub10–aux25, hub10–aux27
```
⟹ 差集**恰为两个 canonical 面的各 3 条边** ✓ = `faces[5] = (10,5,6)` 与 `faces[7] = (10,7,8)` ✓ ⟹ 即**两个 slack 面**
（与 C909/C915 的"6 条零力 slack 边"一致 ✓；其零力性质属那两件，本件不重证 ✗）✓✓。
**修法**：先读该文件 L1–L27 的节点编号（`C/Z/U` 顺序 ✓）确定 raw 的 hub/anchor/aux 标签 ✓，再按面匹配重做边映射 ✓（同样只读、不 import ✓）。

## §4 口径 / 不声称

* A ✓ 与 A′ ✓ **已建立**（精确 ✓）；B 的 **face 层 ✓ 已建立**，**edge 层未建立** ✗（不得引用为通过 ✗）。
* 不注册 claim、不改 lead 文件、不 import lead 模块（避免其写盘 ✓）、不碰 ear/topology ✓、无子 agent ✓。
> 数据：`lead/kernel_basis_diagnostic.json`（**17 项** list，每项含 `name,tau0,mu,B,A,rho_numeric,positivity,R` ✓，
> 第一项 `name='relative'` ✓）、`lead/relative_stress_ball_certificate.json`（`scope/constants/diagnostics` ✓）。

---

## §1 已完成且为真的检查（**逐项一致 + 精确 dyadic**）✓

* `kernel_basis_diagnostic.json[0]['R']` 展开为 **16 个条目** ✓（`R` 是 4×4 ✓ ⟹ 16 ✓）；
  `relative_stress_ball_certificate.json` 内可解析的 **hex 条目 16 个** ✓。
* **逐项一致 = TRUE** ✓：`n_compared = 16`、`first_mismatch = null` ✓。
* **两侧都是精确 dyadic 有理数** ✓：`R_all_exact_rational = true`、`cert_hex_all_exact_dyadic = true` ✓；
  例如首项两侧同为 `5188705913975425/1152921504606846976` ✓（= `k/2^60` ✓）。
  ⟹ **C920 的 basis 输入与 `relative_stress_ball_certificate` 的 hex 在 16 个条目上逐项精确相等** ✓——
  即"**不依赖 whitening**"这一点在**输入层面**得到支持 ✓（该 basis 的 `R` 与证书 hex 同源 ✓）。

---

## §2 未完成的检查（**诚实标注** ✗；原因与修法）

1. **"iv50 decimal 精确接收每个 binary64"（singleton rational 检查）** —— **未完成** ✗。
   脚本给出的 `decimal_receives_hex_exactly_all = false` ✗ **不是**结论：它是我的**配对启发式**（按
   JSON 路径的父节点配对 hex 与 decimal ✓）失配造成的 ✗——证书里可解析的 decimal 只有 **5** 个 ✓，
   而 hex 有 **16** 个 ✓ ⟹ 二者**不是同长度的兄弟对** ✗，我的"兄弟配对"假设不成立 ✗。
   **正确做法**：把证书里 5 个 decimal 的**实际路径**（应为 `constants/diagnostics` 下的标量 ✓）与 R 的
   16 个条目分开处理；对每个 hex 单独做 `Fraction(float.fromhex(h)) == Fraction(对应 decimal 字符串)` ✓。
2. **active edges → canonical 的图映射 + 45 ⊂ 51 检查** —— **未完成** ✗：两个 JSON 里的**边表未被我的模式识别到**
   （`kd_edge_lists = []`、`cert_edge_lists = []` ✓）⟹ 边表**不在**（或不是）"由 2–3 个整数构成的 list"这一形状 ✗。
   **正确做法**：先把两文件的边表**实际 schema** 打印出来（键名/嵌套 ✓），再按 `raw k → can (k−2) mod 9`
   （hubs 不变 ✓）做映射，比较 `|canonical(raw active)| = 45` ✓ 且为 51-edge canonical 集的**子集** ✓。

---

## §3 口径 / 不声称

* 本件**不**再碰 ear/topology ✗；**不** import 任何 lead 模块 ✗（避免其写盘副作用 ✓）；只读文件 + 独立小脚本 ✓。
* §1 的结论 = **16 项逐项精确相等**（exact dyadic ✓），**足以**支持"basis 输入不含 whitening 依赖"这一**输入层**判断 ✓；
  但**不**声称 C920 的整体正确性 ✗（那属其证明本身 ✓）。
* §2 的两项**未完成** ✗，不得引用为"通过" ✗；不注册 claim、不改 lead 文件、无子 agent ✓。
