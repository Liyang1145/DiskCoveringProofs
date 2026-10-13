# STATUS · upper-audit（next-cover-global / n14）

写域：`research-2026/next-cover-global/members/upper/**`。旧资产只读。任务：**有限复现 C411 上界 + 接口审读**（预算一次；**未启动搜索**）。

## 一句话

C411 上界 **精确复现**：14 心（`hprec_sol.json["th"]` 的 7 个字面量按精确有理数解释）的覆盖半径
`R(C) = sqrt(q0)`（argmax = 有理外心 circum{10,11,12}）**严格小于** `T = 0.33173203427623414`；
`sqrt(q0)` 的 70 位截断与保存的 `json["R"]`、C412 陈述值**逐位相同**。
**上界 ≠ 最优**：`R(C)` 是**这一条构型**的 R（上界对象），exact optimum ≤ `R(C)` 且很可能严格更小；**未做任何搜索**。

## 关键读数

| 项 | 读数 |
|---|---|
| 旧核复现（保真副本，仅改 SRC/OUT） | 与只读旧输出 `c407_lead_result.txt` **0 行差异**；候选 507、T/Tp 下 uncovered 0、argmax circum10,11,12 |
| 独立精确核（精确有理代数，无区间/无 float 判定） | 候选 **493 点**、**T 下 uncovered = 0**；控制层 4/4 PASS |
| 精确半径 | `p*` = circum{10,11,12} 有理；`q0 = R² ∈ Q`（argmin 心 10）；阈值 `sqrt(q0)` 下 uncovered = 0 ⇒ `R(C)=sqrt(q0)` |
| `sqrt(q0)` 70 位 | `0.3317320342762341235155066403893542386599009287817317893317705660612302`（= json R = C412 值） |
| 余量 | `T − R(C) ≈ 1.648e-17`；`L − R(C) ≈ 3.648e-17`；精确比较 `q0 < T²`、`q0 < L²` ✓ |
| 对象探针 | 用 float64 字段 `centers` 代替 `th`：T 下 **18 uncovered**、半径 **+2.326e-17** > 余量 ⇒ **证书不可转移** |
| L 的来历 | `R_float_recheck = 0.33173203427623416` 比 `R(C)` 高 3.648e-17（与 C412 一致） |
| 完备性 | 含补上的 `|A|=2` 排除；「盘心恰在原点」退化子情形经审读+实测（P 整圆/真弧/空三情形，均 PASS）⇒ **缺口断言已撤销** |
| 阈值用途（按 lead 修订） | **非锐分支排除继续用 U**；**尖锐 k10 须重新隔离优化方程的根**（`sqrt(q0)` 是上界对象，不能当锐利靶子）；先前“统一阈值”建议**已撤回** |
| 活动数归约 | k∈{10,11} 由 **C1142（proved，`CORE-COUNT-REDUCTION.md`）** 给出（先前误写 note pending，已改） |

## 最小承重问题（按 lead 口径修订）

**尖锐 k10 分支须重新隔离优化方程的根**（理想最优的精确根，而非 `sqrt(q0)`、也非 17 位 U），再在该根处排除
k∈{10,11}；上界侧已有紧的候选值 `R(C)`，两侧在同一精确根上会合才能把上界推成下界。
非锐分支的排除继续用 **U**。配套一个低成本接口项：下游配置来源统一用 `th`，**禁用** `centers` 字段（§5.2 已量化）。

## 改进上界对象复核（新增，2026-09-26 薄）

lead `improved-upper-test.json`（14 个**精确有理**心，`T = 1658660171381170613/5000000000000000000`）已用**两条通路**复现，
详见 `REPRO-improved-upper.md`：

* **旧 isqrt BOX 核**（`import` 只读旧核、只调 `analyse(C, T, grid=False)`，**未跑旧 `main()`**）：候选盒 **507、uncovered 0**、argmax `circum0,4,12` ⇒ `R(C) ≤ T`；
  运行前后 `lead/c407_lead_result.txt` sha256/mtime **未变**（旧域零写入）。
* **本成员独立精确核**（纯有理代数）：同 (C, T) **0 uncovered**；两通路一致。
* **精确比较**：`T² < q0_old` ✓；**`R_old − T = 9.155066e-19`**（与 lead "约9.15e-19" 一致）；`R_old − R_new = 9.576911e-19`；`T − R_new = 4.218445e-20 > 0`。
* 新对象精确半径 `R_new = 0.3317320342762341225578…`（argmax = 有理外心 `circum0,4,12`），与 lead numeric 逐位一致。
* 口径：**只是该有理构型的上界，不最优**；root 方程 / `root_scout.py` / `root-scout.json` 的数学原理**不在本件范围**（纯 given-centers），仅记录其 hash。

## 产物与 hash（全文见 `hashes.txt`，本版已按 lead 反馈重跑）

| 文件 | SHA256 |
|---|---|
| `REPRO-C411.md` | 见 `hashes.txt`（§5.3/§7 撤回统一阈值建议；§4 撤销原点缺口；§9 修订记录） |
| `REPRO-improved-upper.md` | 见 `hashes.txt` |
| `py/repro_improved_upper.py` | 见 `hashes.txt` |
| `py/repro_c411_independent.py` | 见 `hashes.txt`（含第 3 层：原点退化三例审读） |
| `py/repro_c407_lead_localcopy.py` | `0B52DB77A8A26CE875742EDE67DAFC64…` |
| `py/make_localcopy.py` | `116F4794202E5D984B4EE6A1B2CA205C…` |
| `py/probe_argmax.py` / `py/probe_exact_values.py` | `F9F92D99…` / `9BECB02A…` |
| `logs/c407_lead_result_localcopy.txt` | `7E8FF18129C9C32CD28021955AD25983…` |
| `logs/independent_c411_result.txt` | 见 `hashes.txt`（含第 3 层） |

## 复现

```powershell
cd research-2026/next-cover-global/members/upper
py -3 -B py/repro_c407_lead_localcopy.py     # 旧核复现（0 行差异）
py -3 -B py/repro_c411_independent.py        # 独立精确核 + 对象探针 + 原点退化审读
```

## 未决

* 尖锐 k10 的优化方程根**未**隔离（主线下一步；本成员只做上界复现与接口审读）。
* `centers` 字段误用风险已量化，但**未**整改任何旧产物（只读）。
