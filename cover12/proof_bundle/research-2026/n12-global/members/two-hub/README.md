# members/two-hub — n12 k=10 分支：交付索引与状态

写域：仅本目录（`research-2026/n12-global/members/two-hub/`）。未改 lead/shared STATUS/DEAD、未改旧 n11。
路由：cline2 / cline-pass/deepseek-v4.1-flash。本成员 = 单 agent，数学独立性由不同推理（解析审计 + 两套独立积分器 + 有限候选与网格/模式搜索互校）提供，不是由 agent 身份提供。

## 交付物

| 文件 | 内容 | 等级 |
|---|---|---|
| [`AUDIT-2HUB-CORE.md`](AUDIT-2HUB-CORE.md) | 审 `lead/TWO-HUB-CORE-REDUCTION.md` + `CORE-HUB-DOMAIN.md`（m=2 部分）：边界充分性证明、角度刻画、两弧判据、whole-core 分支；指出 3 处需写清之处（closedness/density、域定义须含 whole-core 情形、a<r 需 r>1/3） | **解析审计**（结论：引理正确，无数学错误） |
| [`REDUCTION.md`](REDUCTION.md) | k=10 覆盖（r≤U）→ 固定半径 U 的 exact-k′ 归约（enlarge + reclassify，Lead 方案），以及本分支要排除的精确类 (R_U) | **证明（解析，全称）** |
| [`K10-NUMERICS.md`](K10-NUMERICS.md) | k=10 族最优覆盖半径的数值测定（含器械校准/正负控制/一个已修 implement 错误）；k=10 临界半径 ≈0.3725 vs U=0.36110 | 数值（诊断，不认证） |
| [`DUAL.md`](DUAL.md) | **coupled contribution 精确定义** + LP 对偶设计 + 修正核后的全域扫描 + 连续局部最大值验证 + 独立角积分对照 + 一个有理对偶 | 数值/设计（**未认证**：待 interval 核） |
| [`AVERAGE-TRICK.md`](AVERAGE-TRICK.md) | 单圆容量比下界恒等式（证明）：任何非负权必有半角 h 的弧捕获 ≥ (2h/2π)∫W；⇒ 单圆峰谷整形无益，增益只能来自两圆耦合 | **证明（解析）** |
| `py/` | `k10_feas.py`(搜索+候选判据) `run_search.py` `regime_probe.py` `analyze_extremal.py` `radial_capacity.py` `dual_lp.py`(旧核，obsolete) `dual_scan.py`(旧) `dual_refine.py` `scan_clipD.py` `dual2.py`(**修正核**) `verify_fixed.py` `scan_fine.py` | 实现 |
| `evidence/` | 上述运行的全部 JSON/日志（含 `sweep1.log`、`dual_fine_scan.json`、`rational_dual_worst.json`、`quad_calibration.json`） | 证据 |

## 当前结论（一句话）

1. **k=10 归约为固定半径 U 的 exact-k′ 类**（解析，C942）：任意 r≤U 的 exact-10 覆盖放大到 U 后 active count k′∈{10,11}；排除"U 处 exact k′=10"（本分支）配合 k′=11 theorem 即排除全部 r≤U 的 k=10。在 U 处 inactive ⟺ `|h|<1-U` 严格，故两 hub 圆盘含于 int D，无需 D-裁剪；hub 域 = `t_j<1-U` 且（`t_j≤3U-1` 或 `β_1+β_2≥2π-δ`）。
2. **联合对偶在 hub 域采样上存在**（数值，C956）：耦合贡献 `cap(ρ,φ)=∫_{A_0}W_0+∫_{E_1∩A_1}W_1+∫_{E_2∩A_2}W_2`，需求 `req=∫_{S^1}W_0+∫_{E_1}W_1+∫_{E_2}W_2`；406 个采样 hub 配置上 LP 全部 `10·m*<req`；最坏若干处局部搜索给出 `10·cap_local/req ≤ 0.976`。**这只是浮点读数**（LP 约束在有限 ring 网格上，局部搜索不等于连续 sup）。
3. **一个固定 hub 配置上的 ring 连续域 interval 认证已完成**（最新 id **C997**，proved-interval；修订 SHA256 前缀 ADE005B1E0198462 = 受 upper-audit 纸面审计的 ψ 链 + Lead 指出的两处承重界定向化）：`t_1=t_2=1/5, δ=604457/200000`，284008 盒/213106 叶/**未解 0**，最坏叶上界 0.09995363239854560134043966480160594324602 < 阈值 0.1000036354670063507361525306725503902877（比例 0.9994999874931822190305236565348049283176 < 1）；点态 1000 点（vs dual2）+ 40 点（vs 逐点隶属暴力积分）0 违反；阈值×24/25 控制报 12229 未解。历史：C953（padding 版）与 C966（漏 hE）已撤回，C959/C991/C992 已被取代（见 claim 台账）。**仍未覆盖 hub 域全族（0<d<2U）与 d=0**；独立复算在 upper-audit 侧仍未回。
3c. hline LP proposals (numeric, PROPOSALS ONLY): evidence/hubline_proposals_v2.json -- only the SAMPLED legal points have a proposal (never phrase as every legal point has a weight); its joint entries only assert shared weights on that layer sample set, NOT a layer proof; no domain deletion may rest on it.
3b. **hline LP 粗探测（proposals only）已作废**：`evidence/hubline_lp_probe.json` 因漏掉 chart 的 core 合法性条件被标 `INVALID`，其结构结论（worst 位置、单权覆盖、whole-core 更容易）全部撤回；改正后的合法域见该文件 `INVALID` 字段与发给 lead 的更正消息。
4. **单圆角度整形定理上无益**（解析，C954）：对任意非负权必有半角 h 的弧捕获 ≥ (2h/2π)∫W；∂D 上 h≤asin U，份额下界 asin(U)/π 的区间读出下端 = 0.117599712548224301647212331707970592692723912 > 0.1。（旧稿 asin U 写作 .369795 有误；正确区间 [0.3694503930057728895570312301296049412148, 0.3694503930057728895570312301297528526346]。）
5. **k=10 族的数值读数**（C955，仅上界方向）：r=0.38/0.40/0.45 存在 `R_cand<r` 的构型（需有限归约定理+严格算术才是认证覆盖）；由 `R_10 ≤ 0.372499` 只能得 `R_10 − U ≤ +0.011396`。**不**声称临界半径位置或任何下界间距。

## 未决（不属于本目录可声明完成）
- 上述 `10·cap < req` 在连续域 (t1,t2,δ,ρ,φ) 上的 **interval 认证**（含 d=0 merged hub 的单独处理与边界 t_j→1−U）。
- k′=11 at U 的排除（其他 member）；本分支不重复。
- 本分支**不**给出 r_D(12) 的锐界；也不声称 k=9 的下界。
