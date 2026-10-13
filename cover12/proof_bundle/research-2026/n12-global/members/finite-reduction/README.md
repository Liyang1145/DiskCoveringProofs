# members/finite-reduction — 交付索引与状态

任务（Lead 派单）：**独立证明或明确反例**——对任意非空有限 $C\subseteq D$（允许重复中心与原点），
$f_C(x)=\min_i|x-c_i|$ 的最大点可由有限候选集取得：固定 $(1,0)$、非零中心的反径点、每对不同中心的中垂线与单位圆交点、每个非共线三元组位于 $D$ 内的外心；重点退化：原点唯一最近心形成平台、重复、共线、边界相切；并给出**无分母多项式有限判据**（供量词消元/后续完备分类）。
写域：仅本目录；未改 STATUS/claims/DEAD，未改旧证据。

## 交付物

| 文件 | 内容 | 等级 |
|---|---|---|
| [`PROOF-finite-reduction.md`](PROOF-finite-reduction.md) | 主定理 $R(C)=\max_{x\in K(C)}f_C(x)$ 及加强版（每个局部最大点的值在 $K$ 上取到）；引理 L1–L5；分情形证明；退化清单 7 项；四类候选不可省性；两个等价表述（Voronoi 裁剪单元+凸性；抛物面提升/线性化）；接口与范围 | **证明（解析，全称）**：scope = 所有非空有限 $C\subseteq D$，无一般位置/互异/接触图假设 |
| [`QE-interface.md`](QE-interface.md) | 无分母、**量词自由**判据：$A\wedge\bigwedge B_i\wedge\bigwedge C_{ij}\wedge\bigwedge D_{ijk}$；§3 消根（$a+b\sqrt s\le0$ 精确符号-平方分支）+ $D$ 的 $x=v/(2\Delta)$ 代入；退化 guard 诚实清单（哪些承重）；§5 解析自检 + 精确实现校准 | **证明（等价性，引用主定理）** |
| [`NUMERICS.md`](NUMERICS.md) | 223 例 battery + 28 例 sandwich + 29 构型/305 决定性探针接口校准 + **精确有理检查器**（11 已知答案对照 0 不一致、8/8 域自检；C182 为 instance 行、非对照；二分包围宽 $2.2\times10^{-18}$，已冻结不再加深）；器械边界；C182 只读诊断 | 仅校准（非证明） |
| [`CHECK-one-third.md`](CHECK-one-third.md) | 复核 `lead/ONE-THIRD-LOWER-BOUND.md`（$r_D(12)>1/3$）：逐步清单、承重小步、C925 必要性与两条写法建议；已据此对 C927 追加 `claim_review`(reviewed) 事件 | 复核记录（解析，非形式化） |
| [`CHECK-no-chords.md`](CHECK-no-chords.md) | 复核 `lead/NINE-BOUNDARY-OWNERSHIP.md` + `lead/NINE-RING-NO-CHORDS.md`（k9）：**通过**；四个更紧组合论证（端点序=中点序、三弧不共点、非邻不重叠+见证点、$J$ 内 $\ge3$ 弧）；常量链 14/14 精确有理；割线遗漏专项检查（未发现） | 复核记录（解析，非形式化） |
| `py/candlib.py` | 候选构造、$R_{\rm cand}$、参考最大化、分类、两边界检查 | 实现 |
| `py/exact_checker.py` | **精确有理、无浮点/无区间**的判据检查器（含精确二分；域不变式自检 8/8；越域即 raise、失败即非零 exit） | 实现 |
| `py/run_battery.py`, `py/sandwich_check.py`, `py/qe_interface_check.py`, `py/exact_vs_float_check.py`, `py/no_chords_constants.py` | 复现脚本（证据在 `evidence/`，含 SHA256 前缀） | 实现 |
| [`taylor-audit/`](taylor-audit/) | 独立复核 60 个 k9 witness-network Taylor 证书（另一条实现：精确 Fraction Schur 两路径 + 精确 LDL + 二进制定点 trig）与 `graphs.json` 56 类型**穷举完备性**（56↔56 一一对应）；见 [`taylor-audit/REPORT.md`](taylor-audit/REPORT.md) | 复核记录（解析+实现，非认证） |
| [`coverage-audit/`](coverage-audit/) | 独立复核 Lead 的 ideal-coverage 证明（边界弧 $F/G/H$ 恒等式、13 面＝333 重标号、有向链=环边界、7 slack 面 $R<r$ 用**不同公式** $abc/4K$、6 active 面见证、公共见证方差恒等式、壳外射线单调），32/32 通过；见 [`coverage-audit/REPORT.md`](coverage-audit/REPORT.md) | 复核记录（解析+精确区间，非认证） |
| [`onehub-audit/`](onehub-audit/) | k11 双圆容量证书：**自写核**（精确 Fraction；Machin π；halving+交错级数 sin/cos + 临界点包络；asin/acos 全正级数+显式正项尾界）**独立 12/12 段 box-cover 全 accepted**（margin 9.7e−7…3.3e−5）；nearmerge δ=1/20 的 **changed β 域**独立推导+暴力几何复核（cap 测度=2β；inner 分支不可能；ℓ≥R+U⟺β=0；$q_b$ 非单调）；nearmerge 为**源/推理+记录**独立审、非完整 replay；见 [`onehub-audit/REPORT.md`](onehub-audit/REPORT.md) | 复核记录（解析+精确区间，非认证） |
| [`integer-domain/`](integer-domain/) | 全 hub manifest（stage2200）独立复核器：**独立 recursive tiling** 精确 partition（visited==frontier，非体积论证）＋76 非法叶逐条复现＋prune3 精确 isqrt 对照 13/13＋**atomic 叶 1021/1021 全 certified**＋四源 hash 绑定 resume；口径 `complete-for-snapshot(partial frontier)`、`global_certificate=false`；见 [`integer-domain/REPORT.md`](integer-domain/REPORT.md) | 复核记录（整数域独立重放，非认证） |

## 结论摘要（本成员的回答）

1. **命题成立，未找到反例**：主定理与四类候选的完备性已解析证明（无分母、无一般位置假设）。四类**都不可省**（§4 表：$(a)$ 全零中心；$(b)$ 单中心；$(c)$ 两中心；$(d)$ 正十二边形 $\rho=1$）。
2. **退化全部落地**：重复（按不同位置定义 $K$，$\Delta\ne0$ 自动排除）、共线（$\Delta=0$ 无外心；且三点等距自动非共线，故共线三元组不可能是内点最大点来源）、边界相切（**中垂线那半不可能发生**：不同位置的中垂线必过圆内点，与圆恰交两点；真正相切的是最近心的等距圆 $\partial B(c,R)$ 与 $\partial D$ 于最大点相切 $\iff$ 反径点）、原点平台（平台分量端点与原点及某非零中心 tie 于距离 1，落入 $K_c$；全圆平台 $\iff$ 全中心在原点，此时只有固定点 $(1,0)$ 可用——这是 $(a)$ 类唯一的必需场景）。
3. **$K_d$ 的 $\|x\|\le1$ 过滤是承重的**：它保证 $K\subseteq D$ 从而 $R_{\rm cand}\le R$（等价性的一个方向）；去掉后未过滤读数可达 $1546.6$（C182 的近共线三元组），判据只剩充分方向。$K_d$ 含大量**非 Voronoi 顶点**的圆外心（该超集是刻意的：避免单元归属测试）。
4. **接口**：判据是有限合取，无定义域量词；所有数据项是 $c,\rho=r^2$ 的多项式，平方根由内层辅助变量 $t_i,\nu,w$ 的等式承担；$n=12$ 互异位置时：1 项 $(a)$ + 12 项 $(b)$ + 66 项 $(c)$（132 点）+ 220 项 $(d)$，对应旧 D2 装置的 364 候选点，另加固定点 $(1,0)$。**已数值校准**：多项式接口与几何候选判据（两种表示）在 29 构型、305 个决定性探针上**零不一致**（$\lvert r-R_{\rm cand}\rvert>10^{-9}$；等号边界带 14 例按浮点舍入单独记录）。
5. **审计记录**：v1 经 Lead 审计指出 6 处（L2' $w$ 定义文字、L3(ii) 数值与推理方向、L3(i) $w=0$、§6 提升读法、基数、$D$ 外点的"sound"措辞）；v2 已全部修正并精简。另：本成员在写接口时自查出 $(b)$ 项须为**析取**（$\exists j$）而非合取，已在 `QE-interface.md` §1/§5 修正并留自检例。

## 缺口与边界（不假装完成）

- 本判据**不**给出 $r_D(12)$，**不**排除任何 $r<r_D(12)$：全局仍需"对所有中心位置"的量词消元/分层排除。
- 中心允许在 $D$ 外时 L2 与 L5 第 3 步需重证（本稿只按 $C\subseteq D$；任意中心可先径向投影，见 `lead/FOUNDATIONS.md` §1，该步代数已核对）。
- 无数值上的**认证级**等号（sandwich 上界仅 $\approx7\times10^{-4}$ 宽）；**无独立子代理数值复核**（本环境 `subagent` 路由两次报 `no adapter registered for provider "tokenrhythm2"`、一次报 `subagent depth 2 exceeds maxDepth 1`），故所有"无违例"读数只是同作者双器械证据；本目录内的独立审阅仅 Lead 的人工审计（v1→v2 修正 6 处）。

## 只读接口观察（不作裁决）

旧 D2 装置 `research-2026/session2/n1314/py/cert_cand.py` 的候选族 = (b)(c)(d)，`__main__` 断言中心互异；其算术结构 $12+2\binom{12}2+\binom{12}3=12+132+220=364$ 与旧输出 `cover_n_cand=364` 一致。旧 `cover_n_uncovered=36` 与 REPORT 的 $0/328$ 的口径差异仍以旧脚本自身语义为准，本目录仅记录、不改任何旧 claim。本接口补齐的结构缺口正是：$(a)$ 固定点/原点平台、重复中心、共线三元组、$\|x\|\le1$ 过滤的形式化。

## 下一可执行动作

1. ~~把判据实现为精确认证检查器~~ **已完成**：`py/exact_checker.py`（全 `Fraction`，无浮点/无区间；13/13 校准；C182 在登记 $U$ 处判真；精确二分给 $R$ 的有理包围，宽 $2.2\times10^{-18}$，$U$ 落在包围内）。
2. 若上层要全局分类：以 `PROOF` §2 的四类最大点类型（等距/切向/外心/平台）为分层变量，对每层写紧性条件后做 QE 或区间排除；$\mathrm{Cover}$ 现已是（对 $c,\rho$ 的）半代数条件。
3. 独立复核：本环境子代理路由不可用（两次 provider 未注册、一次深度超限），精确检查器仍属同作者实现；如上层能派独立成员，建议用另写实现复跑 13 个校准例 + C182 两点（$lo$ 判假 / $U$ 判真）。
