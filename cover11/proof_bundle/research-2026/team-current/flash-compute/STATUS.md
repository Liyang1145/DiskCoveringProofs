# flash-compute STATUS — 可分离重计算 / 工具诊断（写域：`research-2026/team-current/flash-compute/`）

> 角色：独立可分离计算与器械诊断；不改根台账/根 DEAD；不注册未审 `proved`。
> 时间：2026-09-24（本轮）。所有数字均为 **numeric 探索**（除标注 exact 者），未认证。

## 0. 首报（≤12 行）

1. **义务 A（已完成）— 两个校准**：(A1) 钝角三角形 MEC ≠ 外接半径：exact 控制 `(0,0),(4,0),(1,1)` → MEC=2 而外接半径=√5=2.2360（差 +0.2361），`(0,0),(4,0),(3,1/2)` 差 +1.4004；正确三点规则 = `max(最长边/2, 外接半径 iff 锐角)`。
2. (A2) `r=.38` 保存可行对象**不能被排除**：`n11/upper/certified_object.json`（sha256 `15a127b2045d90288274bb07dbeae016…`，R_saved=0.3799838531198387090485182 ≤ 0.38）实测为 **9 边界盘 + 2 内盘**（|c|=0.1494/0.2730）；在 r=38/100 处对角配对判据 **失败**（min |v_i−v_{i+4}| = 0.757045 < 2r = 0.76）⇒ 该对象未被排除 ✓（若被排除即器械不 sound）。
3. **义务 B（已完成）— frontier 定位**：`lambda5` 线文件只落盘 **passed** 盒；未决盒只在活栈（`certS_nD40.json`：2405 passed / **1228 未决**；`certS_aligned.json`：2621 / **964**）。59 盒档来自 `cover5_smoke2`/`cert6_run2a`（旧表示）。
4. **scope（采纳 lead 裁定）**：lambda5 全单纯形证书即使封口也**只到条件族级**（C451 仅 9+2、C464 无消重叠 WLOG、Tfree-CHAIN L13 引用有误）⇒ 本轮**不再长跑**该线。
5. **义务 C（已完成）— Voronoi 面积包络（lead 的独立可分离计算）**：F 公式与本人独立推导一致（中心三角 ½r²sinα + 目标圆弓段 (β−sinβ)/2），并核对 FT 归一化 `r_n=1/r`；原文 PDF 由 lead 复核 L106–174 ✓。
6. **加严结论（已证，纯几何）**：胞端点距 d1,d2 ≤ r ⇒ 弦 ≤ r·max(2sin(α/2),1) ⇒ `β ≤ 2asin(r·max(sin(α/2),1/2))`（全 α 有效）；**α ≥ π/3 时 β ≤ f_r(α)=2asin(r sin(α/2))** 成立（lead 要的"同侧/目标几何"条件的充分版）。
7. **lead 代数核对（numeric 精确复核，差 ≤1.1e-14）**：在保存对象上 `E=21, E_rr=9, d=1, K=k1+k2=13=E_hr+2d=12+d`（全为紧）；`T_hr=8.640586013=4π−2dτ_hh` ✓；`Σ_{rr}2τ=26.714158824=14π−A+2dτ_hh` ✓（A=Σα=21.193922928）；边全等 `max|τ_a−τ_b|=6.7e-16` ✓；Σβ=2π ✓；胞面积和=π ✓。
8. **组件化面积（lead 提议）确实变紧**：同一真实构型上 edge-level 包络 = **3.1437**（slack **+0.0021**，0.07%）vs 逐胞 Jensen = 3.3950（+8%）⇒ 分解收益 ~100×。
9. **但机制仍不咬**：把 edge-level 包络在**拓扑+角参数**上取最大：`E_sharp(0.3710)=3.3547`（slack **+0.213**）、`E_sharp(0.3800)=3.5994` ⇒ **所有分配 ≥ 0.3635 处均 > π**，即该族在 r ≥ 0.3635 **不排除任何拓扑**；逐胞 Jensen 版天花板 ≈ 0.364（两版一致）。**远低于既有 0.3709** ⇒ 方法是 method limit，不是数学不可能。
10. **口径/实现修复（供他人复用）**：(i) 胞面积必须含 crossing 点 + 弓段（否则 11 胞和 ≠ π）；(ii) 边必须**裁到 D 内**（否则 τ 取到胞外段，恒等式差 1.4e1）；(iii) 三角面积高度 = |c_ic_j|/2（**不是**到边中点的距离）。
11. **输入 hash**：lead 文档 `4e6d0e866265d40f7395086cf1200218…`；certified_object `15a127b2045d90288274bb07dbeae016…`；certS_nD40 `370f8eaad0fea97a6e3b2ac793a0affe…`；certS_aligned `f75d77d76b272ce470f79ce815e252ad…`；LEMMAS `584681991e9683423ca9caf0fe70d881…`；lc-subdiv/C645-RUN5 `e45cdfda8ec73483e31ee738b2593e1b…`。
12. **运行的 job/命令**（均已完成，可复现，累计新盒 = 0，仅 4 个构型的胞剖分）：见 §4。

## 1. 结论（可引用范围）

* **scope**：n=11、9 边界盘 + 2 内盘族、D 的单位闭盘 Voronoi 胞剖分；结论只对该族 + 所列前件成立，**不是** `r_D(11)` 全局最优性。
* **negative（有量化）**：FT 型面积包络（逐胞 Jensen 版与 edge-congruence/组件版）在拓扑参数上取最大后仍 > π，天花板 ≈ **0.3635–0.3640** < 既有严格下界 0.3709 ⇒ 单靠"面积 < π"不能推进；需要额外的拓扑强制引理（n=11 版 FT-L2：例如 q_i 被钉住 / hub 边数被钉住 / hub 胞必须覆盖"环洞"的面积下界）。
* **positive（结构性）**：
  * edge-congruence 组件化包络在真实构型上几乎紧（+0.07%），是后续更细分析的可用骨架；
  * `β ≤ f_r(α)` 的**充分条件 α ≥ π/3**（真实胞 α≈1.63–2.97 rad ≫ π/3）已给出并证；全 α 安全版 `β ≤ 2asin(r max(sin(α/2),1/2))` 同给；
  * lead 的三条角恒等式与 K ≤ 12+d 在本对象上**逐位成立且取紧**，可作为后续枚举的硬约束。

## 2. 校正/纪律

* `run1_frontier_calib.py` 的 frontier 段无效（JSON 只含 passed 盒）⇒ 已被 `run1_calib.py` 取代；未决盒清单**不落盘**（需要时从 builder 复跑并改落盘）。
* 早先版本的 `seg_on_line_in_poly` 用内法向（符号反）⇒ 0 边；`cell_info` 用 `poly_area(inside)`（缺 crossing）⇒ 面积和 ≠ π。两处已修，修复即留下上面的口径条目。
* 所有 output 仅是 numeric 筛选；未做区间/精确认证，不得当证书引用。

## 3. 关键读数（复现见 §4）

| 对象 | 量 | 读数 |
|---|---|---|
| 保存对象 @ r=38/100 | 对角配对判据 | min |v_i−v_{i+4}| = 0.757045 < 2r = 0.760000 ⇒ 未排除（校准 ✓）|
| 保存对象 @ r=R_saved | 同上 | 0.757086 < 0.759968 ⇒ 未排除 ✓ |
| 钝角控制 | MEC vs 外接半径 | 2.000000 vs 2.236068（exact: 4 vs 5）|
| 保存对象胞剖分 | 9 bnd + 2 内；E=21, E_rr=9, E_hr=11, d=1, K=13, Σq=29, 2E=42 | 全部取紧 |
| 保存对象 @ 0.38 | 面积包络（逐胞/edge） | 3.3953 / 3.1437（π=3.14159）|
| G_max over allocations | r=0.3710 / 0.3709 | 3.3176 / 3.3149（+0.176/+0.173）|
| E_sharp over topology | r=0.3710 / 0.3709 | 3.3547 / 3.3528（+0.213/+0.211；这是**上界在松弛上的数值最大**，不代表方法天花板）|
| 排除的分配（允许 K≤12+d）| 0.3710 处 | 仅 K=k1+k2=6(d=0) 一支（r*=0.37225）；**不能排全类**；K=13 的保存对象 ⇒ K=6 绝非 WLOG |

## 4. 复现命令（全部只读输入 + 本目录输出）

```
py -3 -B -X utf8 research-2026/team-current/flash-compute/run1_calib.py
py -3 -B -X utf8 research-2026/team-current/flash-compute/voronoi_area2.py
py -3 -B -X utf8 research-2026/team-current/flash-compute/voronoi_area3.py
py -3 -B -X utf8 research-2026/team-current/flash-compute/voronoi_edges.py
py -3 -B -X utf8 research-2026/team-current/flash-compute/voronoi_edgesharp.py
日志：本目录 out/run1_calib.log, out/voronoi_area2.log, out/voronoi_area3.log,
     out/voronoi_edges.log, out/voronoi_edgesharp.log
```

## 5. 未决 / 下一步（给 lead 的选项）

1. **要面积法咬住**：需一条带宽度的拓扑强制引理（q_i 或 k_j 的钉住；或 hub 胞覆盖"环洞"的面积**下界**与 hub 胞面积上界的对撞）。当前证明里"每 V-vs-边两侧三角全等"已被复核 ✓，但 Jensen 前的角度自由度太大。
2. **另一条**：`E_rr ≥ 9` 的证明目前只到"每个 switch 点引出的内边是不同的 ring-ring 边"（我把这个论证写全了：共线合并会要求一条边两侧胞不同 ⇒ 不可能）——若要进证书需把它写成引理并检查退化。
3. **O1 线（本轮结论）**：5D 局部松弛不够（域内已有 margin −7.6e−2 的严格合法账本）；要证 O1 必须把覆盖可延拓性写进域（见 §6）。
4. **回 λ5 线**：任何"全单纯形"结论先标条件族级；未决盒不落盘这一缺口建议先修（改 builder 落盘 live stack），否则无法做逐盒复核。

## 6. O1（本轮新任务）——局部三盘松弛**不够**，反例已给出（numeric，可复现）

**对象/义务**：flash-structure O1（NEXT-OBLIGATION §4）= 合法 17D 账本中相邻内交点 v_k 不在任何第三盘内部；lead 局部化后第三盘只可能是 k−1 / k+2，压缩为 5D 域
`t1,t2,t3 ≤ A=asin r；|t1−t2|<x=γ12≤t1+t2；|t2−t3|<y=γ23≤t2+t3；x+y>t1+t3；S=t1+x+y+t3 ≥ 2π−12A`。

**结论（本轮）**：**该 5D 松弛不够** —— 域内存在 margin 显著为负的点（r=0.38）：
* 严格合法账本（JSON：`out/o1_counterexample_strict-legal.json`）：t/a = (0.826668, 0.999999, 0.891666, 1−1e−9 ×6)；overlaps min = +1.0e−6（全部 >0）；private min = +0.1309（全部 >0）；Σo = 2Σt−2π 精确（差 0）。
* 该点满足 lead 域全部条件：x = 11.40°, y = 42.25°, |t1−t2| = 3.87° < x ✓, x+y = 53.65° > t1+t3 = 38.37° ✓, **S = 1.606198 ≥ 2π−12A = 1.605629** ✓（刚过约束）。
* **O1 在几何上失败**：pair #0 与第三盘 #2 的 margin = **−7.566626e−2**（mpmath 50 dps 复算，|v| = 0.650263）——即 tip 落在第三环盘**内部**。
* 位置：`out/o1_counterexample_{strict-legal,scan-min,worst-opt}.json`；复现 `o1_triple2.py`（优化）、`o1_debug.py`（独立暴力扫描，同结论 −7.58e−2）、`o1_counterexample.py`（50 dps 复算）、`o1_clean.py`（严格合法化）。

**它为什么不构成对链条的反例（已严格认证，C795 取代 C794，proved-interval）**：该账本**不可完成成 11 盘覆盖**。认证方式 = 三个有理洞点
`p0=(201/500,179/1000), p1=(−89/250,259/1000), p2=(−23/500,−219/500)`：
* 每点显式 `|p_i|² ≤ 0.1936, 0.1938, 0.1940 < 1`（在 D 内）；
* 全部 27 个洞距下界 `min_k |p−c_k|² ≥ 0.1452765, 0.2343680, 0.2465529 > r² = 0.1444`（区间）；
* 两两距离² = 145241/250000, 581393/10^6, 581909/10^6 **全部 > 4r² = 361/625**（精确有理比较）；
⇒ 半径 r 的盘至多含其中一点 ⇒ 两盘不可能覆盖该洞 ⇒ 不存在两个 hub。
**（旧表述已撤回）**：先前写的"残余 MEC = 0.6116 ⇒ 不可延拓"与"tips min-max MEC 排除（O2）"**都不成立/无效**：前者只是 scipy 浮点优化，后者误用了不在洞内的 tips（tips 恰被环盘覆盖 —— 正是 O1 被违反的内容）。见 claims C789（retracted）→ C794/C795（superseded）→ **C796**。

**认证读数（稳健粗界版；详细真界一律见 `out/o1_certificate.json` 对应字段，不在此抄显示小数）**：
* P1 ∀k `sin(t_k) < 19/50`（max 在 k=1：sin t₁ ≤ 1899998628827/5000000000000）；
* P2 `o8 > 0`（区间两端为正）；
* P3 ∀k `2t_k − o_{k−1} − o_k > 13/100`（真下界最小在 k=0 = 6549215358979/5e13；旧稿误用 k=8 值，已修）；
* P4 前置断言 `0 < D < 2r`、`h²`/`ρ` 被开方下界 >0（已删 `max(负,0)` 静默夹）；`|v01|² < 43/100`；`|v−c0| = |v−c1| = r` 为构造恒等式（区间含 r² 仅一致性）；**`|v01−c2|² < 1/10 < r² = 361/2500`（O1 被违反）**；
* P5 三点 `p0=(201/500,179/1000), p1=(−89/250,259/1000), p2=(−23/500,−219/500)`：各 `|p_i|² < 1/5`；27 项洞距下界全 `> 361/2500`；两两距离² 精确有理 = 145241/250000, 581393/10^6, 581909/10^6，逐个精确比较 `> 4r² = 361/625`；
* 器械 `rt_iv`（DEN=1e−14）+ `mpmath.iv`@80dps 全项一致（`mpmath_iv_all_agree: true`）。claims：C789(retracted) → C794(superseded) → C795(superseded) → **C796（粗界版）**。

**因此**：(i) O1 作为"对所有合法账本"的命题，若"合法"= arc-ledger 域 L_r，则**为假**（显式反例，已认证）；(ii) 该反例落在**覆盖可延拓类之外**（已认证）⇒ **链条本身未被推翻**，但它说明 **O1 的证明不能只靠 arc-ledger 松弛**：必须把"覆盖可延拓性"（洞可两盘覆盖 / C559 能力）显式加入域 —— 否则松弛域内含 O1-假点，任何在该域上的证明必然失败。

**scalar（structure C784）校准**：`ρ_j sin δ ≥ r` 只是**充分**条件、非必要：m=3 档的 argmin 处 **真 margin = +0.642** 而 **scalar = −0.380**（`out/o1_triple2.log`）⇒ 用 scalar 判定 O1 会产生**伪失败**；不得把 scalar 当 O1 的等价判据（lead 的质疑成立）。

**复现命令**
```
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_certify.py       # 严格认证 P1-P5（双核）+证书 JSON
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_triple2.py      # 5D 域多起点最小化
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_debug.py        # 独立暴力扫描
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_counterexample.py  # 50 dps 复算 + 旧 JSON
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_clean.py        # 严格合法化
py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_holecheck.py    # 洞/两中心数值（仅诊断，不作认证）
```

## 7. 机制探针：triple-common-point 子类的"洞内含 >r 圆盘"（numeric，仅样本）

**机制（lead）**：若洞内含**完整半径 s > r 的圆盘** B(z,s)，则两个 r 盘不能覆盖该洞（每个 r 盘在与半径 s 圆的交弧测度 ≤ 2asin(r/s) < π）⇒ 该账本不可延拓。判据 = 2 维 max-min：`max_z min_i|z−c_i| s.t. |z| + (min_i|z−c_i| − r) ≤ 1`，成功 ⟺ `d* > 2r`。
**两条判据不可互相比较（lead 指正，已采纳）**：空圆判据（洞含半径 s > r 的完整圆盘）与 3 点 packing 判据（三点两两 > 2r）是**两个不同的充分条件**，量纲/目标函数不同，**不得用数值大小比强弱**：空圆 s > r **推不出** 3 点 packing（后者需 s > 2r/√3），反向也不蕴含。前稿"强 ~30×"的说法作废。
**读数**（`o1_hole_circle.py` + `o1_triple_common.py`，均 < 5 s）：
* 控制（C796 认证的 O1 反例账本）：d* = 0.830835，z* = (−0.092329, −0.001482)，s = 0.450835 > r，|z*|+s = 0.5432 ≤ 1 ✓。
* **triple-common-point 族**（三连续 ring 盘共享一点 p；六盘取最大半宽 A=asin r，|c|=0.92499 ≥ ρ0=0.7467 自动避开核心；S∈[1.6056, 1.7266] 窗口）：31 个**完全合法**样本（overlap 最小 7.1e−5 > 0，private 最小 0.0616 > 0），**31/31 都满足 d* > 2r**，d* − 2r 的分位：q0 = +0.0563, q50 = +0.1065, q100 = +0.1619。
* 最难样本：S = 1.6065（贴近下界 1.6056），t_cluster = (22.14°, 22.10°, 16.10°)，p = (0.4407, 0.4152)，z* = (0.0012, −0.1186) —— **z\* 确实朝 cluster 反方向平移**（与 lead 预判一致），margin d* − 2r = **+0.0563**。
**method gap（必须写明）**：这是**样本 + 子族**（六盘取最大、cluster 随机）上的数值探针，不是全 triple 子类的定理；成功只说明机制在该样本上成立；若失败既不证明可延拓也不否证 triple 排除。**下一步（2D 解析路线）**：约束看似来自六个最大盘的"内边界"（|c_j| = 0.92499）与 cluster 最深盘（ρ ≈ 0.70），可只对 z 做 2 维 Chebyshev 中心解析/小维区间认证。

### 7b. deficit 版探针（`o1_deficit_probe.py`，含 lead 的新约束）

**新约束**：六个非 cluster 盘不能全取最大 —— 由 S ≤ 2asin(2r) 与覆盖 ⇒ `Σ_j t_j ≥ π − asin(2r)` ⇒ **总缺额 D = 6asin r − Σt_j ≤ Dmax = asin(2r) + 6asin r − π = 0.06049824…**，且 `t_j ≥ t0 = π − asin(2r) − 5asin r = 0.32929806…`。缺额分布模式：6 盘均摊 / 2 盘 / 1 盘集中 / 随机；cluster 三弧按剩余预算合法化；**真实 common-point 检查**（min_x max_i|x−c_i| ≤ r，直接算，不靠 S 界）。
**读数**（150k 次采样，5 s）：**52 个合法样本**，全部 `d* > 2r`（无 d* ≤ 2r）；d* − 2r 分位 q0 = **+0.008798**、q25 = +0.0372、q50 = +0.0473、q100 = +0.0920。
* 最难样本：mode = six（均摊缺额），S = 1.6879（界 1.7266），t_cluster = (13.59°, 22.33°, 17.86°)，deficit = 0.0384（界 0.0605），common-point 半径 = 0.378351 ≤ r ✓，min overlap = −4.4e−16（触及 0），min private = +0.4194；margin = **+0.008798**。完整 JSON：`out/o1_deficit_ledger.json`。
* **趋势（已按 lead 指正修正口径）**：样本 min 随样本量单调下降（0.0563 → 0.0272 → 0.0167 → **0.0088**）是**取最小值的必然性**，**不是**"下确界 = 0"的证据；结论只到"本探针无法判定下确界符号"，不得写成"机制可能失效"。
**method gap**：52 例样本 + 子族（cluster 随机、缺额分布有限模式）；无 d* ≤ 2r **不等于**机制成立；d* ≤ 2r 也**不等于**可延拓。**不在本任务内扩样本量宣称认证**。
**复现**：`py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_deficit_probe.py`；JSON `out/o1_deficit_probe.json`、`out/o1_deficit_ledger.json`。
**复现**：`py -3 -B -X utf8 research-2026/team-current/flash-compute/o1_hole_circle.py`；JSON `out/o1_hole_circle.json`、`out/o1_triple_common.json`。


