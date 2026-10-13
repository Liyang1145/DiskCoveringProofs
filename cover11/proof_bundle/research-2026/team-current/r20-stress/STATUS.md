# r20-stress — STATUS（第三轮：interval 乘子/一阶量；2026-09-25）

写作用域：本目录。**未注册 claim**（lead 决定）。证据文件 + 复现命令见下；历史与细节在
`REPORT.md`、`PHASE2/3/3C/3D/4/5` 各 md 与 `PHASE7-INTERVAL-CYCLIC-NU.md`。

## 当前对象（只读）

| id | 对象 | 来源 | 状态 |
|---|---|---|---|
| `Xbox` | lead 的 exact 12D TC root box：`center_hex`（12 个精确二进制浮点）+ `radius_hex = 0x1.12e0be826d695p-30`（1e-9）；变量 `u=(a0,a1,a2,a3,y0,y1,R,λ0..λ4)` | `../lead/repaired_tc_krawczyk.json`（Krawczyk，收缩 4.372e-3，`pass_inclusion=true`） | lead 已认证（存在性/唯一性）；本目录**条件性使用**，未复证 |
| `μ,ν,c_k,s` | 该盒上、genuine physical chord-circle pin 残差的乘子与一阶量 | 本轮 `out/phase7_interval_cyclic_nu.json` | **interval**（条件性，见 PHASE7 §0） |

## 本轮结论（interval，全部在同一个 12D 盒上）

0. **接口件（第三轮 task1，lead 指令）**：`weights_interface.py` —— 自包含/import-safe 的区间权重模块，
   返回 `mpmath.iv`；`physical_weights()` / `radial_partials()` / `root_box()` / `endpoints()` / `positive()`；
   自检 `py -3 -B -X utf8 .../weights_interface.py`（退出码 = 正性判定，并与 phase7 记录交叉核对）。
   说明 `PHASE7B-RIGIDITY-INTERFACE.md`；哈希 `out/weights_interface_hashes.json`；已发 cline2-r23-rigidity。
1. `μ_i = −λ_i > 0`（i=0..4，区间宽度 2e-9；最小 μ₂ ≈ 6.6454e-3）。
2. `ν_j > 0`（odd-9 cyclic formula，9/9；最小 ν₈ ≈ 1.5286e-2）；orbit 求和形式与独立 12D 线性解一致到 1.07e-12。
3. `c_k = 4y²/F_out > 0`（5/5）、`F_out > 0`、`y ≠ 0`、`a'_j = a_ρ > 0`（9/9，min 0.09786）、`a_{R,j} > 0`（9/9，min 1.12469）。
4. `s = Σ μ_i c_i ∈ [0.44497828057, 0.44497858076] < 1`；`1 − s ∈ [0.55502141924, 0.55502171943] > 0`；
   边界总权重 `Σ_j ν_j(a_{R,j}+a_{R,j+1}) ∈ [0.55501534621, 0.55502779247] > 0`；两者之和区间**含 1**。
5. `s < 1` **不是独立前提**：由 R-平稳恒等式 `1 − s = Σ_j ν_j(a_{R,j}+a_{R,j+1})` 与 ν>0、a_R>0 得到（PHASE7 §3）。
6. 控制件：径向导数独立解析表示 vs 60 位差分最大偏差 5.96e-37；区间 ν vs 旧 FD 5.35e-13；径向方程残差含 0。

## 依赖（承重）

`Xbox`（lead Krawczyk）→ 本证书；本证书**不**自证：`rank DB = 5` / Φ 为局部 7D 图 / 盒内根存在
（lead `TC-BOUNDARY-CHART-RANK.md`；r20-rigidity W11 独立复核）与 lift 定理本身
（lead `TC-TO-PHYSICAL-KKT-LIFT.md`）。若上述任一被撤回，本证书的正性结论随之失效。

## 缺口（不得越界引用）

1. 二阶/Hessian、局部极小：**不在本目录**（与 r23-rigidity 分工）。
2. 全局 n=11 目标：本目录不提供下界、不涉及 remote 排除；`r_D(11) = Tcert` 仍缺（REPORT §5 O1）。
3. 本轮区间是"盒上一致包围"：`Xbox` 半径 1e-9 ⇒ μ 宽度 2e-9、ν 宽度 ~5e-7、恒等式闭合 6.4e-6；
   收紧需要更小盒，当前判据不需要。

## 复现（工作区根执行）

```
py -3 -B -X utf8 research-2026/team-current/r20-stress/phase7_interval_cyclic_nu.py
py -3 -B -X utf8 research-2026/team-current/r20-stress/phase7b_analytic_radial_deriv.py
py -3 -B -X utf8 research-2026/team-current/r20-stress/weights_interface.py          # 接口自检（退出码=正性）
py -3 -B -X utf8 research-2026/team-current/r20-stress/audit_lead_minimax_interface.py  # lead 接口简审
```

## 更新记录

* 2026-09-25 第三轮（本轮）：`phase7/7b` + `PHASE7-INTERVAL-CYCLIC-NU.md`；更正 REPORT §0(8) 与
  PHASE5 A0.7/§4（"由 σ₁₈≠0 推出非精确 KKT 点"作废）。
* 2026-09-25 第三轮 task1/task2：`weights_interface.py` + `PHASE7B-RIGIDITY-INTERFACE.md`（r23 接口）；
  `AUDIT-LEAD-MINIMAX-INTERFACE.md` + `audit_lead_minimax_interface.py`（lead 两条 note 的独立简审：
  定理成立、接口成立且更强（`T_zS=K` 且 minimax 核块 = ∇²L|_K）、证书端点精确有理数复算通过；
  两条记账：det 记录为合法更宽外包裹、G01/G10 端点差 2.4e-59 纯属区间取整（对称性精确）。
  **口径更正（lead 第五条）**：盒上"18 分支区间与 R 相交"**只是相容性**，不是"分支 = R at root"的证明；
  该等式是解析的（根 F=0 + chart + 正 conversion）；区间只认证正因子（`F_out>0`、`y≠0`）与权重正性。
  §5 表格、模块 docstring、机器输出键名（`all_18_branch_intervals_compatible_with_R`）均已按此改写。
* 2026-09-25 第三轮 task3（lead 指令：审 rigidity anti kernel，只读、他 sole writer）：
  `AUDIT-RIGIDITY-ANTI-BLOCK.md` + `audit_anti_tooling_check.py/.json/.log`。审计快照 S2 =
  sha256 `5395d0dd291bc8271b6fd8024a9038d7933fc020ba2a8e4d77582aa8c4da9658`（26975 B）。
  已核：weights order（9 face 逐项语义对应 + 9 tie 同序 + 每支权重和 ∋1 ✓）、integer anti basis 与
  区间算出的 `GEPS=diag(2×8,1,1,1)` ✓、kernel 基为严格区间解集包围 ✓、`[A7]` 的 Sylvester 逻辑与
  "radical = rotation" 的解析链 ✓、`TIEPICK` 判据 ✓、jet 自检 ✓；S1→S2 已修我上轮报告的
  `eigvalsh(G⁻¹B)` 误用（合成已知答案检验证伪：误用给假负值）、U 基降级为 diagnostic、`b12`、元数据。
  剩余：**F-now-1** `[A7]` 的补空间索引取错空间（`rot_a[0:3]` 是 11 维 ε-坐标；正确 float-free 公式
  `c*_t = rot_a[FREE[t]]`，FREE=[0,1,6]，横截性 = 认证 `0 ∉ rot_a[FREE[j*]]`）；
  **F-now-2** minor 枢轴零排除/有限性守卫缺失（±inf 可假通过）。已发 cline2-r23-rigidity 与 lead。
* 2026-09-25 第三轮 task4（lead 指定的两项 bearing 检查；快照链 S1 26324 → S2 26975 → S3 28003 →
  **S4 = sha256 `6be637d3d37dea280a26621861afaf31f066605a832fdc60c459ca0dab2a6a76`（29371 B）**）：
  `audit_tie_branch_identity.py` + `out/audit_tie_branch_identity.json/.log`；`AUDIT-RIGIDITY-ANTI-BLOCK.md` §6。
  **B（零穿越判定）**：S4 已用精确形式 `lo>0 or hi<0`（`TRANS_OK`）并并入合并判定；枢轴守卫用乘积+isfinite；
  `min(|lo|,|hi|)` 仅作 margin 报告；对照件 `[-1,2]` 证明旧形式会漏穿越。**A（TIEPICK = C892 tie）**：
  全盒认证 9/9 —— A1 `sup|p*−P_k|² ≤ 1.75e-13`（≪1e-6）、A2 另一交点 `inf|p_other−P_k|² ≥ 3.78374`、
  A3 非相邻站点 `|p*−C_i|²−R² ≥ 0.42480141`（与 W12 的 `F_out ≥ 0.4248` 同源）、A4 另一分支上判据失败
  裕度 `≥ 1.3613519`。他们 S4 也加了 A1/A3 型检查（`tie_min` 用入射距离 f，略强）；**A2/A4 目前只有本目录有**。
  （其后 r23 已自行补 F-now-1/2 + A2/A4 并于新哈希 `e16d23bf…` 请求复审；按 lead "local 重复审计停" 未再开新审计轮，
  我的 A2 值与其读数一致到 7 位：我 `≥3.78374` vs 其 `≥3.783737220`。）
* **2026-09-25 第三轮 task5（lead 新义务：全局结构 / 固定 witness 路线否证）**：
  `GLOBAL-FIXED-WITNESS-NONSHARPNESS.md` + `global_rotation_nonsharpness.py` + `global_finite_witness_probe.py`
  （各带 `out/*.json/.log`）。**解析定理**（lead 路线，含完整证明）：`E = {d_X = R}` 有限且 `0 ∉ E` ⟹ 对任意有限 `Q`
  存在 rotation `θ` 使 `max_Q d_X(R_θ q) < R` ⟹ 固定有限 witness 集**不可能 sharp**。前提区间认证：`E` = 恰 18 个活跃
  见证（9 外心 + 9 tie）、`0 ∉ E`（`d_X(0) ≤ 0.1494284999`）、2 个松弛面 `≤ R − 1e-3` ✓。**定量版（更强）**：
  对候选自身临界点集 `Q0`，`θ = π` 处区间认证 `max_{q∈Q0} d_X(R_θ q) ≤ 0.327817465`，比 `T_cert` 低 **0.05217**
  ⟹ 用 `Q0` 的固定 witness 路线连 `T_cert` 都证不出来。lead 的一阶/结构判据全部通过：11/11 三角 acute、
  外心非零、9/9 tie 两 site 角导数异号、小旋转一阶速率 `−0.1242202 < 0`（独立路线 A 区间认证
  `D_v F ≤ −0.1242201784`，FD 一致）。**方法级负结果**：该速率不能用"每 (w,i) 一条约束"的单 LP 求（tie 集上的
  `min` 是析取，单 LP 当合取用会给出假"无下降"；实测其最优值为 0）；需显式方向认证或 MILP/逐 assignment。
  **更正（lead 指正，两处）**：(i) 该定理**排除所有有限 Q**（无例外），但**只用精确 `R*`**：`r_fin(Q) < R*` `∀Q`
  （= C903 口径，不引 `T_cert`）；(ii) **不得**把 `R*` 与 `T_cert` 做精确比较（差 `≈8.5e-46` 是 60 位数值读数，
  C891 盒宽 `1e-15` ≫ 该差，无认证依据）⟹ 任何 "`< T_cert`" 的**普适**结论不成立、不得引用；`T_cert` 只用在
  **具体 `Q0`** 的定量比较上（差距 5.2e-2 ≫ 分辨率，合法）。我原先写"特意设计的 ≥12 点 Q 未排除"是把 `C529`
  当成了 `R*`，该句已删。
* **2026-09-25 第三轮 task6（lead 新义务：审 `lead/INWARD-ARC-SWITCH-UNIQUENESS.md`）**：
  `AUDIT-INWARD-ARC-SWITCH-UNIQUENESS.md`（纯解析，无脚本）。结论：**被审证明正确、前提充分**（"至多一个 covered
  equality point" 的 `t±` 平均论证无跳步；essential/无包含 ✓；相交短弧的存在性 IVT ✓，含单点相切 ⟹ triple point ✓）。
  增量：① 给出**更简洁的不同几何推导**——两 equality point 都被覆盖 ⟹（凸性）整条弦 ⊂ 两盘 ⟹（平行四边形）
  透镜 ⊂ `B(m,k)` ⟹ 弦长 ≤ `2k`，而弦长 `= 2sqrt((m·n)²+1−|m|²)`，与 `k² = a·b+r²−|m|² < 1−|m|²`（内向界+相异）
  合起来直接给 `(m·n)² < 0` 矛盾；② 半角的**精确阈值**：`a ≤ asin(r)` ⟺ `(ρ−sqrt(1−r²))² ≥ 0`，
  故 essential 论证成立的精确条件是 `r < sin(π/8) = 0.382683…`（>`≤0.38` ✓）；③ 写出 "9 条 essential 弧循环相邻
  ⟹ C879 逐边 tie 唯一性" 的完整链（含 `d < 2r` 自动成立），并显式保留两项剩余：**图接口**（弧序相邻对 ↔ fan 图边）
  与 **C879 的 `p_out` 条件**（本引理不覆盖）；④ 一处**口径问题**（请 lead 定名，非 claim）：tie 为三点共点时，
  另一圆-圆交点满足 `|p_other|² = 2(a·b+r²) − 1 < 1`（内向界下**严格在单位圆内**），与 "p_out ∉ int D（automatic）"
  的读法需要对齐命名（若 `p_out` 指另一个单位圆 equality point 则平凡 ∈∂D）。
  **lead 已统一命名并补入其文档 §Inner/outer ring-circle intersections**（我读过并确认 ✓，与我的 §4 推导与数值控制一致：
  `pin` = 较小 norm（`< 1`）、`p_out` = 较大 norm（`≥ 1`）；等号 = tie 为三点共点 ⟹ C879 的 `p_out` 条件对 canonical
  相邻弧**自动成立** ✓；C905 已登记，其 control 字段采用了我给的透镜/弦长推导 ✓）。
* **2026-09-25 第三轮 task7（lead 新 structural route：中央纤维 biconvexity）**：
  `CENTRAL-FIBER-BICONVEXITY.md` + `central_fiber_biconvexity_pilot.py` + `out/central_fiber_biconvexity_pilot.json`。
  解析：`ρ(a,b,c_i)` 三顶点对称、product 恒等式对弦端点对称，但双向**不自动**（FAN_A 5 pin vs FAN_B 4 pin、
  `WL` vs `WB`、参考 `bB` vs `aA` ⟹ `ε_A=0.0617` vs `ε_B=0.0674`）。pilot（`delta=1/1000`、`omega=1/10000`、
  `r0=3799838531198387090485182/10^25`，与 C904 同参数）：**标定通过**——我独立实现的原方向
  `G(face_0)=0.024568665543`、`G(face_4)=0.024540121682`，与 C904 报告的 `>0.0245686/>0.0245401` 一致到 7 位 ✓；
  **镜像方向**（弦 `(b∈KB, C_i)`、参考 `aA`）`G'(face_0)=0.047558593752>0`、`G'(face_4)=0.048043973822>0` ✓
  ⟹ 两方向 far 分支统一被排除 ⟹ 单盘约化在两个变量上同时生效 ⟹ **biconvex on KA×KB**（仍非 joint convex；
  非全局结论；换盒宽须重跑同脚本）。
* **2026-09-25 第三轮 task8（lead 源码 audit + 新 SOC route）**：
  (a) **kernel 修正并 freeze**（lead 源码 audit 三处缺陷，均已修 ✓）：① pin 选择**不允许无条件 `else`**
  （充分 guard：`n1_hi<1≤n2_lo` / `n2_hi<1≤n1_lo` / `n1_hi<n2_lo` / `n2_hi<n1_lo`，否则 `raise UNDECIDED`；
  实测 9/9 由 `p1 smaller norm` 判定）；② `sqrt_iv` 上端 `<0` 直接 **fail（domain invalid）**、下端跨 0 给合法外向包围
  并记 `negative_radicands` 台账（实测 0 条）；③ `bbox_inter` 判空（`x0>x1`/`y0>y1` 即 `raise`）。
  另修 **radicand 台账时序 bug**（此前在调用前构造 ⟹ 空账）：现 4 次检查、radicand 下界最小值 `−0.00275659`
  ⟹ 原方向盒内含 `k=0` stratum（显式标注 + strict-gap/equality 排除）；镜像方向 `k>0` 处处 ✓。
  **哈希（freeze）**：`central_fiber_biconvexity_pilot.py` = `7c9951ad…52d84df`（14111 B）；
  `central_missed_point_arc_audit.py` = `64490b11…963fa8b`（9106 B）；读数 json 哈希见 `out/frozen_kernel_hashes.json`。
  (b) **中央漏点审计（另一表示）**：`AUDIT-CENTRAL-MISSED-POINT-ARC-REP.md`。11 个精确 sign 的多重集与其列表**完全一致**
  （仅顺序不同）✓，最小值 = 其 `Rc2_minus_r2` ✓，`|p|<1` ✓ ⟹ p 未被覆盖；p 与 `(hA,CEN[5],hB)` 精确等距、`R_c−r=4.006e-6`、
  三角 acute ⟹ p 是 maximin 洞心；**边界弧只统计 9 条 ring**（2 hub 严格内部 `|h|²<(1−r)²` 精确 ✓ ⟹ 无弧），
  9 弧覆盖边界（最大缝隙 `−3.728e-5` rad）⟹ 纯内部 cap-overlap 洞；九个 pin 用**正确聚合量**
  `max_over_pins(min_over_hubs slack² sign) = −1 < 0` ✓ 全覆（分派 = chain A 4 + chain B 5，与其 FAN_A/FAN_B 一致）；
  其旧 `pins_strict=false` 已由 lead 定位为 sign helper 的 `−β²Q` 代码 bug（非口径差异），现字段 True 与我的精确读数一致。
  (c) **SOC route（纯解析，未写区间代码）**：`CENTRAL-SOC-DUAL-AUDIT.md`。要点：真实中央条件 = **circumradius ≤ r**
  （洞在 circumcentre）；凸代理 = **MEC ≤ r** ⟺ SOC（`∃z_i`）；`R_c ≤ r ⟹ SOC 可行` **无条件** ✓（故
  **SOC 不可行 ⟹ 面条件失败**，是**无条件**证书 ✓），反向只在**非钝角**成立（钝角/近共线反例：三点近共线相距 0.2，
  `MEC≈0.1≤r=0.4` 而 `R_c` 巨大 ✗）⟹ joint-convexity 突破需要 uniform acute；集合 `{(a,b,z_0,z_4)}` 是 SOC ∩ 盒
  ⟹ **joint convex**（投影也凸）；退化分类：直角 ✓ 仍等价、钝角 ✗、共线已被 far-margin 排除（§1(ii) 的显式论证）、
  `k=0` 有 strict-gap 论证。**对偶不可行 witness 形式**：任意有理权重 `w`（Σw=1）给 `V_w(p) ≤ r²`（均方方差恒等式），
  故 `V_w > r²` ⟹ SOC 不可行 ⟹ 中央条件失败；固定 rings 时 `V_w(a,b,c_i)` 是 (a,b) 的凸二次型，其**盒上极小**有闭式
  （有理 + 至多一个 sqrt）⟹ 若极小 `> r²` 则 **fixed rings ⟹ no hub**（exact、simple、SOC-support 对偶 ✓，不依赖 acute
  也不依赖 biconvexity ✓）。按 lead 指示：停 biconvex envelope、不重复 acute 读数（等 alternative）。
* **2026-09-25 第三轮 task9（lead 新任务：独立 derive 向量力对偶 + 8-angle oracle 性质）**：
  `VECTOR-FORCE-DUAL-AND-ORACLE.md`（纯解析，未跑代码）。要点：(i) primal = 11 center node + 11 face aux node、
  9 fixed anchor `U_i`、51 norm edge `≤ r`、`min r`；(ii) 对偶 = 边标量 `y_e ≥ 0, Σ y_e ≤ 1`、单位方向 `|w_e| ≤ 1`、
  **自由节点力平衡** `Σ_{e∋v} y_e w_e = 0` ⟹ **`r ≥ Σ_i ⟨l_i, U_i⟩`**（锚载荷点乘锚坐标 ✓）；(⋆) 是等式
  （有限 index ⟹ minmax/Sion ✓）⟹ 固定 switch 下强对偶 ✓（KKT 即全局最优 ✓）。(iii) **退化两支必须分清**：
  内点支 `Σ y_e w_e = 0`；锚点支（节点落在某 incident 锚上）**只需** `|Σ_{e≠j} y_e u_e| ≤ y_j`（子微分被支配），
  而 gluing 的 "dual zero"（同一节点同时等于两个锚 `U_i ≠ U_j`）**非法** ✓。(iv) 候选处 exact stationarity dual 配方：
  face circumcentre 的**重心坐标**（三边方向权重）+ 边界 tie 的**切向 ±t̂** 按 C897 权重分配，拼成 `Σy=1`、逐节点平衡的对偶点；
  值 `= r` 即精确驻点（与 C897 的同一性用等式 `Σ⟨l_i,U_i⟩ = r` 验证，留给 alternative pilot）✓。
  (v) **oracle 性质**：`V(U) = sup_dual Σ⟨l_i, U_i⟩` **正齐次** ✓、**关于 Cartesian `U` 凸**（= 某凸紧集支撑函数 `h_K` ✓）、
  `∂V(U)` = 达到最大值的对偶点集；但外层 `U` 落在单位圆 9 重乘积（torus，**非凸**）⟹ `min_{T^8} V(U(θ))` 是
  "凸 ∘ 非凸参数化" ✗ ⟹ **不能直接 global**（凸性只用于固定 switch / 局部）；即便凸松弛到 `|U_i| ≤ 1` 也不等于原问题 ✗。
  (vi) 已判死并记录：central-box variance 证 no-hub ✗（cover box 内本就不可能）；不再续 biconvex envelope ✓。
* **2026-09-25 第三轮 task10（lead 修正 + exact candidate lift 义务）**：
  (a) **修正**（写入 `VECTOR-FORCE-DUAL-AND-ORACLE.md`）：强对偶**不用** "finite index ⟹ Sion" ✗（自由节点无界），
  改为 **Slater**：所有自由节点 = 0、`r = max|U_i| + 1` 严格可行 + 目标有下界 ⟹ 强对偶 ✓；`r` 口径两版
  （`r ≥ 0` ⟹ `Σy ≤ 1`；`r` 无限制 ⟹ `Σy = 1`）；**向量预算 `Σ|f_e| ≤ 1` 形式的证书永远合法** ✓。
  (b) **§7 一般 lift 引理 L**（承重骨架）：(L1) primal 可行 `≤ R*` + (L2) 对偶可行（`y_e ≥ 0`、`|w_e| ≤ 1`、
  逐自由节点力平衡、预算 ≤ 1；退化按 §2 两支）+ (L3) 值等式 `Σ⟨l_i,U_i⟩ = R*` ⟹ **fixed-switch SOCP optimum = R*** ✓
  （弱对偶 + 可行性夹逼；不需 Sion、不需 tight 预算 ✓）。**候选字典**：anchor = 9 tie；center node = 11 site；
  aux node = 11 面外心（9 活跃足够）；边 = 33（面心↔三顶点）+ 18（tie↔两侧 ring）= **51** ✓ 与 lead 一致；
  面边力 = 面**重心坐标**、anchor 边力 = tie 权重按**切向 ±t̂** 分配 ⟹ 面边平衡 ⟺ `O_f = Σw_jV_j` ✓、
  ring/hub 平衡 ⟺ **C897 乘子方程**（按构造、可解析写出 ✓）。
  (c) **已由区间读数覆盖**：(C-a) 面重心坐标全正 ⇐ 认证的 **11/11 acuteness**（外心重心坐标 = `(sin2A:sin2B:sin2C)`，
  全正 ⟺ 三内角 < π/2 ✓；证据 `out/global_rotation_nonsharpness.json.aux_acuteness` ✓）；(C-b) tie 切向偏导**异号 9/9** ✓
  （同文件；"各自 away from 0" 的逐条 margin 待办、廉价）；(C-c) (L1) 候选在 `R*` 下所有边距离 ≤ `R*` ⇐ C892/PHASE7 ✓。
  (d) **未完成（明确列出）**：(L3) 值等式的解析证明。本件新增**精确形式**：由逐节点平衡，
  `Σ_i⟨l_i,U_i⟩ = Σ_e y_e·dist_e` ✓（(V1)：自由节点项全消 ✓），故值等式 ⟺ **`R*(Σy_e − 1) = Σ_e y_e(dist_e − R*)`** ✓
  （预算松量与距离松量精确相抵）；9 活跃面边紧 ✓、**2 松弛面 `dist = 0.99697R*` ✗** ⟹ 必须解析处理这两条边
  （**不得**把 rounded residual zero 当 identity ✗）。
* **2026-09-25 第三轮 task11（lead 源码 audit：修 instrument bugs + radial 推导）**：
  (a) **修 `fresh_acute_slopes_interval.py` 四处**：① 符号判定改**两侧穷尽**（`HI<0` 或 `LO>0`，两侧都必须可判），
  删掉"只看 LO"与"`min(|endpoints|)` 排跨 0"的错误判据 ✗；② 统一保守阈值 **|slope| ≥ 0.51** ✓；
  ③ 斜率方向改为 lead 口径 **(U − c)/norm**（原 `(c−U)` 与注释相悖；异号性不变 ✓，符号整体翻转 ✓）；
  ④ 删除 `set(map(tuple, dicts)) is not None` tautology ✓；**判据全部由 raw iv 计算**，`nstr` 字段标注 diagnostic ✓。
  **重跑**：acuteness **11/11** ✓（最坏 0.0752478 ✓）；tie **9/9** 满足 `[两侧可判 AND 异号 AND 两侧 |slope| ≥ 0.51]` ✓
  （逐条下界 0.5111873–0.8891367 ✓；site k 一律正、site k+1 一律负 ✓）。证据 `out/fresh_acute_slopes_interval.json`。
  (b) **§7.6 新增 2 行解析（anchor load 的 radial 正性）**：切向取消 `⟨l,JU⟩ = −[y⟨c,JU⟩ + y'⟨c',JU⟩]/R = 0`
  （由 (C-b) 异号且 ≥ 0.51 ⟹ 2×2 有 `y,y'>0` 解 ✓）；radial `⟨l,U⟩ = [y(1−⟨c,U⟩) + y'(1−⟨c',U⟩)]/R > 0`
  （由 `⟨c,U⟩ ≤ |c| < 1` 严格 + `(y,y') ≠ 0` ✓）⟹ `l` 为严格向外径向载荷 ✓。
  **口径**：只对 C897 split 构造的对偶解成立，**不**声称所有最优对偶解都 radial ✗。
  (c) **同时作废**（lead §5 纠正）：`V2 补偿边` 段 ✗ —— 18 物理权重 = 9 tie + 9 active-face、两 slack 面 6 条零力边、
  `Σμ+Σν = 1` exact ⟹ 带力边全紧 ⟹ `Σ⟨l_i,U_i⟩ = R` 精确 ✓（无缺口 ✓）。
* **2026-09-25 第三轮 task12（harmonic-stress envelope：lead 四处接口纠正 → v2）**：
  `HARMONIC-STRESS-ENVELOPE-LEMMA.md` **v2（全文重写）**。① 变量改**角向**：`δ = θ − θ*`（固定整体旋转，`θ ∈ R^8`），
  `f_j(θ) = F_{α_j}(U(θ))`，`g_j, H_j, K, S` 全部在该图内 ✓；② **撤**"二次型 ⟹ 无三阶项" ✗——写明
  `H_j = 2(∂U/∂θ)^T S_{α_j}(∂U/∂θ) + 2(∂²U/∂θ²)S_{α_j}U*`（第二项非零）与**显式余项** `|Rem_j| ≤ C_j|δ|³`
  （常数由 cos/sin 二/三阶导 ≤ 1 给绝对界）✓；③ 写入 **Euler 障碍**：`F_α` 关于 `U` 二次齐次 ⟹ Cartesian 梯度凸包
  **永不含 0**（取内积 `U*` 得 `0 = 2R² > 0` ✗）⟹ 只能在角向图表述 ✓；④ **split 引理 E′**：用 distinguished
  `f_0 = f_{α_radial}`（`g_0 = 0` ✓）提供 `K := ker(G^T) ∩ rot^⊥` 上的二阶正性，用对称 ± 族提供角向锋利性 (E2′)；
  证明按 `|δ_S|` 大小分两支（大的用一族的一阶项，小的用 `f_0` 的二阶项 + `|δ_K|² ≥ |δ|²/2`），取
  `ρ = min(c_1M/(4C), c_2/(16C_0), 1)` ✓；并明确**任意 λ-平均不安全** ✗（`Σλ_jg_j ≠ 0` 时 `δ_S = O(|δ|²)` 方向的
  线性增益降为 `O(|δ|³)`，**分方向单独修不了** ✓）。
  数值（**仅 numeric**）：lead `dual_envelope_check.json`（rank 41 数值秩、`dim A* = 4`、`G` 奇异值
  `[.7451,.5786,.3646,.10391]`、投影 H 特征值 `[.00742708,.01752846,.04230869,.07123306]` 全正、`α_min = .002934`）；
  chain 单点 α_radial（min α `0.00293444`、balance `2.7e−10`、**angular grad `5.4e−11`**、`E(U*) = r²` 差 `+4.44e−16`、
  9×9 角 Hessian 含 **−9.28e−3** 与旋转核）——两者不冲突：单点 Hessian 在 `K` 外的负方向由族内换 α 处理，
  `H_0|_K ≻ 0` 是**有内容假设**（已与 chain 互相确认 ✓）。不再向 chain 索要零空间基（lead 已算 ✓）。
  未决：`S`/`K` 生成元、`H_0|_K` 的**区间**正下界、`c_1, C_0` 的界、C897 stress 内部性（`α_min > 0`）——需 lead 指派由谁实例化。
