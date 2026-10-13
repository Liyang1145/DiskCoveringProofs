# CENTRAL-ACUTE-JOINT-CONVEX —— 两中央三角一致 acute ⇒ MEC=SOC 投影 ⇒ 联合可行集凸（区间认证，pilot 盒）

> 路由 r20-alternative/cline2（sole write，no child）。证据/复现：`central_acuteness_interval.py` → `central_acuteness_interval.json`
> （`py -3 -B -X utf8 research-2026/team-current/r20-alternative/central_acuteness_interval.py`）。**不注册 claim**。
> 本轮按 lead 指示**停止** inversion/Hessian 路线（`central_joint_convexity.py` 的两处旧测试：其 F_i-边界点落在 `K_B` 之外、
> 对 joint 集无判定力；`central_joint_convexity2.py` 数值 Hessian 因 1e−20 步长在 50 位下病态而放弃）——**两者均不作结论**。

## §1 结构链（lead 观察）

对象：两个中央三角 `(a, b, c_i)`，`i=0,4`。若在中点/盒上**一致 acute**（三个顶点内角 dot > 0），则
`Rc(a,b,c_i) = MEC(a,b,c_i)`（acute 域上 MEC 半径 = 外接圆半径），于是

```
{ (a,b) : Rc(a,b,c_i) <= r }  =  { (a,b) : MEC(a,b,c_i) <= r }
                              =  proj_{a,b} { (a,b,q) : |q-a| <= r, |q-b| <= r, |q-c_i| <= r }
```

右端是**凸集（SOC 可行域）在 (a,b) 上的投影** ⇒ 凸。两个中央面各给一个凸集，故联合可行集

```
S = (K_A x K_B)  cap  {Rc_0 <= r}  cap  {Rc_4 <= r}  cap  {|a|<1-r}  cap  {|b|<1-r}
```

在 (a,b) ∈ R⁴ 上**凸**（`K_A, K_B` 是凸盘交，strict-hub 球凸）。⇒ 不仅 biconvex，而是 **whole-4D convex**，
Helly-4 / SOCP 可用；无需 Hessian、无需 quartic 消去。

## §2 区间认证（pilot 盒）

盒：环心 ±1/1000（坐标）、`r ∈ [UB*−1e−4, UB*+1e−4]`（精确有理数）；
`a` 取 `K_A` 外矩形 `[−0.0063485534, 0.0060920146] × [−0.2137220365, −0.1453094860]`，
`b` 取 `K_B` 外矩形 `[−0.0056776541, 0.0063439031] × [0.1983527204, 0.6201161469]`
（构造 = 链 pin 盘 ∩ strict-hub 球 ∩ variance 局域化球，与 v3 同；全外向、mpmath.iv, dps=40）。

| face | `(a−b)·(c−b)` | `(b−a)·(c−a)` | `(c−a)·(c−b)` | acute |
|---|---|---|---|---|
| 0 | [0.0265897404, 0.4477129253] | [0.0736658059, 0.2664023276] | [0.3096425022, 0.4675391168] | ✓ |
| 4 | [0.0267137957, 0.4471099972] | [0.0735415775, 0.2670050421] | [0.3093148635, 0.4677438266] | ✓ |

⇒ `uniform_acuteness_certified = true`（六个 dot 的下端全部 > 0，最小 0.0266 ≫ 0）✓。

## §3 承重结论（口径）

* **在此 pilot 盒上**：两个中央三角一致 acute（区间证明，非数值）⇒ 两中央约束 = 凸 SOC 投影
  ⇒ 联合可行集在 (a,b) 上**凸**（Helly-4 / SOCP 可用）。
* **条件性**：结论条件于该盒（环 ±1e−3、`r` 窗口 ±1e−4）与 `a,b` 的外矩形；**不是全局结论**；
  acuteness 本身依赖 `c_i` 与 hub 几何（更宽盒须重跑同脚本）。
* **与其它线的关系**：stress 的 biconvexity（各变量单独凸）是本结论的弱化版（joint 凸 ⇒ biconvex）；
  stress 另报告的"pin/链刻画不充分（中央漏点，`Rc−r=4.0e-6`）"与本件互补——正因如此中央条件必须与 pin 条件联用，
  而本件给出的是"中央条件本身在这类盒上凸"这一结构事实。
* **未做/不主张**：不主张全局；不主张更宽盒；不做 Hessian/inversion；不注册 claim。

## §4 FREEZE（source + 已修的两处 + SOCP pilot）

**Acuteness 结论冻结（same C904 exact box）**：`central_acuteness_interval.py` -> `.json`。
K_A/K_B 接口 source（供独立 Fraction replay）：
(a) pins = 相邻环 r-圆的内交点（较小范数支；**已加 guard：两支不可判即 RuntimeError，不静默取 else**）；
(b) K_A = B(0,1-r) ∩ ∩_{j in {4,5,6,7,8}} B(p_j,r) ∩ B(b_A, eps_A)，b_A/eps_A 用固定精确有理权 (.459977731/.080044539/.459977730) on pins {4,6,8}（variance 恒等式）；
(c) K_B = B(0,1-r) ∩ ∩_{j in {0,1,2,3}} B(p_j,r)，**未**加 B(b_B,eps_B)；故其外矩形上界 .6201161 来自 strict-hub 球 1-r = 0.6200161469 一侧，宽仍合法，acute margin 0.0266 不受影响；
(d) rect_of 端点**已改为 (c-rr).a / (c+rr).b 外向标量**（原 plain-mp 版本不作区间证书，lead 已指出）。
盒：环心 ±1/1000、r ∈ [UB*−1e−4, UB*+1e−4]（精确有理）。结论仍 uniform_acuteness_certified = true。

**SOCP pilot（全 free-site fixed-switch，candidate U_i）**：`socp_fixed_switch_pilot.py` -> `.json`
（表示取自 gluing SOCP-RELAXATION-INDEPENDENT-CHECK.md (a)，**未使用其 dual-zero 说法**；cvxpy 不存在、环境未改，用 scipy SLSQP + 解析梯度，一次 bounded 运行）：
* min r = 0.3799838531198412，与 R* = 0.37998385311983873 差 2.4e−15 ⇒ **candidate switches 处无 relaxation gap**；
* 18/18 endpoint 与 33/33 face cone 约束**全部活跃**（完全饱和角点）；
* chord 下界 0.3785427692（弱）；SLSQP success=true, 11 iter, 末 violation −9.4e−16；
* **dual 未决**（只报 multipliers 读数，不判定；gluing 的 dual-zero 说法与本件无关）；
* 口径：只给 **candidate 角** 的 sharpness 迹象；**不等于** 8 角全局路线 sharpness（需 8 参数空间上 R*(U) ≥ R*）。

## §5 Anchor experiment（numeric；`socp_fixed_switch_anchor.py/.json`）

口径更正（lead）：candidate 处 `min r` 与 R* 的数值吻合是 **sharpness evidence**，**不称 no-gap 已证**。

**基线（saved U，5 次 SLSQP，起点近 primal）**：`V − R* = −1.9e−15`；**SOCP 解 sites 与 saved sites 差 ≤ 5.3e−15**
（即最优解确实落在 primal sites 上 ✓）；endpoint 残差最小三项 `−1.9e−15, −1.7e−15, −1.6e−15`。
**"33/33 全活跃"是 aux 伪影**：face 残差用 1e−9 判据只有 **27/33** 活跃；两个 slack face（`(5,6,9)`、`(7,8,9)`）的残差为 0 是因为
**aux `z_f` 可自由移动而饱和**，与 primal sites 上"circumradius = r"是两回事（原候选这两面 Rc−r = 1.153e−3 ✓ 不变）。

**单开关 ±0.01 rad 扰动（每格 5 次 SLSQP）**：

| 扰动 | `V − R*` |
|---|---|
| switch0 +0.01 rad | +3.735e−4 |
| switch0 −0.01 rad | +1.090e−3 |
| switch4 +0.01 rad | +3.134e−4 |
| switch4 −0.01 rad | +2.898e−4 |

⇒ 所有测试方向 `V > R*`（增益 2.9e−4…1.1e−3）⇒ candidate 角在被测切向上是**严格局部极小**（numeric）；
`+`/`−` 不对称 ⇒ 外层函数在锚点**不可微（角点）**，故单方向中心差分 `(V(+)−V(−))/0.02`（读得 −0.0358 / +0.0012）
**不能**当"外层梯度=0"的证据（不是导数）。radial 方向的 anchor load 不在 `U`（切向）参数化内，未测。

## §6 越级撤回 + 修正审计（`socp_anchor_audit.py/.json`）

**撤回（lead 判定）**：① 有限 ±0.01 的不对称**不证**外层函数不可微（光滑三次函数也不对称）；② 少数方向样本 `V > R*`
**只证"样本上升"**，**不证**严格局部极小。§5 里"不可微（角点）""严格局部极小"的措辞据此作废，只保留"样本读数"。

**保留的 bug 原因（不掩盖）**：`circumcenter` 的 `np.column_stack` 生成转置 2×2 方程组（已改 `np.stack(...,axis=0)`）；
活跃计数用 `-slack < tol` 把**所有可行/松弛约束**都算作 active（已改 `abs(slack) < tol`）——**先前"18+33 全 active"的根因是这个符号 bug**（叠加 aux 饱和），不是松容差。

**修正后读数（saved U，baseline）**：`V − R* = −2.2e−16`；sites 与 saved 差 ≤ 1.4e−15；endpoint 残差 18 项全 ~0；
face 残差（每面 3 项，平方形式 `r²−|c−z|²`）：仅 **face 5 与 face 7**（site 集 `{5,6,9}`、`{7,8,9}`）三项各 **+8.7467e−4**，
其余 9 面 ~0 ⇒ 与其 `Rc − r = −1.1527e−3`（**负号**，与 lead 一致）相容；aux `z_f` 饱和是这些 0 的来源。
**KKT**：`Σα(范数形式) = 1.0000000000000127`，full-free 残差范数 `4.9e−15`（numerically stationary；不做结论）。
**anchor 切向载荷（baseline）**：`(radial, tangential)` = sw0 (−0.10057, −0.08084)、sw1 (−0.01946, −0.01819)、sw2/3 ≈ 0、
sw4 (−0.02289, −0.01362)、sw5 (−0.09545, −0.08910)、sw6 (−0.04378, −0.04819)、sw7 (−0.03206, −0.03876)、sw8 (−0.04657, −0.04539)
⇒ 多个锚点有**显著切向载荷**（观测，不下结论）。

**合法性重定 scope**：弧宽 max = **0.776443**，第二 0.766024，cap = **0.779593** ⇒ 余量仅 0.00315 rad
⇒ **±0.01 rad 扰动会越过 cap**，故那批扰动只能作为 **arbitrary anchors（非 legal pilot）** 记录。

## §7 anchor load 修正（edge incidence）—— 取代 §6 的载荷读数

**lead 指出的索引错已修**：锚点 `U_i` 的关联边是 `ring i → U_i`（约束 `i*2`）与 `ring i+1 → U_i`（约束
`((i+1)%9)*2+1`），**不是** `[2i, 2i+1]`；载荷 `F_i = α_e·unit(U_i−c_i) + α_{e'}·unit(U_i−c_{i+1})`，`α = 2rλ`。
§6 里那组"全负 radial/tangential"读数**作废**（索引错，且未含两条 incident edges）。

**修正后（`socp_anchor_export.py/.json`，全 51 乘子 + incidence + U/C/Z 已导出给 chain）**：
`V − R* = −2.2e−16`、`Σα = 1.0000000000000127`；
`(radial, tangential)` = sw0 (0.061471, 0.036561)、sw1 (0.0, −0.0)、sw2 (0, 0)、sw3 (0.061471, −0.036561)、
sw4 (0.058249, −0.018310)、sw5 (0.059422, 0.019834)、sw6 (0.021699, −0.0)、sw7 (0.059422, −0.019834)、sw8 (0.058249, 0.018310)
⇒ **所有 radial ≥ 0 且 ≈ 正** ✓；**Σ radial = 0.37998385 ≈ r**；**Σ tangential = −0.0**、**总力矩 = −1.8e−15 ≈ 0** ✓
（个别切向非零与"乘子 dual 非唯一"相容；净力矩为零是必须的，已核 ✓）。数值 scope，不结论。

## §8 lift v2（修正 site 平衡后）—— 撤回 v1 的 "no positive" 结论

**source bug（lead）已修**：v1 的 site 平衡只含 endpoint 力、**漏掉全部 face 边力**（每条 face cone 给 site `+α·unit(C−Z)`、给 aux 反向）⇒ v1 的 "无正解 / 强版本无解" **作废撤回**；v1 的 51 映射（压缩 45 再补零）也作废，改用 **未知元组 → incidence 元组**（slack 落位 `[33,34,35,39,40,41]`）。

**v2 读数（`socp_anchor_lift_v2.py/.json`，numeric）**：`rank A = 45`（满秩）；LS 残差范数 **5.0e−10**（≠ 机器零 ⇒ **6 个 slack 槽固定 0 时未获得精确 feasibility certificate**（措辞按 lead 更正：浮点非零残差 + LP 失败**不**证明精确系统不可行））；
**45 个 α 全部严格正（min 0.002934）**、`n(α<1e−9) = 0`；**独立 direct-scatter 校准**（另一套循环、直接散力到 22 节点）复现同量级 **2.7e−10** ⇒ 与 LS 自洽；
max-min LP 在**精确等式**下 `success=False`（infeasible，与 5e−10 残差一致；**不**用"浮点零 t\*"当严格不可行证明——该说法已作废）。
worst 残差行：`site7_1, site6_1, aux6_0, tangential6, site7_0`（量级 ≤ 5e−10）。
导出：`U, C, Z, incidence_51, alpha51_ls, slack_slots, label_cross_map` ⇒ 供 chain。

## §9 outer attack（numeric；socp_outer_attack.py/.json）

**19 个确定性 legal Δ 点**：uniform widths 2π/9、capped-simplex 9 个顶点（w_k=cap=0.779593，其余 (2π−cap)/8）、
以及它们与 uniform 的 9 个 0.5 混合；θ_0=0（旋转对称），逐点用**优化 primal** 求 V。
**结果**：全部 V − R* ∈ [+0.0113, +0.0190] > 0，min_51 残差 ≈ −0.0（优化器容差内可行）；
**ny_bad_point = false（无 V < R* − 1e−6）** ⇒ 该 relaxation 的全局路线在 legal 域**未被证伪**，
且 candidate 处 V − R* = 2e−16 远小于其余点 ⇒ **candidate switches 是所测 legal 集上 V(U) 的孤立近全局最优**。
口径：numeric（SLSQP，凸问题）；relaxation 是**必要**条件、非 cover，故"bad point"钩子未触发，无可 realise 的坐标；
**不测原定理**、不做全局断言。

## §10 撤回（越级）与 sector pilot

**撤回（lead）**：§9 里"放大域内无 bad point ⇒ 精确 legal 域内亦无"**作废**（采样 → 连续域不成立；放大域只覆盖采样点）。
算术更正：九个 width 之差 **9 × 4.07e−7 = 3.66e−6**（不是 2.9e−5）。

**joint sector SLSQP（`socp_sector_pilot.py/.json`，numeric，3 次 bounded）**：均匀 θ、θ_0 固定 0、U_1..U_8 为变量、
约束 `|U_i|=1` 与 `n_i·U_i ≥ cos h`、51 条边照旧：
| h | V − R* | 51 边 min 残差 | sector margin | 备注 |
|---|---|---|---|---|
| 0 | **+0.013675765793** | −6.9e−16 | 0.0 | **与既有 uniform 值 +0.01367577 吻合 ⇒ 标定通过**（`success` 标志为 false，但约束/值均已收敛） |
| 0.005 | +0.012852808 | −8.3e−17 | 0.0 | U 变量使 V 下降 ✓ |
| 0.02 | +0.010596367 | −1.9e−16 | 0.0 | 继续单调下降 ✓ |

⇒ 该 sector 族内 **V > R\***（未出现 bad point）；V 随 h 单调下降（0.01368 → 0.01285 → 0.01060），
距 R* 尚远（candidate 的开关配置离 uniform 很远）⇒ 若要覆盖到 candidate 需更大 h ⇒ 需 B&B（本轮不做）。
口径：纯 numeric，不 certify；乘子和为**未归一化**的粗 dual 侧代理（h=0 那次因状态退化而发散，弃用）；
`U_deviation_max_rad` 指标有 arctan2 绕回 bug，不作读数。
