# CENTRAL-HELLY-SCREEN —— crescent 接口（方向已修正）+ 固定 ringbox 的 uniform distal exclusion（区间证书）+ Helly-3 消去 b 的有限 witness 类计数

> 路由 r20-alternative/cline2；只写本目录；无子派生；**不注册 claim**（用户/lead 指令：本路线不自行 claim）。
> 输入 = `n11/upper/certified_object.json` 精确有理圆心 + `lead/q0_graphs.json[2]` 的 q0 面表；
> 依赖在册 **C879**（链凸化：`h ∈ B_open(0,ρ) ∩ ∩_j B(p_j,r)`，ρ=1−r）、`lead/R20-CENTRAL-SPAN-NECESSITY.md`
> 的乘积恒等式、geometry 的 `STRICT-HUB-FINITE-DISJUNCTION`(A/B)。
> 证据/复现：`central_crescent_interval.py` → `central_crescent_interval.json`；
> 修正后的代数件仍在 `central_crescent_stress.py/.json`（[L2] 字符串已改为正确方向）。
>
> **状态提醒**：lead 已 **retract C894**（其 (ii) 的包含方向写反）；C895（quartic 无加权二次 stress）与
> C896（候选处读数）内容不受影响，但 C896 未登记 dependsOn、且不再新增 claim（见 §7）。

---

## §0 一句话

在**固定 ring box** 里把 hub A 局域化（`a ∈ K_A` 片段）后，**uniform distal exclusion**（两个"远端盘"与整个 `K_B` 不相交）
可以被**区间算术证明为一个区域判据**；一旦成立，b 的精确条件就是
```
b ∈ K_B ∩ B(q_0(a), r) ∩ B(q_4(a), r) ,   |b| < ρ ,          (★)
```
与 `K_A ∋ a` 合起来是**两个凸（圆盘交）screen**；再用 **Helly-3** 把 b 完全消去，只剩 §5 的**有限个 a 上的
MEC/min-norm 条件**（真参数减维：b 的 2 维 → 0 维）。quartic 无需消（因为它根本不进入，见 §1/§5）。

## §1 修正后的 crescent 接口（方向！）

固定 `A≠C`，`0<|AC|<2r`；`q,q'` = 过 `A,C` 的两个半径 r 圆心（关于直线 `AC` 镜像）；`g_y(p)=|p-y|²−r²`。

* **L1（对称差，已有符号验证）** `ρ(A,b,C) ≤ r ⟺ g_q(b)·g_{q'}(b) ≤ 0`
  `⟺ b ∈ (B(q,r) ∪ B(q',r)) \ int(B(q,r) ∩ B(q',r))`。
* **L2（方向修正版）** 等半径 ⇒ 根轴 = 弦线 `AC`；在 `AC` 的 q-侧闭半平面 `H_q` 上逐点 `g_q ≤ g_{q'}`
  ⇒ **`B(q',r) ∩ H_q ⊆ B(q,r)`（远端半盘 ⊂ 近端盘）**。
  ⚠ 原稿写成 `B(q,r) ∩ H_q ⊆ B(q',r)`（反了）。反例（lead）：`r=1, A=(-3/5,0), C=(3/5,0), q=(0,4/5), q'=(0,-4/5), p=q`
  给出 `g_q=-1` 而 `g_{q'}=39/25>0`。
* **L3（超额 = 半 lens，且落在远端盘里）** `(B(q,r) ∩ H_q) \ {crescent} = B(q,r) ∩ int(B(q',r)) ∩ H_q ⊆ B(q',r)`；
  又由平行四边形律该超额 ⊆ 弦 `AC` 的 Thales 盘（`|·−mid(AC)| ≤ |AC|/2`）。
* **推论（接口所依赖的那一条，仍然对）** 若区域 `R` 满足 `R ∩ B(q',r) = ∅`，则
  `{b ∈ R : ρ(A,b,C) ≤ r} = R ∩ B(q,r)`（**等式**）。证明：L1 给出左边 = `R ∩ (B_q ∪ B_{q'}) \ int(lens)`；
  `R ∩ B_{q'} = ∅` ⇒ 第一项 = `R ∩ B_q`，且 `int(lens) ⊆ B_{q'}` ⇒ 第二项为空。∎

## §2 条件定理（uniform distal exclusion ⟹ b 的精确条件 (★)）

固定 ring box（9 个环心 + r 的区间）与 `i∈{0,4}`，记 `c_i` 为中央环端点，`q_i(a),q'_i(a)` 为过 `(a,c_i)` 的
两个半径 r 圆心（`q_i` 取 hub B 所在侧的那一个，即"近端盘"）。假设

* **(H1) C879 接口**：两 hub 各自属于其链凸集 `K_A = B(0,ρ) ∩ ∩_{j∈{4..8}} B(p_j,r)`、
  `K_B = B(0,ρ) ∩ ∩_{j∈{0..3}} B(p_j,r)`（`p_j` = 相邻环 r-圆的内部交点；q0 面表见 `q0_graphs.json[2]`）；
* **(H2) uniform distal exclusion**：对 box 内所有数据、所有 `a ∈ K_A`：
  `K_B ∩ B(b_B, ε_B) ∩ B(q'_i(a), r) = ∅`，其中 `b_B=(p_0+p_3)/2`、`ε_B=√(r²−|p_0p_3|²/4)`
  （variance 恒等式 + 非负有理权 `(1/2,1/2)` ⇒ 任何合法 hub B 满足 `|b−b_B| ≤ ε_B`；**纯 ring-only**）。

则对任何合法配置：`ρ(a,b,c_i) ≤ r ⟺ b ∈ B(q_i(a), r)`（`i` 分别成立），于是
```
两中央 face 对 b 的全部约束  ⟺  (★):  b ∈ K_B ∩ B(q_0(a),r) ∩ B(q_4(a),r),  |b| < ρ .
```
证明：只需在 `R := K_B ∩ B(b_B,ε_B)` 上用 §1 推论（`R` 与远端盘不相交 = (H2)）。∎
**注意**：(★) 里**没有** quartic 项、不需要任何 dual/KKT/CQ——非凸性被"定向 + 远端盘排除"**精确**吃掉（这就是它比
"正加权消 quartic"（C895：不可能）更强的原因）。

## §3 区间证书（`central_crescent_interval.py` **v2**；mpmath.iv，dps=40，全部外向）

> **v2 = lead code review 已落实**：(1) 权重全部改为**精确有理** `iv(num)/iv(den)`（不再 `float()`），
> variance 恒等式的 `Σλ=1`/乘积保持精确；(2) 输出 = 30 位 endpoint 字符串 **+** `nextafter` 有向 float 两套；
> (3) **每个 sqrt 都有合法性契约**：pin 根号 `r²−d²/4`（UB<0 ⇒ d>2r ⇒ **ILEGAL/UNDECIDED**，绝不静默夹 0）；
> 中央圆 `r²−|AC|²/4`（UB<0 ⇒ 整 box **EXCLUDED**：`|AC|>2r ⇒ ρ ≥ |AC|/2 > r`，face 必失败）；
> 局域化 `r²−V`（`V≥0` 代数成立 ⇒ 下端夹 0 有据；UB<0 ⇒ `V>r²` ⇒ 整 box **SCREEN-EXCLUDED**；否则 `ε=√UB` 为上界）；
> (4) `disk_bbox` 用**外层标量端点** `((cx.a−r_hi, cx.b+r_hi), (cy.a−r_hi, cy.b+r_hi))`，box 交用标量 max/min；
> (5) `r₀` 标注为**保存的有理上界对象 UB\*（C529 行）**，**不是** exact root；**不主张任何 box 覆盖精确最优点**
> （fixed-root inclusion 未证）。**δ 读数只有在 v2 代码下才算候选证书**（此前 δ 读数已作废，lead 已标 not accepted）。
> **(6) 声明域**：本证书只对 box 内的 **C879-legal tuples** 断言（不是对该 box 的一切点）；pin 内根归属用
> "unit-disk 判据（UB<1 ≤ LB(outer)）"优先，退化时才退到"较小 norm 判据"，并在两判据都不定时显式 `UNDECIDED`
> （两根都在单位圆内的 tuple 不是 C879-legal，本来就不在声明域内）。

* **box 参数**：`c_i ∈ [c_i−δ, c_i+δ]²`（9 个环，坐标各向同性）×`r ∈ [r₀−w, r₀+w]`（`r₀` = 保存的有理上界对象 UB\*）。
* **A 片段（moving hub A）**：**固定精确有理权** `(459977731, 80044539, 459977730)/10⁹` 作用在链 pin `{4,6,8}` 上
  得 `b_A, ε_A`（variance 恒等式 ⇒ `a ∈ B(b_A, ε_A)`，**区间证明的加厚**，取代旧 "numeric 1.4e−8"）；
  再与 `K_A` 矩形相交。名义处 `ε_A = 5.905046376e−9`（区间）。
* **判据** `G_i := |b_B − q'_i(a)| − ε_B − r`（全区间求值，`q'_i` 取 `a` 在 A 片段上的整体包络；
  分支由 `det(c_i−a, b_B−a)` 的区间符号判定）。`G_i` 下确界 > 0 ⇒ (H2) 成立。`ε_B = 0.033062070669`（权 `(1/2,1/2)` on pins 0,3）。
* **读数**（`central_crescent_interval.json`，v2，exact-rational 权重）：

| 箱 | `G_0` 区间 | `G_4` 区间 | 结论 |
|---|---|---|---|
| δ=0, w=0 | [0.15415898185, 0.15415902122] | [0.15415898245, 0.15415902185] | CERTIFIED |
| **δ=1.8720480434e−3, w=0** | [2.9687e−5, 0.269417] | [6.58e−13, 0.269294] | CERTIFIED（face 4 为瓶颈） |
| **δ=1.8200529466e−3, w=1e−4** | — | — | CERTIFIED |
| δ=1.9e−3 | 下确界 < 0 | 下确界 < 0 | FAILED（G 下界跨 0） |
| δ≥0.05 | — | — | UNDECIDED（pin 内根选择显式返回） |

  即：**uniform distal exclusion 是候选附近的"区域判据"**，在坐标半宽 ≈**1.872e−3**（r 固定）/
  ≈**1.820e−3**（r 窗口 ±1e−4）上区间证明；在最大 δ 处 screen 数据：
  `K_A` 矩形 ≈ `[−0.0101, 0.00986]×[−0.23663, −0.14219]`，`K_B` 矩形 ≈ `[−0.00924, 0.00990]×[0.19482, 0.62002]`，
  两近端盘中心矩形半径 ≈ `0.0891` ⇒ screen 盘半径 `r + 0.0891 = 0.46908`。δ 的瓶颈是 A 片段包络（≈0.089），
  不是 exclusion 本身；B&B 细分或"在 `K_A ∩ 球` 上直接包络 `q_i`"会改善。

## §4 Helly-3：b 的完全消去与 witness 类计数（**权威版本在 lead / geometry，本表仅作交叉核对**）

> **接口权威件**：lead 的 `lead/CENTRAL-FIBER-HELLY-REDUCTION.md`（条件定理 + **25 个 new triples**，
> 含 "far positive 自动排 collinear" 的证明）；geometry 的 `r20-geometry/CENTRAL-COUPLING-NORMAL-FORMS.md`
> §2.1/§2.2（H1–H6 在 two moving central disks 上的显式算式，含 H5 的有限候选与 H6 的 orientation-free
> MEC 两分支）。**本件不重推，也不与之竞争**；下表只给出"三元素子族按是否含中央盘"的**计数**，用于规模核对。

在 (★) 里，对**固定 a** 的 b 集合族是（R² 中的凸集，有限）：
```
𝓕(a) = { B(0,ρ) （开，来自 strict hub） }  ∪  { B(p_0,r),…,B(p_3,r) }（4 个"链盘"）  ∪  { D_0(a)=B(q_0(a),r), D_4(a)=B(q_4(a),r) }
       = 1 开球 + 4 链盘 + 2 移动中央盘 = 7 个集合。
```
Helly（R²，n=2）⇒ `∩𝓕(a) ≠ ∅` ⟺ 每个 ≤3 元子族都有公共点（有限族、开/闭同界）。
**配对与三元素枚举的权威版本由 geometry 持有**（`r20-geometry/CENTRAL-COUPLING-NORMAL-FORMS.md` §1–§3，
固定 a 的 b-fiber 有限盘 Boolean 组合；放松凸 ⟹ Helly-3 ⟹ **H1–H6**：H1 两 pin `>2r`；H2 pin–动盘 `>2r`；
H3 两动盘 `>2r`；H4 `|u| ≥ ρ+r`；H5 开球+两盘 `μ(a) ≥ ρ`；H6 三盘 `ψ(a) > r`；每项都是**对 a 的显式条件**）。
本件**不重复**该枚举，只补两张"计数/对应"表（用于规模控制与接口核对）：

**（a）三元素子族的计数**（`C(7,3)=35`，按是否含中央盘分层）：

| 类 | 组成 | 个数 | 归属 |
|---|---|---|---|
| 旧 | 3 个链盘 | `C(4,3)=4` | geometry A/B（ring-only）；对应 H6 中的 pin-only 三元 |
| 旧 | 开球 + 2 链盘 | `C(4,2)=6` | strict-hub 旧判据（geometry §3 open 语义）；对应 H4 |
| **ν1** | **1 中央盘 + 2 链盘** | `2·C(4,2)=12` | H2/H6 |
| **ν2** | **2 中央盘 + 1 链盘** | `C(4,1)=4` | H3/H6（"两 central 的 4 triples"） |
| **ν3** | **开球 + 1 中央盘 + 1 链盘** | `2·4=8` | H5 |
| **ν4** | **开球 + 2 中央盘** | `1` | H5（"加 1"） |

⇒ **含中央盘的三元素共 25 个**（`2·C(5,2)+C(5,1)=25` ✓，与 7 集合的自动计数一致）；其中含**两个**中央盘的
三元素 = `4 + 1 = 5`（即 lead 问的 `4 triples 加 1`）。**配对**（≤2 元）另有 H1–H4 覆盖（本件不重列）。

**（b）本件对 geometry 两个 caveat 的补位（互补，不冲突）**
* geometry caveat (i)"放松可行 ≠ 精确可行（精确分支还需第三类 witness：`C_σ(a)` 不被被禁开盘覆盖）"：
  **本件 §2 的 (H2) uniform distal exclusion 正好把这一条在该区域内消掉**——(H2) 成立时放松纤维 = 精确纤维
  （§1 推论是**等式**），因此在这个 box 里不需要第三类 witness ✓。这也是本件与 H1–H6 的**接口点**：
  `(H2) 区间判定成立` ⟹ 可直接用 geometry 的 H1–H6（且其 (i) 项自动满足）。
* geometry caveat (ii) 退化层破坏闭性（`h∈{a,b}`、`y=0` 等）：本件不处理；区间证书里的"pin 内根选择/分支符号"
  由区间比较**显式判定**，一旦不确定即返回 `UNDECIDED`（不静默放行）✓。

## §5 消去 b 之后：a（2 维）上的有限条件（**只接 geometry 的固定-a 结构**）

三元素/配对非空判据在 R² 上都是闭式（= geometry A/B 的同一族器械）；**权威枚举是 geometry 的 H1–H6**
（本件不重推，仅说明其与上表的对应）：

* **H1/H3**（两 pin / 两动盘 `> 2r`）与 **H2**（pin–动盘 `> 2r`）：配对层，快速筛；
  对应 ν1/ν2 的必要配对条件 `|q_i(a)−p_j| > 2r`、`|q_0(a)−q_4(a)| > 2r`；
* **H4**（`|u| ≥ ρ+r`）：开球与单盘不相交（旧类，`u` = 该盘圆心）；
* **H5**（开球 + 两盘：`μ(a) ≥ ρ`）：对应 ν3/ν4 —— `min-norm( B(q_i(a),r) ∩ B(p_j,r) ) ≥ ρ`、
  `min-norm( B(q_0(a),r) ∩ B(q_4(a),r) ) ≥ ρ`；
* **H6**（三盘：`ψ(a) > r`）：对应 ν1/ν2 —— `MEC(q_i(a),p_j,p_k) > r`（锐角三点 = 外接圆半径判据；
  钝角分支由最长边 > 2r 的 H1/H2/H3 封住）、`MEC(q_0(a),q_4(a),p_k) > r`。

其中 `q_i(a) = mid(a,c_i) ± √(r² − |a−c_i|²/4)·n(a,c_i)`（显式；分支 = hub B 所在侧，区间可判）。
⇒ **b 的 2 维被完全消去**，剩下 `a ∈ K_A ∩ B_open(0,ρ)` 上的**有限**条件；与 geometry A/B（a 侧 strict-hub
可行性的有限析取）组合即得 2-hub 的凸 screen。**全程没有 CQ、也没有用到 quartic 消去**；在 (H2) 区间成立的 box 内，
geometry 的 caveat (i)（精确分支的第三类 witness）自动满足（§4(b)）。

## §6 未做 / 未决（诚实清单）

1. **不做全域**：§3 的证书是对**给定 ring box** 的判据（区间可证），本件只演示了候选附近 δ≲1.87e−3 与若干
   r 窗口；**没有任何全局覆盖或下界结论**。box 的**合法性**（C879 假设：每边唯一公共覆盖等距点；弧账本）不由本件检验。
2. **ν3/ν4 的开球细节枚举**未做（按 lead 指示留后）。
3. **a 上的有限条件未在本件实现**（§5 只给闭式形式与计数）；建议与 geometry 的 A/B 实现合并（已发协调消息）。
4. **A 片段偏松**（`q'_i` 包络半径 ≈0.089）是当前 δ 瓶颈；B&B 细分或"在 `K_A ∩ 球` 上直接包络 `q_i`"会改善。
5. 本件**不注册 claim**；C894 已被 lead retract，C895/C896 的复核/登记由 lead 处置。

## §7 与 C894/C896 的收尾（trace）

* **C894（retracted by lead）**：错在 (ii) 的包含方向。修正后接口 = §1 L1+L2(修正)+L3+推论；
  §1 推论（"区域 ∩ 远端盘 = ∅ ⇒ crescent = 单盘"）仍然成立——这正是 C896 的 (e) 与 §2 (H2) 使用的那一条，
  所以 **C896 的读数与结论不受影响**（C896 引用的应是本节修正版，而非被撤回的 (ii)）。
* **C895 不受影响**（quartic 不可消是独立的代数事实；本件进一步说明：**接口根本不需要消 quartic**）。
* 原先计划里的**"固定 saved rings 求 r 阈值"已放弃**（same-candidate saturation / fixed-ring 已知不锋利）。
