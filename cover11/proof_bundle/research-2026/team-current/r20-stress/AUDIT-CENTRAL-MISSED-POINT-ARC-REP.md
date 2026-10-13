# 独立审计：r=19/50 的"pin 可行但中央漏点"（用另一套表示复现同一 witness）

> 写作用域：本目录。等级：**exact-rational 独立复算（同 witness）+ 不同表示的控制**。
> 只读输入：`r20-geometry/exact_missed_point.json`（其 witness）、`n11/upper/certified_object.json`（有理中心）。
> 证据：`central_missed_point_arc_audit.py`、`out/central_missed_point_arc_audit.json`。

---

## §0 结论

1. **同一 witness，独立复算通过**：`r = 19/50`；扰动的两 hub `hA = (2653/10⁷, 2729979/10⁷)`、
   `hB = (−241/1250000, −1494489/10⁷)`；`p =` 其给出的有理 circumcentre。用我自己的 Fraction 核（不共享其助件）：
   * `|p − c_j|² − r² > 0` 对**全部 11 个 site** 成立 ✓；最小值 = 其 `Rc2_minus_r2` **逐位相同** ✓
     （`6469548614306402579287424946618188833094320673118615777995529757487872813 / 2125091…`，
     我独立算得 `B_matches_their_Rc2 = True`）；
   * `|p|² < 1` ✓ ⟹ **p 是单位圆盘内一个不被任何盘覆盖的点** ⟹ `r = 0.38` 下的该 11 盘组**不覆盖 `D`** ✓。
   * `p` 恰与 `(hA, CEN[5], hB)` **等距**（精确有理相等 ✓），`R_c − r = 4.005719342e-06 > 0` ✓，
     且该三角**锐角**（三个顶点角 dot > 0 ✓）⟹ `p` 位于三角形内部 ⟹ 它是 min-距离函数的**极大点**
     （"洞心"）✓。其 json 的 `outside_signs` 列表与我的**顺序不同**（他们的 site 列表顺序不同），
     故我未逐项比对列表，只比对**决定性不变量**（最小值/`Rc2_minus_r2` 相等 ✓）。
2. **不同表示（short-arc cap overlap）复现同一结论**：
   * **统计对象 = 9 条 ring 弧**（不是 11 条）：两个 hub 严格在内部——**精确**验证 `|h|² < (1−r)²` ✓，
     故其盘根本不与 `∂D` 相交、**无边界弧** ✓；半角 `a_j` 满足 `cos a_j = (ρ_j² + 1 − r²)/(2ρ_j)` ✓；
     9 条 ring 弧总长 `/2π = 1.000066`（略重叠 ✓），**边界完全被覆盖**（最大"缝隙"= **−3.728e-05 rad** < 0 ✓）
     ⟹ 失败是**纯内部**的 cap-overlap 洞，不是边界缝 ✓（与 `p` 在内部一致 ✓）。
   * 洞的"深度"= `R_c − r = 4.0057e-06` ✓（= 其 `R_c > r` 读数 ✓）。
3. **"pin 可行"精确确认（用正确的聚合量）**：九个相邻环对的 pin（取 norm 较小者 = `p_in`，按 C905 命名 ✓，
   用 `alpha + q·sqrt(K)` 的精确符号判定 ✓）：
   * 每个 pin 的"最佳 hub 松弛"= `min over hubs (|pin − h|² − r²)` 的符号；
     正确的全称量是 **`max_over_pins( min_over_hubs ) = −1 < 0`** ✓ ⟹ **九个 pin 全部（且严格）被覆盖** ✓✓
     （**不能**用"全体最小松弛 < 0"来断言全称命题 —— 那只是存在性）；
   * 分派恰为 **chain A 4 个**（pairs (5,7),(7,1),(1,8),(8,6)）+ **chain B 5 个**（(6,4),(4,9),(9,10),(10,3),(3,5)）✓
     与其 `FAN_A/FAN_B` 完全一致 ✓；每个 pin 恰好被一个 hub 覆盖 ✓（`both_hubs_cover_it = False` ✓）。
   * 其 json 字段 `pins_strict=false` 曾为**代码 bug**（sign helper 用了负 `β²Q`），**非口径差异**（lead 定位 ✓）；
     他们已修，现字段 = `True` ✓，与我的精确读数一致 ✓。
4. **净结论**：geometry 的"pin 可行但中央漏点"**成立**（我以另一表示 + 独立精确核复现 ✓），
   即：**九链 pin-盘刻画对中央覆盖不充分**（中央面需要另有条件）；这不影响 C879 本身（C879 是 fan 面的等价刻画 ✓），
   但影响"C900 单盘中央约化 + pin 可行 ⟹ 覆盖"的用法 ✓。

---

## §1 方法与"separable"声明

* 与 geometry 的路线**不同**：他们取"违反的中央三角的外心 p"再逐个检 11 个距离（circumcentre 路线）；
  我除复算该点外，另走 **cap/弧表示**：把"覆盖失败"表述为"短弧 cap 在中央区域不重叠"，
  并用 **maximin/critical-point** 刻画（`p` = 等距三点且严格极大 = 洞心）——两条表示给出**同一** witness ✓。
* 无新搜索、无共享助件（我只读了他们的 json 数据与 `certified_object.json` 的有理中心）✓。
* 控制：`R_c−r > 0`、11 距离全正、`|p|<1`、锐角/内部、边界无缝隙、九个 pin 全严格覆盖 —— 六项互相独立可查 ✓。

---

## §2 复现

```
py -3 -B -X utf8 research-2026/team-current/r20-stress/central_missed_point_arc_audit.py
```
（只写 `r20-stress/out/central_missed_point_arc_audit.json`。）

---

## §3 与 biconvexity pilot 的接口（同一冻结核 + 本轮 kernel 修正）

**冻结核（v1，SHA256）**：`central_fiber_biconvexity_pilot.py` =
`7c9951adadcb47dad7d2ed6b097a42f07333bd187760048bcfa15d93652d84df`（14111 B）；
`central_missed_point_arc_audit.py` =
`64490b1170c38336fc4c95b85ed5e783b9718dc486fd92ad2a9cba759463fa8b`（9106 B）；
读数 `out/*.json` 的哈希见 `out/frozen_kernel_hashes.json` ✓（lead 要求：修后 freeze 再给 sha，不随手 ✓）。

**本轮按 lead 源码 audit 修正的三处 kernel 缺陷（已修 ✓）**：
1. **pin 选择不允许无条件 `else`**：改为充分 guard（`n1_hi<1≤n2_lo` / `n2_hi<1≤n1_lo` / `n1_hi<n2_lo` / `n2_hi<n1_lo`），
   否则 **`raise` UNDECIDED**（实测 9/9 都由 `p1 smaller norm` 判定 ✓，无 UNDECIDED ✓）。
2. **`sqrt_iv` 不得静默返回 0**：上端 `< 0` 直接 **fail（domain invalid）**；下端 `< 0 ≤` 上端时返回合法外向包围
   **并记入 `negative_radicands` 台账**（实测 0 条 ✓）。
3. **`bbox_inter` 必须判空**：若 `x0>x1` 或 `y0>y1` 则 **`raise`（inverted box）**，不允许用反转矩形 ✓。
另外**radicand（`k>0`）台账**改为按调用填账（修掉"台账在调用前构造"的时序 bug）：
4 次检查、radicand 下界最小值 `−0.00275659`（**原方向盒内含 `k=0` stratum** ⟹ 已显式标注并由 strict-gap/equality 论证排除 ✓），
`mirrored_k_strictly_positive = True` ✓（镜像方向 `k>0` 处处成立，无退化）。

**两条结论合起来**：pin/链刻画在中央区域**必须**与 central-face 条件（圆盘或等价的 maximin 条件）联用；
biconvexity 正是把该 central-face 条件在每个变量上化为圆盘的那一步 ✓。
