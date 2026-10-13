# 中央纤维的 **biconvexity**：解析对称性 + 小盒区间 pilot

> 写作用域：本目录（sole writer）。等级：**解析（对称性）+ 区间 pilot（标定过 C904）**。
> 证据：`central_fiber_biconvexity_pilot.py`、`out/central_fiber_biconvexity_pilot.json`。
> 只读输入：`n11/upper/certified_object.json`；约定与 `r20-gluing/r23_central_screen_audit.py`（C904 的器械）一致。

---

## §0 结论

1. **解析对称性**：中心面 `ρ(a,b,c_i)` 是三个顶点的**对称**函数（`a↔b` 任意交换不变）；product 恒等式
   `4y²(ρ²−r²) = F_in·F_out` 对**弦端点**对称，且把"哪个点是第三顶点"换掉即得另一个方向上的单盘约化 ✓。
   但**双向不是自动的**：两条链的 pin 数不同（FAN_A = pins 4..8 共 5 个；FAN_B = pins 0..3 共 4 个）、
   variance 权重不同（`WL` vs `WB=(1/2,1/2)`）⟹ `ε_A = 0.0617` vs `ε_B = 0.0674`、参考点不同（`bB` vs `aA`）✓。
2. **区间 pilot（小盒，未放大规模）**：
   * **标定**：我独立实现原方向（弦 `(a ∈ KA, C_i)`、参考 `bB`）得
     `G(face_0) = 0.024568665543`、`G(face_4) = 0.024540121682` —— 与 C904 报告的 `>0.0245686 / >0.0245401`
     **一致到 7 位** ✓（器械可用）。
   * **镜像方向**（弦 `(b ∈ KB, C_i)`、参考 `aA`，即交换 a,b 后的 distal 排除）：
     `G'(face_0) = 0.047558593752 > 0`、`G'(face_4) = 0.048043973822 > 0` ✓（两面的 far 分支符号在盒上**一致可判**，
     无 straddle ✓）。
3. **因此**：在 `KA × KB` 上，中心纤维的可行集（经 C879 pin 盘约化 + far 分支排除后）**在每个变量上都是圆盘约束**
   ⟹ **biconvex**（两个中心面各给一个 b-圆盘与一个 a-圆盘；交集仍是 biconvex ✓）。
   **仍非 joint convex**（两个圆盘的圆心随另一变量移动 ✗）。
   **更正（lead 指正，撤 dimension claim）**：固定 `b` 时 `a`-可行集是 **2D 凸集**（`R²` 中若干圆盘之交），
   固定 `a` 时 `b`-可行集同样是 **2D 凸集**；**biconvex 不自动降为 1D 扫描** ✗——它把"联合可行性"化为
   "一族 2D 凸可行性"（可用于投影/包络/不动点式分析），维数仍是 2 ✓。

---

## §1 解析部分：对称性与它**不**给出的东西

* 记中心面为 `ρ(a,b,c_i)`（顶点 = 两 hub + 一个 central ring center）。`ρ` 对三顶点对称 ✓，故
  `ρ(a,b,c_i) ≤ r` 本身在 `a↔b` 下不变 ✓——**约束的对称性不蕴含每个变量的凸性** ✗。
* product 恒等式（C879/C905 家族）：取弦（两个固定点）与第三顶点 `v`，`y` = `v` 到弦线的有符号高，
  `F_in = |v − pin|² − r²`、`F_out = |v − pout|² − r²`（`pin/pout` = 半径-r 两圆在弦端点处的两个交点）：
  `4y²(ρ²−r²) = F_in·F_out` ✓。故 `ρ ≤ r ⟺ F_in·F_out ≤ 0`（`y ≠ 0`）——**一般情形是"两个圆盘的对称差" ✗ 非凸**。
* **单盘约化（C904/C900 的关键）**：若另有区域保证 `F_out > 0`（"far 分支被排除"），则 `ρ ≤ r ⟺ F_in ≤ 0`
  ⟺ **一个圆盘** ✓ 凸 ✓。C904 证明的正是"对 `(a,b) ∈ KA × KB`，以 `(a, C_i)` 为弦、`b` 为第三顶点时 `F_out > 0`"
  （统一 margin `0.0245`）⟹ **b-方向**的可行集是圆盘 ✓。
* 反过来（**a-方向**）需要把角色换成：以 `(b, C_i)` 为弦、`a` 为第三顶点，far 分支同样被排除 ✓——
  这不是 C904 的字面内容（弦不同、参考点不同、`ε` 不同）✓，故必须**独立验证**：本文 §2 的镜像 pilot ✓。
* 两个方向的 far 分支排除都成立 ⟹ 每个中心面给出
  `b ∈ B(pin(a,C_i), r)`（固定 a）与 `a ∈ B(pin'(b,C_i), r)`（固定 b）
  ⟹ 该约束 biconvex ✓；两个中心面取交仍 biconvex ✓（截口 = 凸集的交 ✓）。
* **退化 loci 的显式处理（lead 要求：不靠"domain 外空真"）**：
  (i) **`k = 0`（弦长 `|u| = 2r`，两半径-r 圆相切）**：`pin = pout = m`，双分支塌缩、单盘约化退化 ⟹ 必须**排除**：
      本 pilot 显式要求盒上 `rad = r² − |u|²/4` 的**下界 > 0**（即 `k > 0` 一致成立），否则报 `UNDECIDED`（§2 给出实测下界）✓。
  (ii) **共线 locus（`a, b, c_i` 共线 ⟹ 中心面退化、`ρ = +∞ > r` 不可行）**：这里**不是**"域外空真"——
      共线的 `a` 完全可以在盒内。显式论证：若 `a` 与弦 `(b, c_i)` 共线，则到两个圆-圆交点 `q_in', q_out'` 的距离**相等**
      （`|a − q'|² = |a − m'|² + k'²`，`m' = (b+c_i)/2` ✓），故 `F_in = F_out`；而认证的 far 排除给出 `F_out > 0`
      ⟹ `F_in > 0` ⟹ **近盘条件也失败** ✓ ⟹ 共线 stratum 上"近盘条件"与"`ρ ≤ r`"**同假**，两者一致，**无缺口** ✓
      ⟹ 可行集 = `KA ∩ 近盘`（无需额外删除共线集，因为它本就被排除在圆盘之外 ✓）。

---

## §2 区间 pilot（小盒，标定 + 镜像）

参数与 C904 完全一致：`delta = 1/1000`（ring 盒半宽）、`omega = 1/10000`（r 盒半宽）、
`r0 = 3799838531198387090485182/10^25`；ring 用保存的有理中心（`certified_object.json`，`NEW2RAW_RINGS` 重排）；
严格 hub 球用闭包 `B(0, 1−r)` 做包围；`KA`、`KB` 各为矩形（其构造与 C904 同：variance 盘 ∩ pin 盘 ∩ 严格球）✓。

| 方向 | 弦盒 | 第三顶点/参考 | 判据 | 读数 |
|---|---|---|---|---|
| 原（C904） | `a ∈ KA` | 参考 `bB` | `G = dist_lo(q_far, bB) − ε_B − r_hi` | `face_0: +0.0245687`、`face_4: +0.0245401` ✓（= C904） |
| **镜像** | `b ∈ KB` | 参考 `aA` | `G' = dist_lo(q_far', aA) − ε_A − r_hi` | `face_0: **+0.0475586**`、`face_4: **+0.0480440**` ✓ |

* `q_far`（resp. `q_far'`）= 半径-r 两圆交点中、位于参考点**反向侧**的那个 ✓（`sref = det(u, ref − A)` 的符号在
  盒上严格一致，无 straddle ✓）；`dist_lo` = 盒上一致下界 ✓；`ε_A ≤ 0.0617173`、`ε_B ≤ 0.0673723` ✓；
  `|bA| + ε_A = 0.21379`、`|bB| + ε_B = 0.37591` 均 `< 1 − r = 0.619916` ✓（严格 hub 条件在盒上成立 ✓）。
* 结论（区间）：对**一切** `a ∈ KA`、`b ∈ KB`：`|q_far'(b) − a| > r` ✓（且原方向也成立 ✓）
  ⟹ 两方向的 far 分支排除统一成立 ⟹ §1 的单盘约化在两个变量上同时生效 ⟹ **biconvex on KA × KB** ✓。

**冻结核（v1，SHA256）**：`central_fiber_biconvexity_pilot.py` =
`7c9951adadcb47dad7d2ed6b097a42f07333bd187760048bcfa15d93652d84df`（14111 B）；读数 json 哈希见
`out/frozen_kernel_hashes.json` ✓。本轮按 lead 源码 audit 修了三处缺陷并 freeze：
(1) **pin 选择不允许无条件 `else`**：改为充分 guard（`n1_hi<1≤n2_lo` / `n2_hi<1≤n1_lo` / `n1_hi<n2_lo` /
`n2_hi<n1_lo`），否则 **`raise UNDECIDED`**（实测 9/9 由 `p1 smaller norm` 判定 ✓）；
(2) **`sqrt_iv`**：上端 `<0` 直接 **fail（domain invalid，不静默返 0）**，下端 `<0≤` 上端时给合法外向包围并记入
`negative_radicands` 台账（实测 0 条 ✓）；
(3) **`bbox_inter` 判空**：`x0>x1` 或 `y0>y1` 即 **`raise`（inverted box）** ✓；
另 **radicand 台账**改为调用后填账（修时序 bug）：4 次检查、radicand 下界最小值 `−0.00275659`
（⟹ **原方向盒内含 `k=0` stratum**，已显式标注 + 由 strict-gap/equality 论证排除 ✓；
`mirrored_k_strictly_positive = True` ✓ 镜像方向 `k>0` 处处成立）。

**边界与口径（不得越界）**：
1. 这是 `KA × KB`（**条件 ring 盒**，非全 Cartesians 域）上的结论；C904 的同样限定 ✓。
2. biconvex ≠ joint convex；本文**不**主张联合凸性，也不主张任何全局结论 ✓。
3. 数值上的"far 分支选择"依赖盒上符号一致（本 pilot 检查通过 ✓）；若放大盒宽或换数据，必须重跑（同一脚本）✓。
4. 本 pilot 只做**两个中心面**（`CENTRAL = {0,4}`）与两 hub 方向；fan 面由 C879 的 pin 盘闭式覆盖 ✓（不在本轮重复）。
5. 我的实现在原方向与 C904 的读数一致到 7 位（标定 ✓）；镜像方向是本轮新增的独立读数 ✓。

---

## §3 复现

```
py -3 -B -X utf8 research-2026/team-current/r20-stress/central_fiber_biconvexity_pilot.py
```
（同样代码只读 `n11/upper/certified_object.json`，只写 `r20-stress/out/`；改盒宽改 `DELTA/OMEGA` 即可。）
