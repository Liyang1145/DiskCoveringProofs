# 中央面 SOC 化的**解析审计** + 对偶不可行 witness 形式（fixed rings ⟹ no hub）

> 写作用域：本目录。等级：**纯解析**（按 lead 指示：不写区间代码、不重复器械；acute 读数等 alternative）。
> 输入假设：C904 盒上两 central triangles（`(a, b, c_0)`、`(a, b, c_4)`，`a∈KA, b∈KB`）**uniformly acute**。

---

## §0 结论（六条）

1. **两件不同的事必须分开**：真实中央条件 = **circumradius ≤ r**（洞在 *circumcentre* 上）；凸代理 = **MEC ≤ r**
   ⟺ SOC 可行（`∃z_i: |z_i−a|,|z_i−b|,|z_i−c_i| ≤ r`）。二者只在**非钝角**三角形上等价 ✓。
2. **必要性无条件成立**（不需要 acute）：circumradius ≤ r ⟹ 三点都落在 `B(circumcentre, R_c) ⊆ B(·, r)` ⟹ SOC 可行 ✓✓。
   故 **SOC 不可行 ⟹ 中央条件必失败** ⟹ 对偶不可行 witness 是**无条件**证书 ✓（见 §3）。
3. **充分性需要 acute**：`MEC ≤ r ⟹ circumradius ≤ r` 仅当三角非钝角 ✓（钝角时 `MEC = 最长边/2 < R_c` ✗）。
   故 joint-convexity 突破（把 SOC 当中央条件用）**必须**带 uniform-acuteness；这正是 alternative 在读的量 ✓。
4. **convexity 是 joint 的（不是 biconvex）**：集合 `{(a,b,z_0,z_4)}` 是 `|z_i − a| ≤ r` 型约束（`(a,z_i)` 的凸集，
   作为线性映射 `(a,z_i) ↦ z_i − a` 的球原像 ✓）与盒约束的交 ⟹ **凸** ✓ ⟹ 投影到 `(a,b)` 也凸 ✓✓。
   （这比我上一轮 biconvex 强一级：joint convex ⟹ 可做 SOC 可行性/对偶，不需 envelope ✓——按 lead 指示**停** biconvex envelope。）
5. **退化分类（必须显式，不得靠域外空真）**：
   * **直角**三角：`MEC = R_c`（`= 斜边/2` ✓）⟹ 等价**仍成立** ✓（无需排除 ✓）。
   * **钝角**：`MEC < R_c` ⟹ 等价失败 ✗ ⟹ 若盒内含钝角点，SOC 只给**必要**条件（对"证不覆盖"仍足够 ✓，对"证覆盖"不够 ✗）。
   * **共线**（degenerate）：`R_c = +∞`（面条件必失败 ✓）而 `MEC = 最长距离/2`（有限 ✗）⟹ 等价失败 ✗；
     但**该 stratum 已被排除**：我在 `CENTRAL-FIBER-BICONVEXITY.md` §1(ii) 已认证——共线时到两圆-圆交点距离相等
     ⟹ `F_in = F_out`，而认证的 far-margin（`G' > 0`）迫使 `F_in = F_out > 0` ⟹ 近盘条件也失败 ⟹ 共线点在 `KA×KB`
     内**不可行** ✓（不是"域外"，是显式排除 ✓）。
   * **`k = 0`（弦长 = 2r，两半径-r 圆相切）**：原方向盒内含此 stratum（radicand 下界 `−0.00275659`，已标注 ✓），
     镜像方向 `k>0` 处处成立 ✓；`k=0` 时 `pin = pout` 使单盘约化退化，须用 strict-gap/equality 论证排除 ✓（C904 control 已有 ✓）。
6. **范围**：本审计只给**逻辑关系**（等价/必要性/凸性/退化分类）；**不**主张盒上真的 uniform acute（那是 alternative 的读数），
   **不**主张 no-hub 已被证明（§3 只给证书**形式**）。

---

## §1 等价链（写成可逐行核对）

记三点 `p_1=a, p_2=b, p_3=c_i`，`MEC(p) = min_z max_j |z − p_j|`。

* **(N) SOC 是面条件的松弛（方向必须写对）**：
  * **事实 1（无条件）**：`R_c ≤ r ⟹ MEC ≤ r` ✓——过三点的圆 `∂B(z_c, R_c)` 本身就是一张覆盖三点、半径 `R_c ≤ r` 的盘 ✓。
    故 **SOC 可行是面条件的必要条件** ✓✓；其 **contrapositive：SOC 不可行 ⟹ 面条件必失败** ✓（**无条件**，不需要 acute ✓）。
  * **事实 2（需要非钝角）**：`MEC ≤ r ⟹ R_c ≤ r` 只在非钝角时成立 ✓；反例（钝角/近共线）：三点近似共线且彼此相距 `0.2`，
    则 `MEC ≈ 0.1`（可取 `r = 0.4` 使 SOC 可行 ✓）而 `R_c` 巨大 ✗ ⟹ **SOC 可行不能推出面条件** ✗（除非 acute ✓）。
  * 故：**证"不覆盖/无 hub"** 用事实 1 的 contrapositive（稳 ✓）；**证"可用/有 hub"** 必须借助 uniform acute ⟹ `MEC = R_c` ✓。

* **(S) 充分性 = 经典事实**：非钝角三角：`MEC = R_c` ✓（锐角：极小圆过三点 ⟹ `ρ* = R_c` ✓；
  直角：`ρ* = 斜边/2 = R_c` ✓）。钝角：`ρ* = 最长边/2 < R_c` ✓。共线：`ρ* = 直径/2`，`R_c = ∞` ✓。

---

## §2 uniform acute 假设要覆盖什么（供 alternative 的读数使用）

1. 必须对**两个** central faces（`i = 0, 4`）与**所有** `(a,b) ∈ KA × KB` 成立 ✓（含盒边界 ✓；
   等价类在闭盒上封闭 ✓，故"闭盒上非钝角 + 内部严格锐角"即够 ✓）。
2. 只需"非钝角"即可（直角允许 ✓，见 §0.5）；若读数只给"严格 acute"则更强、更安全 ✓。
3. 读数需带**统一 margin**（例如所有顶点角 ≤ π/2 − δ ✓，δ > 0）——否则盒边界上的直角点会让等价在该点退化 ✓
   （退化点本身无害：直角处 `MEC = R_c` ✓ 等价仍成立 ✓；但若读数只覆盖开盒内部，则边界需另证 ✓）。
4. **不需要**排除共线：共线 stratum 已被 far-margin 排除 ✓（§0.5）；`k=0` stratum 已有 strict-gap 论证 ✓。

---

## §3 对偶不可行 witness 形式（SOC support；exact、simple）

**引理（variance / SOC 对偶）**：若点集 `{p_j}` 满足 `∃z ∀j: |p_j − z| ≤ r`，则对**任意**权重 `w_j ≥ 0, Σw_j = 1`：

```
V_w(p) := Σ_j w_j |p_j|² − |Σ_j w_j p_j|²  ≤  Σ_j w_j |p_j − z|²  ≤  r²          (★)
```

（第一步：`Σw_j|p_j−z|² = Σw_j|p_j|² − 2⟨z, Σw_jp_j⟩ + |z|² = V_w + |z − Σw_jp_j|² ≥ V_w` ✓（均方方差恒等式）✓；
第二步：每个 `|p_j − z| ≤ r` ✓。）⟹ **contrapositive**：`V_w(p) > r²` ⟹ **SOC 不可行** ⟹ 中央条件失败 ✓（§1 (⟸) 的 contrapositive ✓ **无条件、不需要 acute** ✓✓）。

**"simple exact dual infeasibility witness"的具体形式（利于 fixed rings 证 no hub）**：
* 取**有理**权重（例如 `w = (1/3,1/3,1/3)`，或按其链结构取 `WL/WB` 型有理权重 ✓）；
* 因为固定 rings ⟹ `c_0, c_4` 是**常数**，`V_w(a, b, c_i)` 是 `(a,b)` 的**凸二次型**（`= λ_a|a|² + λ_b|b|² + λ_c|c_i|²
  − |λ_a a + λ_b b + λ_c c_i|²`，`λ` = 权重 ✓）✓；
* 于是 `min_{(a,b) ∈ KA × KB} V_w(a,b,c_i)` 是**盒上凸二次极小**（闭式：梯度 = `2` 倍一个线性映射，
  极小点 = 无约束解 clamp 到盒上，取值为有理 + 至多一个 `sqrt(有理)` ✓，或直接用有理下界 ✓）；
* **若该极小值 `> r²`，则 fixed rings 下 no hub** ✓✓——证书 = `(w, 盒, 极小值下界)`，全部有理/闭式，
  且**不依赖 acute** ✓，也不依赖 biconvexity ✓。这类证书正是 SOC 对偶支撑（乘子只支撑在 `|p_j − z| ≤ r` 这些 SOC 约束上 ✓）。
* 反向提示：`V_w ≤ r²` **不是**充分条件（它只给"三点能被某张半径 `sqrt(V_w)` 的盘覆盖" ✗）；所以要证 *feasibility*
  必须回到 acute + SOC ✓（或直接构造 `z` ✓）。
* 与 C904 的关系：C904 的两 hub 定位 `KA/KB` 本身就是用 variance 权重（`WL/WB`）+ 链 pin 盘做的 ✓；
  本条把这些**同族**不等式反过来当**对偶不可行**使用 ✓，因此与既有器械同源、可复用 ✓。

---

## §4 我这一轮**不**做的事（按 lead 指示）

* 不写/不跑区间代码，不重复 acute 的机械读数（等 alternative ✓）；不继续 biconvex envelope（SOC 直接给 joint convex ✓）。
* 不注册 claim；本件是接口审计 + 证书形式，等 acute 读数到达后再与实际盒绑定（届时需声明：闭盒非钝角 ✓、
  统一 margin ✓、`k>0`/共线 stratum 的排除来源 ✓）。
