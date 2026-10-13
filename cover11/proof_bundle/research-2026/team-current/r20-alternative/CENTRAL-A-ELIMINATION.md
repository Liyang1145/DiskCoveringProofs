# CENTRAL-A-ELIMINATION —— 固定 nominal rings 时 b 消去后的 2D a-区域：最小多项式表述 / 度 / 域 / 退化，及凸性反例

> 路由 r20-alternative/cline2（sole write，no child）。证据/复现：`central_a_region.py` → `central_a_region.json`
> （`py -3 -B -X utf8 research-2026/team-current/r20-alternative/central_a_region.py`）。
> 输入：`n11/upper/certified_object.json` 精确有理圆心 + 保存的上界对象 UB*；q0 面表同前。
> **本件不注册 claim**；不主张全局；不触碰 geometry 线。

## §1 最小多项式表述（rings 固定）

固定环后，b-消去条件里与 `a` 有关的**唯一**非常数量是两条中央圆分支
`k_i(a) = sqrt(r² − |a−c_i|²/4)`，`i = 0,4`（`q_i(a) = (a+c_i)/2 + k_i·perp(c_i−a)/|c_i−a|`，分支 = 参考 b 点所在侧，保 orientation）。
其余量（pins `p_j`、`b_B`、`ε_B`、`ρ`、`r`）全是**常数**。于是：

* **变量**：`(x, y, k0, k1, s0, s1)`，`s_i = |a−c_i| > 0`；
* **关系**：`k_i² = r² − s_i²/4`、`s_i² = |a−c_i|²`（两条二次）；
* **度（脚本 [S]，sympy 实算）**：清掉正分母 `s_i` 后
  `|q0−p|²·s0`、`|q4−p|²·s1`、`|q0−q4|²·s0s1`、`cross·s0s1` **各为 4 次**（六元 `(x,y,k0,k1,s0,s1)`）。
  于是 H6 型 `max(a2,b2,c2) > 4r²` ⟺ `max(L0 s1, L1 s0, L01) > 4r² s0 s1`（≤4 次）；
  锐角三比较同法；锐角积支 `a2b2c2 > 4r²X²` ⟺ `L0 L1 L01 > 4 r² Xc²`（≤12 次）。
  ⇒ **quantifier elimination 原理上可用**（只需消两条二次关系），代价是边界是**1 维曲线**（见 §2）。
* **域**：`a ∈ K_A = B(0,1−r) ∩ ∩_{j∈{4..8}} B(p_j,r)`（凸），加 `k_i ≥ 0`、分支侧符号 `det(c_i−a, b_ref−a) ≠ 0`。
* **退化**：`k_i = 0`（`|a−c_i| = 2r`，两分支圆心合并；**注意**此处不能用 `ρ ≥ r` 排除，`ρ ≥ r` 不否定 `ρ ≤ r`——
  k=0 tuple 靠 **strict G** 排除：`q_near = q_far = m`）；`s_i = 0`（`a = c_i`，中央三角形退化，无外接圆半径）；
  分支符号为零（`a` 与 `c_i`、`b_ref` 共线）；loss 区（单盘等式只在 certified (H2) box 内成立）；
  `K_A` 的圆弧边界（部分盘活跃）。

## §2 撤回（lead 判定）与修正后的口径

**撤回两处越界**（本件上一版）：
1. 「crescent 不凸 ⇒ a-projection 不凸 ⇒ 无有限临界候选算法」**撤回**。§2 的有理反例只说明 *clause* 的形状是弧形；
   它**不**证 fixed-rings 的 a-projection（P = {a∈K_A : K_B∩D_0(a)∩D_4(a)∩B(0,ρ) ≠ ∅}，C904 branch 后的两个**中央盘**）不凸，
   更不证"有限临界候选算法不可能"。
2. 「四个轴向平移 1e−6 使 fiber 空 ⇒ 区域点状(<1e−6)」**撤回**：四方向空**不**蕴含包含于 1e−6 盒，也不证点状。

**保留**：§1 的多项式表述/度/域/退化清单（与被撤回的两条无关）。
**clause 形状仍是有用的**：对**固定 b**，|b − q_i(a)| ≤ r 在 a-空间恰是同一个 crescent 形状（三顶点对称），
所以凸性**不会自动成立**，必须用"F := K_B ∩ B(0,ρ) 固定且凸"＋联合 (a,b) 结构（例如 F 被钉住时）去证——
这是"一条解析路线"的内容。

## §3 r = 0.38（C904 window）固定 saved rings：K_A 严格内点 + ≤20 探针（central_a_projection.py/.json v2）

**先立条件（lead 要求，先条件后推导）**：固定 b 时，分支盘条件  ∈ D_i(a) = B(q_i(a),r) 只在
**避开远端盘**的区域上等价于精确 crescent 约束 ρ(a,b,c_i) ≤ r：
∀b∈R: R ∩ B(q'_i(a),r) = ∅ ⇒ 两者在 R 上一致；反向**不自动**成立（C894 被撤回的正是半平面方向，禁止使用）。
本节取 R := K_B ∩ B(b_B, ε_B)（ε_B = sqrt(r²−|p_0p_3|²/4)，权 1/2,1/2 的 variance 恒等式），
并对每个探针**逐点核验**该 distal 条件 ✓。

**K_A 严格内点（先 assert）**：pins 按 r = 0.38 重算，K_A = B(0,1−r) ∩ ∩_{j∈{4..8}} B(p_j,r)。
均匀内缩量 	* = 3.652806146e−5 > 0（对 t 二分、用有限候选判定 ∩B(c_i, r_i−t) ≠ ∅）⇒
**K_A 有真内点**；内点见证 z0 = (−0.000181945014531, −0.149404431917)，
其对**原始**盘的 min slack = 	*/2 ≈ 1.83e−5 > 0。另：候选 hub hA 本身 slack = 3.6032628e−5 > 0（也在 int K_A）。
⚠ **不主张**任何由数值相等得到的 min-norm 角点；JSON 里 K_A_witness_min_slack = 3.889e−62 是**收紧盘**的机器零
（= 	*/2 在机器精度下的读数），**不是证书**。

**探针（10 个，≤20 预算）**：z0 + 8 方向（步长 margin/3）+ hA；全部 in_K_A ✓、fiber nonempty ✓、distal 条件 ✓。
**凸性检查**：45 个两两中点**全部 fiber nonempty**（无空性证书可给）⇒ **无反例；凸性未证**（本轮唯一 decision 是
"counterexample: no"）。

## §4 结论（本轮可承重的）
1. **固定 saved rings + r = 0.38**：K_A 有**严格内点**（t* = 3.65e−5，见证 min slack 1.8e−5），且候选 hA 亦在内部（slack 3.6e−5）。
2. **fixed-rings a-projection 凸性**：≤20 探针内**无反例**（凸性未证）。要作决定需：(a) 把探针换成"K_A 内部更宽的成对取样 + 精确 Helly 空性证书"，或 (b) 走解析路线（F := K_B∩B(0,ρ) 固定凸 + 联合 (a,b) 结构）。
3. **口径**：先条件后推导（§3 顶）；不用 3.9e−62 类机器零作证书；不主张全局；不堆 digits。
