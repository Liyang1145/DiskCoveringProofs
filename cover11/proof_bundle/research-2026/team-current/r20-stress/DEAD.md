# r20-stress — DEAD（方法级负结果 / 实现失败 / 预算停止）

写作用域：本目录。**未注册 claim**。区分四类：① 被判死的数学命题；② 方法限（通道关闭 ≠ 命题为假）；
③ 实现失败（已修/未修）；④ 预算停止（不是结果）。

## ① 被判死的命题（有独立对照件）

1. **无限制命题 `min_{D_legal} max_i D_i ≥ r*` 为假**（M1 的充分不等式，20 次反例优化，最好见证
   `0.379430906080 < Tcert − 5.53e-4`；对照 = 独立重算 21 等式残差 + C840 条件 + 两个见证的合法性核验）。
   证据：`REPORT.md` §3、`out/mechanism_test.json`、`out/phase1_runs.json`、`out/cited_witness_check.json`。
   注意：**限制版** `min_{D_legal ∩ {R_shape<0.38}} max_i D_i ≥ Tcert` 既未证伪也未检验，仍开放。

## ② 方法限（不得升格为"命题为假"）

1. **"半径消除—亏损分解"cap 通道（M1）关闭**：合法 cap 的最小值就是真实半径（路径传播恰为 `u`），
   故该通道的值不可能超过 `q_i/max(u_{i−1},u_i) ≤ R`；要么恒等（无信息）要么有损。见 `REPORT.md` §2.2/§7。
2. **小奇异值 ≠ 秩亏；非零小奇异值也 ≠ 精确对象非驻点**（本轮更正）：`σ₁₈(M)=2.49e-11` 是 float64
   图表点的参数误差产物 ⇒ 不得写 `rank=17`，也**不得**"由 σ₁₈ ≠ 0 推出 TC 点不是精确 KKT 点"。
   见 `REPORT.md` §0(8)、`PHASE5-KKT-WEIGHTS-LIFT.md` A0.1/A0.7、`PHASE7-INTERVAL-CYCLIC-NU.md` §5。
3. **`R_shape = max_f b_f` 在 18 并列处没有普通梯度**：只有单侧方向导数；中心差分（任何步长）是
   混合量。`phase4c` 的 `dR_shape/dR = −1.658`、旧版 `Yt` lift、旧版「rank 17」都不得作为证据引用。
4. **不能靠全局凸性证明 (O1)**：`nonlinear_stress_convexity.py` 在距候选 0.15 处给出方向二阶导 −0.865
   （真负）。障碍是域的非凸结构（"全体半径同时缩水"方向），不是 logsumexp 光滑化假象。

## ③ 实现失败（已记录，避免重读为几何阻碍）

1. 第二轮的"21 维 reduced Hessian 有 10 个负特征值（min −4.82）"读数**作废**：只算了 `ZᵀH_ΦZ`，漏掉等式
   二阶 normal correction `Σμ_j∇²c_j`（lead 读码确认）。修正后 min = −0.3354（`PHASE3-LAMBDA-HESSIAN.md`）。
2. 第一阶段的 M1 见证全部落在 `R_shape ≈ 0.389 > 0.38`（域外）：该批"反例"对限制版**无**效力，
   只对无限制命题有效（`out/audit_scope_phase0.json`）。
3. 固定-λ 精化点丢失 18 条 tie（g-spread 8.2e-8，仅 1/18 保持）⇒ 不能当 sharp 候选使用。
4. `phase6_boundary_nu.py` 的坐标替换/符号 `sgn` 只在盒上**严格**可判时才用（本轮已核 9/9 严格）；
   若要扩展到更宽的盒，必须重新判符号而**不能**沿用中心点的 sgn。
5. `phase6b_nu_explicit.py` 的 `nu_12D` 列是把 5 个 orbit 代表值复制成 9 向量（成对项**未**除 2），
   与 per-gap 的循环公式值相差恰为因子 2（`max_diff = 0.025434`）。**两者都对，但口径不同**：
   循环公式给 per-gap ν，12D 对称空间解给 orbit 求和（= 成对 2 倍）。混用会把边界总权重放大 2 倍。
   本轮 `phase7` 同时输出两种口径并核对相等（区间相交）。

## ④ 预算停止（不是结果）

* 第一阶段：20 次反例优化用满预算后停止（`REPORT.md` §3）；当时未做全域扫描。
* 第三阶段：bounded（1 次 Jacobian + 1 次 Hessian + 1 个方向）后停止，等级 numeric。
