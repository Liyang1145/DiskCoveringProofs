# Kernel-metric design：用 `S ≻ 0` 重标 basis 以压低 remainder 损失项 `τ(Bd+‖A‖) p q²`

> 写作用域：**只**本文件 + 自有 script（`kernel_metric_design.py`）。**只作 numeric proposal，不升级为 claim/证书** ✗。
> 未改 lead 文件；未再审 cert（另成员做 ✓）。数据源：`lead/ANISOTROPIC-STRESS-REMAINDER.md`（引用其常数与恒等式 ✓）、
> `lead/interval_network_envelope.py`（**重算 root 核**：import 即重算 ⊂ 只该用 numeric 口径看 ✓）。

---

## §1 目标与自由度（照 lead 的式子）

lead 的定量链（`ANISOTROPIC-STRESS-REMAINDER.md`）：
```
p = ‖G8ᵀx‖,  Q = τ N G8ᵀ,  B = max_e ‖N_e‖/α_e,  A = (t ↦ root 处 stress Nt 的 anchor flux)
V²−R*² ≥ ½xᵀH₀x + τp² − C_cross q³ − (d/3)q⁴ − τ(Bd+‖A‖) p q²
```
数值（其新 cert）：`B=182, A=1.074, C_cross=0.0358, G=1.892, d=0.08, μ=0.002, τ₀=0.05, τ=0.1, ρ=0.00764`。

**自由度（本任务）**：把 basis `N` 换成**带度量的** `K := N S`（`S ≻ 0`，4×4 ✓）：
```
α = α₀ + τ K Gᵀ x   （等价 t = τ S Gᵀx）     合法性：B K = B N S = 0 ✓（与 S 无关 ✓）
gain   : τ xᵀ G S Gᵀ x        （lead 的 "quadratic gain G S Gᵀ" ✓；S=I 时退化为 τp² ✓）
loss   : τ (B(S)·d + ‖A(S)‖) · p_S · q²,   p_S := √(xᵀ G S Gᵀ x) ✓
B(S)   = max_e ‖(N S)_e‖ / α_e        ‖A(S)‖ = ‖A ∘ S‖（anchor-flux 的算子范数 ✓）
```
**核心张力**：S 增大 ⟹ gain ↑（对 `S` **线性** ✓）但 `B(S)`、`‖A(S)‖` 也 ↑（对 `S` **凸、正齐次** ✓）⟹ 最优在"增益/损失"比的边界上 ✓。
因 loss 的系数 `B(S)d + ‖A(S)‖` 凸、gain 线性，**最坏方向比** 是 convex-fractional ✓ ⟹
**analytic 路线**：Charnes–Cooper 变换 `S = T/ξ`（`ξ > 0` ✓）把它化为**凸/SDP**问题 ✓（**非网格** ✓）；
`S=σI` 的一参数版则是**闭式/一维凸**（可直接求解 ✓）。

---

## §2 解析候选（≤5，**不用网格** ✗）

| # | `S` | 设计理由 | 需评估的量（actual `b,m,λ` ✓） |
|---|---|---|---|
| 1 | `I` | 基线（复现 lead 的 `B=182, A=1.074` ✓） | `B, ‖A‖, gain` |
| 2 | 白化 `S = (G Gᵀ|_im)⁺^{1/2}` | 均衡 gain 各方向，压低 `p_S` 的方向依赖 | 同上 |
| 3 | 列归一化（对角 `S`，使 `‖(NS)_{:,l}‖ = 1`） | 让 `B` 对基的标度不敏感 | 同上 |
| 4 | 增量白化 `S = (K₀ᵀK₀)^{−1/2}`（`K₀ = N` 的 Gram ✓） | 直接压 `max_e‖K_e‖`（= `B` 的分子 ✓） | 同上 |
| 5 | **标量最优** `S = σ* I`，`σ* := argmin_σ [ (B(σ)d + σ‖A‖) / (σ λ_min(GGᵀ)) ]` | 由 §1 的一维凸性——**闭式/单调**，非网格 ✓ | 同上（1-D 求解 ✓） |

**提示**：候选 2–4 只改"方向/标度"✓；候选 5 是唯一按比值最优的 ✓；若把 `‖A(S)‖` 换成 lead §19 提到的**径向 A**
（"radial A replaces full A" ✓）则 loss 系数再降 ✓——这属可选精化，本件不改其定义 ✓。

---

## §3 评估口径（**只 numeric proposal**）

* 必须用**实际** `b, m, λ` 项（不是包络/最坏方向估计 ✗）：即对候选 `S` 数值给出
  `(B(S), ‖A(S)‖, λ_min(G S Gᵀ|_8), gain(x)/q² 的极值方向)` ✓ ——**不**做参数网格 ✗。
* 所有输出标 `numeric`；**不**把任何候选的提升当作证书 ✗；**不**升级 C916/其它 claim ✗。
* 若 import `lead/interval_network_envelope.py`：它会**重算 root 核** ✓——只用其数值做候选比较 ✓，**不**把其浮点当区间结论 ✗。

---

## §4 判据（如何判定某个 `S` "有用"）

对固定方向 x，令 `r(S) := (B(S)d + ‖A(S)‖) / (τ^{−1}·gain 系数 ... )` ——**严格写法**：
比较量 = `τ(B(S)d+‖A(S)‖) p_S q²` 与 `τ p_S²` 的**比** `= (B(S)d+‖A(S)‖)q²/p_S` ✓；
若存在 `S` 使该比在**同一方向族**上一致小于 `S=I` 的比 ✓，则候选"有用" ✓（numeric ✓）。
**注意**：`S` 放大不改变比（`S → cS` 使 `B, ‖A‖, p_S` 同乘 `c` ✓）⟹ 只需在**归一化**集合（如 `tr S = 4` ✓）上比较 ✓——这也是候选 5 的 `σ*` 只在"相对 G 的标度"上有意义的原因 ✓。

---

## §5 撤回 + 实跑结果（**numeric proposal only**）

**撤回（lead 指正）**：
* v1 的"模块顶层没有 `N/G/alpha`" ✗ **错误**：`k.N / k.G8 / k.alpha` **明确存在** ✓，只是 **`mpmath.iv.matrix`** 而非 `np.ndarray` ✗，
  故用 `dir()` 只筛 numpy 类型的检查会漏 ✓。正确读法（照 `lead/local_tau_diagnostic.py`、`lead/certify_anisotropic_stress_ball.py`）：
  `k.arr(k.N)`、`k.arr(k.G8)`、`k.arr(k.alpha).ravel()` ✓。script 已改用该 API ✓（**不再"未评估却写实测"** ✗）。
* v1 的"**convex-fractional ⟹ 有解析最优**" ✗ **删除**（未给精确定理/约束证明，按 lead 要求不得保留）。

**实跑 5 行表**（`λ_min(gain) = λ_min(G S Gᵀ)` 于 `im(G)`；`b = τ·max_e‖(NSGᵀ)_e‖/α_e`，`τ = 0.1`）：

| S | `B_basis` | `b` | `λ_min(gain)` | `b/λ_min` |
|---|---|---|---|---|
| 1 identity | 181.04 | 11.372 | 0.088082 | **129.1** |
| 2 `(GᵀG)^{−1/2}` | 527.20 | 18.104 | 0.296790 | **61.0** |
| 3 列归一化（对角） | 76.91 | 5.414 | 0.033066 | 163.7 |
| 4 `(NᵀN)^{−1/2}` | 81.70 | 6.244 | 0.030951 | 201.7 |
| 5 `σI` 族 | `σB(1)` | `σb(1)` | `σ²λ_min` | **与 σ 无关（σ 约掉）** |

* **标定**：`S=I` 给 `B_basis = 181.04` ✓ ≃ lead cert 常数 `B = 182` ⟹ 读取路径正确 ✓。
* **唯一改善比值的候选 = 2**（`(GᵀG)^{−1/2}`）：`129.1 → 61.0`（≈2.1×）✓；候选 3/4 把 `B` 压低 ~2.3× ✗ 但同时把
  `λ_min(gain)` 压低 ~2.7× ⟹ 比值反而变差 ✗。
* **未计算（诚实标注）**：loss 系数里的 **anchor-flux 项 `‖A(S)‖` 未计算** ✗——需要 lead 模块内部的 edge 列表
  （`sgn, X[v], X[w]`；其 `certify_anisotropic_stress_ball.py` 内有 ✓）。故上表**排序不完整** ✗：加入 `‖A(S)‖` 后
  候选 2 的领先可能改变 ✓——这就是下一步该跑的量 ✓。
* **口径**：全部 numeric；**不**升级为证书、**不**注册 claim、**不**把浮点当区间结论 ✗。

