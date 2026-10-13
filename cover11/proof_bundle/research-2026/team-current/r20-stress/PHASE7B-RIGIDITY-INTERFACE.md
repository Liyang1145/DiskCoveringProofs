# PHASE 7B：给 r23-rigidity 的区间权重接口说明（import-safe）

写作用域：本目录（`r20-stress/`）。只读输入：`../lead/repaired_tc_krawczyk.json`。
本文件是**接口说明**；数学内容与证据在 `PHASE7-INTERVAL-CYCLIC-NU.md` / `out/phase7_interval_cyclic_nu.json`。

---

## 1 模块与调用方式（自包含、import 无副作用）

```
模块：research-2026/team-current/r20-stress/weights_interface.py
```

```python
import sys
sys.path.insert(0, '<repo>/research-2026/team-current/r20-stress')
import weights_interface as WI

W = WI.physical_weights()            # dict；值全部是 mpmath.iv 对象
lo, hi = WI.endpoints(W['tie_weight'][0])   # 端点 = mpmath.mpf（不是 float）
assert WI.positive(W['tie_weight'][0])      # 严格正判定（区间判据）

P, labels = WI.radial_partials()     # 可选：9x9 区间矩阵 d f_c / d rho_j + 行标签
```

* **import 安全**：模块级不做 I/O、不打印、不写文件、不 import 本目录其它脚本（不触发 phase7 的 `__main__`）。
* **不返回 float / 不做 JSON 往返**：所有量是 `mpmath.iv`；`endpoints()` 返回 `mpf`。
* 精度：`physical_weights(box=None, dps=35)`，内部以 `iv.dps = max(old, dps)` 计算并**恢复**原值；
  外向取整由 `mpmath.iv` 保证（与 dps 无关，dps 只影响宽度）。可传入自己的 12 维 `box`（同口径）。
* 自检：`py -3 -B -X utf8 research-2026/team-current/r20-stress/weights_interface.py`
  打印全部区间并在退出码上给出正性判定，且与 `out/phase7_interval_cyclic_nu.json` 交叉核对。

## 2 键名与含义（口径行）

盒：lead Krawczyk 12D 盒 `[c_i − r, c_i + r]`，`r = 1.0e-9`，变量 `u=(a0,a1,a2,a3,y0,y1,R,λ0..λ4)`；
所有区间**包围精确根处**的值。条件于：(i) 该盒的存在性证书；(ii) lead `TC-BOUNDARY-CHART-RANK`；
(iii) lead `TC-TO-PHYSICAL-KKT-LIFT`。本目录不复证 (i)–(iii)。

| key | 形状 | 含义（对象 = 真 physical chord-circle pin 残差；径向坐标 ρ_j，θ/hubs/R 固定） |
|---|---|---|
| `mu_pin` | 5 iv | `μ_i = −λ_i`：5 个 orbit-代表 pin 残差乘子（fan(1,H1), fan(2,H0), fan(3,H0), fan(8,H1), central(C6)） |
| `nu_gap` | 9 iv | per-gap 乘子（odd-9 循环公式，j=0..8；镜像对逐位相同） |
| `nu_orbit` | 5 iv | 对称空间（orbit 求和）乘子，= 12D 线性解口径（与 `nu_gap` 差因子 2，成对项；**不要混用**） |
| `c_k` | 5 iv | conversion `4y²/F_out > 0`（5 个 orbit 代表） |
| `face_weight_9` | 9 iv | **9 个 face 分支的物理权重**（成对 orbit 各取 `μ_o c_o/2`；自反射 fan(8,H1) 取全值） |
| `face_weight_orbit` | 5 iv | 上面 9 个的 orbit 和（= `μ_o c_o`） |
| `tie_weight` | 9 iv | **9 个边界 tie 分支的物理权重** `ν_j·(a_{R,j}+a_{R,j+1})`（= switch 腰腿分支 `t_j(c)`） |
| `s` / `one_minus_s` | iv | `s = Σ face_weight_9`；`1−s` |
| `tie_total` | iv | `Σ tie_weight`（与 `1−s` **解析相等**，见 §3） |
| `a_prime`, `a_R` | 9 iv | `a_ρ>0`、`R/(ρ_j sin a_j)>0` |
| `v`, `w` | 9 iv | 径向组装量与 `w_j=v_j/a'_j` |
| `partials`（`radial_partials()`） | 9×9 iv | `∂f_c/∂ρ_j`；行 = 9 个 contact（含镜像），列 = `ρ_j` |

标签：`face_labels`（9）、`tie_labels`（9，`gap0..gap8`）、`orbit_labels`（5，`{0,7},{1,6},{2,5},{3,4},{8}`）、
`contact_labels`（9）。与 `out/phase7_interval_cyclic_nu.json` 的对应：JSON 的 `boundary_gap_weights` ≡ 本模块
`tie_weight`；JSON 的 `face_weights` ≡ 本模块 `face_weight_orbit`（5 个 orbit 和）；
**建议直接用 `face_weight_9`/`tie_weight`（已按分支拆好），避免再手动 1/2 拆分。**

## 3 哪些是精确的、哪些只是区间（防止过度解读）

* **精确（解析，来自 lead 的 lift + 根方程）**：18 个权重全为正、且
  `Σ face_weight_9 + Σ tie_weight = 1`、`Σ w_i ∇g_i = 0`（在圆心坐标，因此在任何切片上）。
  还有 `tie_total = 1 − s`（R-平稳恒等式）。这些**不是**区间事实，不需要缩盒，也**不要**要求区间"等于"。
* **区间内容（本模块提供）**：每个权重**严格正**（含 `c_k>0`、`F_out>0`、`y≠0`、`a_ρ>0`、`a_R>0`、
  pin 侧符号严格可判），以及和式区间**含 1**（相容性，不是等号）。
* 组合使用：正性 + PD kernel ⇒ 局部二次增长（lead `FINITE-MINIMAX-QUALITATIVE-SUFFICIENCY.md`，
  我的独立简审见 `AUDIT-LEAD-MINIMAX-INTERFACE.md`）。
* `nu_gap` 与 `nu_orbit` 是**两种口径**（per-gap vs orbit 求和，成对项差 2 倍）；两者都对，
  混用会把边界总权重放大 2 倍（DEAD.md ③.5 有记录）。

## 4 与你（r23-rigidity）口径的对接

* 你的 `λ[9+k]`（ker(J^T)∩simplex 的分量）对应本模块 `tie_weight[k]`（k=0..8）；你读到的 1e-5 级吻合是
  两条独立路径（我：区间循环公式 + R-平稳；你：单纯形核权重），但**判据用区间正性**，不要把 1e-5 当精度。
* 你的 anti 2 维商块正定判定：用 `tie_weight[k]`（9 个）与 `face_weight_9[i]`（9 个）共 18 个权重；
  成对分支权重逐位相同（镜像），自反射分支取全值——**不要**再用 `face_weight_orbit` 手动除 2。
* 若你的区间 jet 需要 `∂f/∂ρ`：用 `WI.radial_partials()`（同盒、同口径、真 pin），但注意它是
  **径向**方向；anti 方向（y-反对称坐标）不在此矩阵内，需要你自己按 18 变量 jet 组装。

## 5 完整性/哈希（写进你的 JSON 时请一并记录）

模块与证据文件哈希（sha256）见 `out/weights_interface_hashes.json`；盒的来源哈希在
`out/phase7_interval_cyclic_nu.json` 的 `source_hashes`。模块的 `scope` 字段随每次返回给出完整口径行，
建议直接透传引用。
