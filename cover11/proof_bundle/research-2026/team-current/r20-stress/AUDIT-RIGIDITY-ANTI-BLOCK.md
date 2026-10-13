# 独立简审：r20-rigidity 的 anti kernel 区间块（`r20_anti_block_interval.py`）

> 审阅人 = r20-stress（**只读**；未写、也不会写 r20-rigidity 的任何文件）。工具：`audit_anti_tooling_check.py`
> （+`.json`/`.log`，合成已知答案的器械检验）。
> 本次审计覆盖该文件的**两个快照**（审查期间它一直在改）：
> S1 = 26324 字节（第一次读到的版本）、**S2 = 26975 字节，sha256 `5395d0dd291bc8271b6fd8024a9038d7933fc020ba2a8e4d77582aa8c4da9658`**（当前）。
> 逐条注明发生在哪个快照；S2 之后的改动需重新对哈希审。

---

## §0 结论（三行）

1. **权重顺序（lead 重点）正确**：18 支物理权重与 9 face / 9 tie 的对应逐项核过（§1.1），且是**每支**权重
   （成对成员各取 orbit 一半）⟹ 和为 1（解析）✓。
2. **S2 的主证书 `[A7]` 是 float-free 的（除一个索引选取仍需修，见 F-now-1）**：显式坐标补空间 +
   端点 Sylvester，不用特征值、不用度量算术 ✓；此前 [A6] 的 U 基（含 float lstsq）已被降级为 diagnostic ✓。
3. **F-now-1（必须修，S2 引入）**：`j*` 从 `rot_a[0:3]` 取，但 `rot_a` 是 **11 维 ε-坐标**向量，而补空间要按
   **3 维 kernel 坐标**选取；`0..2` 里第 2 个还是**非自由**列。正确且 float-free 的公式见 §2.1（一行可改）。
   另有 F-now-2（枢轴/有限性守卫）未修。

---

## §1 已核正确（逐条给理由）

1. **weights order（逐项语义核对）**：`FACE_MAP = {0:0, 5:1, 1:2, 4:3, 2:4, 3:5, 6:6, 8:7, 7:8}`（他们的 face
   下标 → 我的 `face_weight_9` 下标）与站点约定（9/10 = hubs `H0/H1`）核对：
   `(1,2,10)=fan(1,H1)`、`(6,7,10)=fan(6,H1)`、`(2,3,9)=fan(2,H0)`、`(5,6,9)=fan(5,H0)`、`(3,4,9)=fan(3,H0)`、
   `(4,5,9)=fan(4,H0)`、`(8,0,10)=fan(8,H1)`、`(2,9,10)=central(C2)`、`(6,9,10)=central(C6)` —— 一一对应无误。
   tie：`BR[9+k] = gap k` 与 `tie_weight[k]` 同序 ✓。`W` 是**每支**权重（pair 成员各 `μ_o c_o/2`、自反射全值）
   ⟹ `ΣW ∋ 1` ✓；成对成员区间逐位相同 ⟹ `W` 反射不变（B3 的 radical ⊇ rotation 所需）✓。
   控制：numeric Danskin λ ⊂ 区间权重（±1e-9）通过 ✓。
2. **float-free 的 anti 基与度量**：`BA` 全 ±1 ✓；`GEPS = BAᵀBA = diag(2×8,1,1,1)` 是**区间算出来**的 ✓；
   `rot_a` 用同一对角 ✓。无 1/√2。
3. **kernel 基严格**：8×8 minor 的区间 Gauss–Jordan（`MP`/`RHS` 同 `perm` 一致置换）+ det 区间非零 ⟹ 真根的
   `X*` 被包围 ⟹ `KV` 真为核向量（`A8·KV ∋ 0`，≤7.4e-57）；rank 8 ⟹ dim ker = 3（≤8 由 8 行 orbit 结构；
   自反射分支 anti 行恒 0）✓，与旧独立读数 `dim(ker∩Anti)=3` 一致 ✓。
4. **`[A7]` 的 Sylvester 逻辑有效**：对坐标补空间算 `B11 = lo(B3[a,a]) > 0` 与
   `det ≥ lo(B3[a,a])·lo(B3[b,b]) − (max|B12|)² > 0` ⟹ 该 2 维面上的二次型 PD ✓；配合
   (i) rotation ∈ radical(B3)（解析：加权平稳 + 旋转不变 ⟹ `Σ w_i∇g_i·x = 0` ⟹ `rotᵀH rot = 0`，
   且 `H[rot,·] = −⟨Σw∇g, J·⟩ = 0`）与 (ii) 补空间横截于 radical ⇒ **商空间 PD** ✓
   （`radical` 恰为 1 维：若 ≥2 维，2 维补空间必与之相交 ⟹ Sylvester 不会通过 ✓）。
5. **tie 侧符号 `TIEPICK` 正确**：取单位圆两交点中"最近两站点恰为 {k,k+1}"者 ✓；9/9 = −1，镜像自洽 ✓。
6. **jet 自检**（`1/x`、`x/y`、`sqrt` 已知 Hessian）误差 ≤1e-61 ✓。
7. **S1→S2 已修的项**：`eigvalsh(G⁻¹B)` 误用 → 已换 `scipy.linalg.eigh(B,G)`（S2 里 control 1/3）✓；
   `[A6]` U 基（float lstsq + `l1` 除法）已**降级为 diagnostic**（S2 第 556–558 行明确写 "not the certificate"）✓；
   `b12` 已同时取 `B12/B21` ✓；`weight_source` 元数据已改为模块路径 + 记录哈希 ✓。
   我 S1 报告里的 F1/F2/F3(a,c)/F4/F5 因此**均已解决或降级**，下面是剩余项。

---

## §2 剩余发现（S2 快照）

### 2.1 F-now-1（必须修）：`[A7]` 的 `j*` 取错空间，且未认证横截性
`rot_a`（第 421–426 行）是 **11 维 ε-坐标**向量；`[A7]`（第 562–566 行）却取 `rot_a[0:3]` 当作"3D kernel 的
旋转系数"。补空间应按 **kernel 坐标** `c*`（满足 `Σ_t c*_t KV[t] = rot_a`）选取。

**float-free 的正确公式（一行可改）**：由 `KV` 的构造（`v[COLS[i]] = −X[i,t]`、`v[FREE[t]] = 1`，
其余自由列为 0）立得

```
KV[t][FREE[s]] = δ_{ts}      ⟹      c*_t = rot_a[FREE[t]]        （FREE = [0,1,6]）
```

于是 `j* = argmax_t |rot_a[FREE[t]]|`，横截性 = 认证 `0 ∉ rot_a[FREE[j*], 0]`（区间非零下界）✓。
当前代码取 `{0,1,2}`：其中 **2 ∉ FREE**（依赖列），既不是 `c*`，也没有横截性认证 ⟹
`[A7]` 的"rotation-free 2D complement"目前**未被证明** rotation-free（虽然极可能仍是对的，因为
`{KV[a],KV[b]}` 一般仍横截）。修法：改索引集合 + 增加一条 `0 ∉ rot_a[FREE[j*]]` 的判定并把
`c* = rot_a[FREE]` 写进日志（这正是 `c_coef` 的 float-free 版本，可顺便删掉 `np.linalg.lstsq` 的 `c_coef`
对**证书**的一切影响）。

### 2.2 F-now-2（未修）：minor 枢轴无零排除/有限性守卫
目前只判 `det_iv = Π MP[c,c]` 两端同号。若某枢轴区间含 0，mpmath 的区间除法可能给出 ±inf，而
`EL(det)*EH(det) > 0` 在 ±inf 下仍可能为 True ⟹ **可能假通过**（box 模式下更危险，点模式已过）。
补：逐枢轴 `0 ∉ MP[c,c]`（并报 `min|枢轴|` 下界），对 `MP`、`X`、`det_iv` 做 `isfinite` 检查，NaN 一律记 FAIL。

### 2.3 记账（不必修，但引用时注意）
* `[A6]` 的 `blo`/`gmax`（第 552–557 行）现在被标注为 diagnostic ✓ —— 请**不要**把它与旧的
  "numeric run: 0.16490, 0.25496"并列引用；跨基/跨度量的特征值不可比（lead 在 `TC-SYMMETRIC-SECOND-VARIATION.md`
  里也警告过同一件事）。要比较就用 `scipy.linalg.eigh(B2,G2)` 的**同一对**（它们与 22D orthonormal 商块
  必然一致；我的 T2 合成检验证明了这一点）。
* `control 3` 的 `eig(...)` 路线（`np.linalg.eig(solve(G,B))`）**是合法的**（对 G-自伴算子给实数特征值）；
  只有 `eigvalsh` 那条不能用 —— S2 已改 ✓。
* box 模式输出（`r20_anti_block_interval.json`）在我审计时**尚未生成**，所以"整箱上 anti 商块正定"这一读数
  我未见过、不引用；本审计只覆盖逻辑与工具。

### 2.4 我做的器械检验（`out/audit_anti_tooling_check.json`）
| 检验 | 误用读数 | 正确读数 |
|---|---|---|
| T1：3×3，`G⁻¹B` 非对称（含精确零方向） | `np.linalg.eigvalsh(solve(G,B))` = **[-0.1302, 0.8086, 2.8910]** | `scipy.linalg.eigh(B,G)` = `eig` = Cholesky 白化 = **[-8.9e-18, 0.92440, 2.64497]** |
| T2：真实结构（`B3c=0`、`G3` SPD），补空间 2×2 铅笔 | `eigvalsh(solve(G,B))` = **[-0.1956, 0.2570, 1.2401]** | `scipy.linalg.eigh` = **[4.7e-17, 0.14058, 1.16094]**；坐标补空间 2×2 铅笔 = 同一对（精确/浮点系数差 1e-15） |
| T2 附带 | —— | `B3c` 的精确零性（1.7e-16）与"补空间 2×2 = 固有正特征值对"互证 ✓ |
这两条是我在 S1 里给 F1 的独立证据（不是读他们的代码得出的结论）；S2 已按此修 ✓。

---

## §3 未审范围

1. 我**没有重跑**他们的脚本（各自 sole writer）；未独立复算 18 变量 jet 的 zz/混合块（只看结构与自检）。
2. 未审计他们 `r20_physical_kkt_kernel.py` / `r20_anti_rank_interval.py` 的实现（只用到其 JSON 的一个控制）。
3. 审计针对 §0 的哈希快照；S2 之后若有改动，需重新对哈希审。
4. 数值（如 0.16490/0.25496 与旧 numeric run 的一致）是他们的读数；我只核工具与逻辑。

---

## §4 与 lead 定理的接口（整块 `H|_K ≻ 0` 的合成口径）

* `K` = 18 个活跃分支梯度的共同核；反射把它分成 sym ⊕ anti，`H`（加权 minimax Hessian，权重反射不变）
  **无交叉项**（`H[u_s,u_a] = H[σu_s,σu_a] = H[u_s,−u_a]` ⟹ =0 ✓）。
* **旋转方向在 K 内**（所有分支旋转不变 ⟹ `∇g_i·J = 0`），且 `H[rot] = Σ w_i∇g_i·x = 0`（加权平稳 ⟹
  `Σw∇g = 0`）⟹ `H|_K` 只有 PSD，`radical ⊇ span(rot)`。**所以两块的正定性都必须在 K/rot 上读**
  （lead `FINITE-MINIMAX-QUALITATIVE-SUFFICIENCY.md` 的 "Rotations" 段：先在切片内应用定理）✓。
* 维数对账：`K/rot` = 4 维 = **sym 2**（lead 的 `G = ZᵀHZ`，2×2，已核）+ **anti 2**（本文件审的
  `[A7]` 坐标补空间 2×2）；这与 r20-rigidity 旧读数 `c_k` 的 "dim 4, sym/anti 两半" 一致 ✓
  （注意：特征值不可跨基比较，见 §2.3）。
* 权重侧：`weights_interface.physical_weights()` 给 18 支**严格正**权重；`Σw = 1` 与 `Σw∇g = 0` 是**解析**
  （根平稳 + odd-9 + conversion 正因子），区间只需正性与相容 —— 这一点在 lead 的第 5 条指正后已统一口径。

---

## §5 补记（2026-09-25，收到 r23-rigidity 的 box 模式读数之后）

他们报告（我未跑其脚本、未看 box JSON，以下为**其**读数）：
8×8 minor 区间 `det ∌ 0`（rank ≥ 8，全 box）；补空间 **(KV[0], KV[2])** 上 `B11 ∈ [0.450451, 0.450475] > 0`、
`det ≥ 0.217798969238 > 0` ⇒ 商空间 PD；点模式 `scipy.linalg.eigh` 给
22D 正交商 `{0.164903, 0.254960}` 与 3D pencil `{0, 0.164903, 0.254960}` ✓（与我 T2 检验的结构一致）；
其 `ker(J^T)∩simplex` Danskin λ 逐分量落在我的 18 个区间内（0/18 失配）✓。

**关于 F-now-1 的实际影响（重要）**：他们用的 `j* = 1`（掉 KV[1]，补空间 (KV[0],KV[2])）与**正确规则**
恰好一致 —— 因为由 §2.1 的恒等式 `c*_t = rot_a[FREE[t]]`（FREE=[0,1,6]）以及他们打印的
`c* = rot_a[FREE] = (0.298370, −0.764706, 0.598609)` 得
`argmax_t |c*_t| = 1`（0.764706 > max(0.298370, 0.598609)）✓。所以**结论不变**，但**理由不成立**
（他们比较的是 `rot_a[2]`，一个依赖 ε-坐标，而不是 `rot_a[6]`）；按 §2.1 改成
`argmax_t |rot_a[FREE[t]]|` 并把 `0 ∉ rot_a[FREE[j*]]` 立为判定项后，同一补空间即获得有效论证。
F-now-2（枢轴/有限性守卫）仍建议补：box 模式下"det ∌ 0"的读数本身正确，但守卫可防 ±inf/NaN 假通过。

---

## §6 补记二（2026-09-25，lead 指定的两项 bearing 检查）

审计快照 **S4 = sha256 `6be637d3d37dea280a26621861afaf31f066605a832fdc60c459ca0dab2a6a76`（29371 B）**；
快照链：S1 26324 → S2 26975（`5395d0dd…`）→ S3 28003（`2742e64b…`）→ S4 29371（`6be637d3…`）。

**B. 零穿越判定（lead 第 2 点）—— S4 已满足。**
`TRANS_OK = bool((c_lo > 0) or (c_hi < 0))`（第 593 行）= **精确形式** ✓，并已并入合并判定
`VERDICT = DET_OK and not PIVOT_BAD and TRANS_OK and Sylvester`（第 614 行）✓；minor 枢轴守卫为
`p_lo * p_hi > 0` + `isfinite`（第 391–419 行）✓（乘积形式与 `lo>0 or hi<0` 等价）；两处
`min(abs(lo),abs(hi))`（第 399、594 行）只用于**报告 margin**，不再充当判定 ✓。
我的对照件（`out/audit_tie_branch_identity.json` → `check_B_control`）：区间 `[-1, 2]` 满足
`min(|lo|,|hi|) = 1 > 0` 却**含 0**、精确判定为 False ⟹ 旧形式的漏洞确实存在，现已不在证书路径上。

**A. TIEPICK 分支同一性（lead 第 1 点）—— 我在整个盒上独立认证 9/9 通过。**
器械：`audit_tie_branch_identity.py`（+`.json`/`.log`）；复用其构造（单位圆 ∩ 两盘 radical 线）在**同一个 lead 盒**上
以区间算术评估。阈值按 lead 指定：

| 判据 | 含义 | 读数（全盒一致包围） |
|---|---|---|
| A1 | 选中交点 p* 与 **chart 边界 tie** `P_k=(cos(θ_k+a_k), sin(θ_k+a_k))` 一致 | `sup |p*−P_k|² ≤ 1.75e-13`（≪1e-6 ✓） |
| A2 | 另一交点与 `P_k` 分离；两交点彼此分离 | `inf |p_other−P_k|² ≥ 3.78374`；两交点分离 `>0`（≈4）✓ |
| A3 | 相邻两点恰好 tie；**非相邻**站点 `|p*−C_i|²−R² > 0.01` | 相邻：区间含 0 ✓；非相邻 **min = 0.42480141** ✓ |
| A4 | 另一交点上 TIEPICK 判据**以裕度失败**（⇒ 冻结符号在盒上唯一正确） | **min = 1.3613519** ✓（有非相邻站点比相邻对近 ≥1.36） |

**结论**：lead 盒上 9 个 gap 的冻结 tie 分支**就是 C892 boundary tie**（A1），另一分支被 A2+A4 严格排除，
无非相邻站点抢夺（A3）⟹ "TIEPICK 是 numeric nearest choice" 这一 bearing 缺口在本盒、本构造下**闭合**。
两点补充：① 他们 S4 也加了同向检查（`tie_min`、`max|p−B_k|`，第 337–352 行），其中 `tie_min` 用**入射距离 f**
而非 R 作比较，形式比我的 A3 略强（不预设 f=R）✓；但 **A2/A4 他们尚未认证** —— 建议直接引用本节读数或补进脚本。
② 本认证针对**构造**（同公式 + 同盒），对其实现有效的前提是"其 `tie_branch` 确按该公式实现"——已读码核对 ✓（第 211–220 行）。
A3 的 min 值 `0.42480141` 与 W12 的 `F_out ≥ 0.4248` 数值同源（同一几何量的两种算法）✓。
