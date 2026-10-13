# C912：raw fixed-theta8 半径 `1e-8` 球 → canonical θ y-chart 局部 patch 的 exact 接口

> 写作用域：**只**本文件。等级：**纯解析/接口设计**（按 lead 指示：**先不写代码、不注册 claim、不派子 agent**）。
> 上游：`lead/NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md`、`lead/interval_network_envelope.py`、`lead/TC-ROOT-SOURCE-IDENTITY.md`、
> C909（labeling caliber）、C891（interval root）、本目录 `fresh_acute_slopes_interval.py`。

---

## §0 逻辑骨架（一行）

```
canonical y-cell  ⊆  { x : ‖A(x − x*)‖ ≤ 1e-8 }  =  raw fixed-theta8 半径 1e-8 球       (C912)
        ⟹ （lead 的 quantitative lemma）  V(θ) ≥ R*  在整个 cell 上 ✓
```
* 左边由 **凸性 + 线性** 给出：cell 凸 ⟹ 其像 = 顶点像的凸包 ✓；检验**顶点**即够 ✓。
* 右边是 lead 的引理：`V(θ*+x)² ≥ R*² + min(1, μ/4)‖x‖²`（`‖x‖ ≤ ρ`）✓ ⟹ 在球内 `V ≥ R*` ✓（`min(1,μ/4) ≥ 0` ✓）。
* **不是** global 结论 ✓（lead 已声明该 patch 只在 `‖x‖ ≤ ρ` ✓）。

---

## §1 先核实：labeling 与**两种角**（**v2 修正**：raw 角 = switch 角，不是 center 角 ✗）

**源码读数（lead 纠正）**：raw 侧用的是 `U[k] = (cos(θ_k+a_k), sin(θ_k+a_k))` ✓ —— 即**边界 switch（tie）角** ✓，
**不是** center 角 `θ_k` ✗（v1 若混同即错）。另：**`θ₄ = 0` 是 center-root 构造的初值** ✓，**不等于** "pin 第 8 个角" ✗——
两者**不可混同** ✓；本件凡言 "pin" 一律指 **raw 的第 8 个分量 = 0** ✓。

**labeling 确认（`new i = old (i+2) mod 9`）**：由 raw 的 face/hub 结构直接可见 —— **raw hub 9 的 fan 覆盖 raw ring 2..5
⟹ canonical ring 0..3** ✓（与 C909 caliber 同句 ✓；`TC-ROOT-SOURCE-IDENTITY.md` 提供源级同一性 ✓）。
**根角（canonical）**：
```
angles*_i = rawangles[(i+2) mod 9] − rawangles[2] + 2π·(branch)      (i = 0..8)
```
并须**检验 `angles*` 递增** ✓（一致性检查；本轮不写代码 ✓）。

---

## §2 线性 map `x_raw = A(θ_can − θ_can*)`（**v2 修正：只能是 9×9 置换，不得先丢 raw8** ✗）

**(a) 正确分解链（lead 给定）**：`A = R · P · Q9 · E`，四步**按序**：
1. **`E`（embed 到 9 维）**：canonical perturbation `δ ∈ R^9`，且**明确 pin `δ₀ = 0`** ✓（canonical 的第 0 个分量取 0 ✓）。
2. **`Q9`（9×9 置换）**：`new i = old (i+2) mod 9` ✓ ——**重 pin 之前只能是 9×9 置换** ✓，
   **不可**先丢掉 raw 的第 8 个分量再直接做 8×8 置换 ✗（v1 的说法作废 ✗）。
3. **`P`（减去 raw-8 分量）**：`u ↦ u − u_8·𝟙` ✓（实现"raw 第 8 个角 pinned 为 0" ✓）。
4. **`R`（restrict 到 raw 8）**：取前 8 个 raw 分量 ✓，第 8 个为 0 ✓。

**因此（lead 给的显式公式）**：raw 扰动
```
h_k = δ_{(k−2) mod 9} − δ_6        (k = 0..7)        h_8 = 0
```
✓（自洽性：`k = 8` 给 `δ_6 − δ_6 = 0` ✓，与 "raw8 fixed 0" 一致 ✓）。

**(b) 显式算子范数界（经上述链，仍得 ≤ 4 ✓）**：
`‖E‖ ≤ 1` ✓；`‖Q9‖ = 1` ✓（置换等距 ✓）；`‖P‖ ≤ 1 + ‖𝟙‖₂ = 1 + 3 = 4` ✓（`|u_8| ≤ ‖u‖₂` ✓）；
`‖R‖ ≤ 1` ✓ ⟹ **`‖A‖ ≤ 1·1·4·1 = 4`** ✓（与 v1 的数值同，但 v1 的**分解**错 ✗——现按 E→Q9→P→R ✓）。
（可选精化：`P` 在 8 维像上的谱；本件不展开 ✓。）

**(c) 方向与用途**：`‖x_raw‖ = ‖A(θ_can − x*)‖ ≤ ‖A‖·‖θ_can − x*‖ ≤ 4‖θ_can − x*‖` ✓ ⟹ §3 的充分式 ✓。

---

## §3 可执行的 containment formula（**一条**）

设 canonical y-cell 的顶点集为 `Vert`（例如各坐标 `|y_j| ≤ h_j` 的**角点** ✓），`x* := ` **C891 interval anchored point**
在 canonical chart 中的坐标（**不是十进制 root** ✗——见 §4）✓。检验：

```
(C912-EXACT)     ∀ v ∈ Vert :   ‖ A (v − x*) ‖₂  ≤  1e-8
```

由其充分性（用 §2(b) 的界）得**一条更易执行**的式子（不需要 `A` 的矩阵元，只要 `‖A‖ ≤ 4` ✓）：

```
(C912-SUFF)      ∀ v ∈ Vert :   ‖ v − x* ‖₂  ≤  2.5e-9        （= 1e-8 / 4）
```

* 若 (C912-SUFF) 成立 ⟹ (C912-EXACT) 成立 ✓ ⟹ **cell ⊆ raw 1e-8 球** ✓（凸性 + `A` 线性：像集 = 顶点像的凸包 ✓）。
* 若只用 (C912-EXACT)：需要 `A` 的**区间**矩阵元（或至少 `‖A‖` 的区间上界 ✓——保守取 4 即可 ✓）。
* `x*` 与 `Vert` 都必须来自 **interval** 对象 ✓（C891 interval root ✓；cell 的定义坐标 ✓），
  不等式用**区间/有理**判定（`HI(‖A(v − x*)‖²) ≤ 1e-16` 型的有理判据 ✓），**不得**用浮点比较 ✗。

---

## §4 对象身份与"不得把十进制 root 当 exact"

* **中心 `x*` 的来源**：C891 的 **interval root**（`lead/repaired_tc_krawczyk.json` 的 `certificate.radius_hex` +
  `center_hex` ✓），按本目录 `fresh_acute_slopes_interval.py` 已验证的同源构造（`z=u[:7]`、`a4=π−2Σz[:4]`、`ρ_k`、`θ` 递推、
  `c` = 9 ring + hubs `(z4,0),(z5,0)`、`U_k` = tie）✓——即 **interval anchored point** ✓。
* **禁止**：把任何十进制/浮点 root（例如 JSON 里的 decimal 字段）当作 exact 中心 ✗；也不得用"数值上等于 R*"代替区间包含 ✗。
* **对象身份证据（本次引用清单）**：
  1. `lead/TC-ROOT-SOURCE-IDENTITY.md`（raw ↔ chart 的**源级**同一性，含 `θ₄ = 0` 与两条递推 ✓）；
  2. C909 caliber 的 labeling 句（`new i = old (i+2) mod 9` ✓）；
  3. `lead/interval_network_envelope.py`（用 C891 interval root 构造 carrying nodes；未归一化位移等价 ✓）；
  4. 本目录 `fresh_acute_slopes_interval.py` + `out/fresh_acute_slopes_interval.json`（同源 interval 构造的独立实现 ✓）。
* **C912 的成立模式**：`C912` 断言的是"**raw 1e-8 球 ⊆ canonical patch**"这一**集合包含** ✓；它由
  (C912-SUFF) 的**顶点检查**与 §0 的引理链给出 ✓；**不**依赖任何 solver rank、数值秩或十进制读数 ✗。

---

## §5 环境与口径（本次不写代码）

* 需要的输入对象：C891 interval root（路径见 §4）；canonical y-cell 定义（顶点/半宽 —— 由 lead 的
  `NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md` 的 `x` 变量与 `ρ` 给出 ✓）；`‖A‖` 的上界（§2(b) 取 4 ✓）。
* 需要的判定：对每个顶点 `v`：`HI(‖v − x*‖²) ≤ (2.5e-9)²` ✓（有理/区间 ✓；`A` 若要用精确版则需 `A` 的区间元 ✓）。
* **未做**：本文件不含代码、不含新数值、未注册 claim、未派子 agent ✓（按 lead 指示 ✓）。
* **风险点（提前写明）**：(i) 若 `‖A‖` 的保守界 4 使 (C912-SUFF) 过紧（cell 半宽 > 2.5e-9），则需改用
  (C912-EXACT) 并给 `A` 的区间元（§2(b) 的精化版 ✓）；(ii) 若 cell 不是盒而是多面体，仍只要**顶点** ✓；
  (iii) `P_pin` 的"减共同旋转"必须在**同一约定**下做（`θ₄ = 0` ✓），否则 `A` 的定义会差一个整体平移 ✗。
