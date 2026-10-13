# Q0-CLOSURE-SOURCE-AUDIT —— q0 half-area/closure 因子完整性与 (4,9)/(5,8) 排除证书的 r 迁移作用域

**范围（lead）**：只做**源审计**（不改 lead 文件、不重跑长全域、无 claim）。源：`lead/Q0-CLOSURE-EXCLUSIONS.md`、`lead/RADIUS-TRANSFER-MOMENT-DUAL.md`（含其指向的 `CLOSURE-LOCAL-HALFPLANE-PROOF.md`(C820)、`CLOSURE-KERNEL-ANALYTIC-AUDIT.md`、符号/盒子脚本）。

## §1 真实 q0 graph ⇒ half-area 因子完整性 / closure 约束

* **扇区记号（源）**：扇区 `i = (A = P_{i−1}, C = c_i, B = P_i)`，`|CA| = R u`、`|CB| = R v`、`∠C = a`；`L_i` = A 处角、`T_i` = **B** 处角（**不是** `P_i` 处角）；`L_i = atan2(v sin a, u − v cos a) ∈ [0,π]`，`T_i = π − a − L_i`。
* **闭合成对性（完整性关键）**：`P_i` 处的 closure 方程用 **`T_i + L_{i+1}`**（相邻两扇区的**底角**），九条闭合成环（C820）；源写明"no supplement choice"：非负三角叉积 + 带符号点积唯一给出 ordinary base angle，`q > 0` 由 owns-positive-width 给出 ⇒ **九条闭合成环无缺项**。
* **面积/矩因子（供 dual）**：face 半径参数 `x ≥ 0` 以 `2r²·x·sin a sin b sin c` 入面积；switch 区 `r²·x·sin(2b)/2`；ring `q = (u−v)² + 4uv sin²(a/2) ∈ [0,4]`，`w(r) = 2 asin(r√q/2)`，其 r-依赖部分 `r²uv sin(a)/2 + (w − sin w)/2 + Cw`；closure 追加 `(h_left − h_right)β − h_right·a + h_right·π + (h_left+h_right)w/2`，`β = atan2(v sin a, u − v cos a)` **与 r 无关**。
* **审计结论**：half-area 因子集合（face/switch/ring/closure 四类）在源中**逐项给出**且与 C820 的九条闭合方程耦合方式一致（`h_i` 为任意实乘子加在零残差上，非负性只加在既有线性惩罚项上）；**未发现缺项**（本件只审源内自洽性，不重推 C820 的解析证明）。

## §2 (4,9)/(5,8) 排除证书的作用域（对**所有 r ≤ 0.38**）

* 源结论：`C817/C818`（shared first/second moment area dual）+ `C819` 合并后**只剩 q0(6,7)**；即在 `r ≤ 0.38` 内 **(4,9)、(5,8) 两族（以及其余度对）已被排除**，其证书作用域声明为**全域 `r ≤ 0.38`**（不是仅端点）。
* 端点算术（源）：`R = 19/50` 的 `k3` 上界区间 `[3.09579…, 3.09579…] < π`（文件 `q0_closure_dual_certificate_0_3.json`）；`R = 3/8` 的 `k4` 上界区间 `[3.10878…, 3.10878…] < π`（`q0_lower375_dual_certificate_0_4.json`）。
* **审计要点（作用域成立的两个前提）**：见 §3——(a) 各因子对 r 的**单调方向**；(b) **域嵌套**（小 r 的合法域 ⊆ R 端点域）。

## §3 固定 r ⇒ 小 r 的迁移：方向与域包含（逐条对源）

1. **单调方向（逐因子点对点，非区间算法单调）**：源明文要求"用 **EXACT factor functions 及其 domain suprema**，而不是实现里按 r 相交的区间界"：
   face `2r²x sin a sin b sin c` 对 r 不减（`x ≥ 0`）✓；switch `r²x sin(2b)/2` 对 r 不减（`x ≥ 0`）✓；
   ring `w(r)` 不减，其 r-依赖部分导数 `r u v sin a + [(1−cos w)/2 + C]·w′(r) ≥ 0` ✓；
   closure 追加项中仅 `w/2` 依赖 r（β、a、π 项与 r 无关）⇒ 系数符号由 `(h_left+h_right)` 决定（源按各 orbit 的 `h` 记录处理）；
   常数项 `C0(r) = π(Σz[:9] + 2Σz[9:11] + Σz[50:71] − 2z[71] − 2z[72]) + 2z[72]·asin(2r)`，closure 另减 `π·Σz[112:]`；**没有额外的 r 因子乘在线性 π 惩罚上** ✓（源逐槽核实 slots 71/72 = λ/η）。
   源并指出 saved q1 orbit0/orbit2 的 `λ = 0`、`η = 0.437458336 / 1.357679461 ≥ 0` ⇒ `C0` 非减（`η ≥ 0` 时）✓。
2. **域包含/嵌套**：closure ring screen 用 `q ≥ qmin(r) = 4sin²(π − 8 asin r)/r²`；九个边界弧每个 ≤ `2 asin r` ⇒ 强制 `r ≥ sin(π/9)`（更小的 r 对 9-ring cover 本身不可能）✓ ⇒ 小 r 的合法参数域**嵌套在**端点域内 ✓（源的 "Closure-domain nesting" 一节）。
3. **结论（迁移成立的条件式）**：在 **(1) 逐因子单调（按源给定的符号/系数范围）+ (2) 域嵌套** 两条都成立时，端点 `R = 19/50`（以及 `k4` 的 `3/8`）的 `< π` 上界可**顺 r 下移**到所有 `r ≤ 0.38` 的合法域；**反之若把实现里的区间界当函数单调用则不成立**（源已明示，本件不把它当证明）。

## §4 可承重 / 不可承重（口径）

* **可承重（源内）**：(4,9)/(5,8) 及其余度对的排除在 `r ≤ 0.38` 的**声明作用域**由"端点证书 + 单调迁移 + 域嵌套"三件支持；half-area/closure 因子在源中逐项完整，九条闭合成环（`T_i + L_{i+1}`）无缺项。
* **不可承重**：本件**未**重推 C820 的解析证明，**未**重跑全域；`check_closure_boxes.py` 的 13439 点/4350 盒与 scalar 残差 `9e-16` 在源中标注为 **calibration only（no continuum inference）**，本件**不作证据引用**；不含 `q0(6,7)` 在 `r ∈ (3/8, 19/50]` 的排除（源留作 open）。
* 无 claim；无 lead 文件改动；无长全域重跑。
