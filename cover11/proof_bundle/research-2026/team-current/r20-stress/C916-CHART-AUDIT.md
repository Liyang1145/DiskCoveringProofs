# C916 chart-containing 接口审计（独立；**未独立重构 root**）

> 写作用域：**只**本文件。审计对象：**C916**（`lead/certify_canonical_local_patch.py` + `canonical_local_patch_certificate.json`）。
> 范围**限 chart containing 接口** ✓；**不**审 C915/adaptive ball lemma ✗（其常量属 lead 另一线 ✓）；**不**审 energy lemma ✗；
> **不**改 lead 文件 ✓；**未**独立重构 C891 root ✗（身份/读数按路径引用 ✓——**身份不是证明** ✓，故本审计只对"接口一致性"下结论 ✓）。

---

## §0 逐项核对（lead 指定项）

| # | 待核项 | 代码/证书证据 | 判定 |
|---|---|---|---|
| 1 | **raw 角是 switch `th+a`**（非 center 角） | 注释 "Increasing unwrapped raw tie angles, root center-angle theta4=0 unrelated to gauge" ✓；C916 caliber 同句 ✓；且 `assert all(raw[k+1]−raw[k]>0)` ✓ | ✓ 一致 |
| 2 | **`2π` 分支 `i ≥ 7`** | `can=[0]+[raw[(i+2)%9]−raw[2]+(2π if i≥7 else 0) i=1..8]` ✓；并由 `assert all(0<w<L)` ✓ **反向校验**（分支错则该断言失败 ✓） | ✓ 一致且被校验 |
| 3 | **canonical θ₀ ↔ raw 2** | `raw[(i+2)%9]−raw[2]` 且 `can[0]:=0` ✓；与"raw k → canonical (k−2) mod 9"（`rotation_map` ✓）互为逆 ✓ | ✓ 一致 |
| 4 | **`h_k = δ[(k−2)%9] − δ6`（k=0..7），raw8 = 0** | 代码第 28 行逐字一致 ✓；json `rotation_map` 同句 ✓ | ✓ 一致 |
| 5 | **`y8` dependent** | 独立坐标 = `y0..y7`（半宽 `1/50000` ✓），`y8 = 1 − Σ_{i<8}y_i` ✓ | ✓ 一致 |
| 6 | **exact candidate 包含 + cube ⊂ P** | `assert all(I(c_i−eps) < y0_i < I(c_i+eps))` ✓（`y0` = canonical candidate 的 y 区间 ✓）；`assert all(I(c_i−eps)>0)` 且 `I(c_8−8eps)>0` ✓（⊂ `P={y≥0,Σy=1}` ✓）；"no decimal radius/angle is used as exact candidate" ✓ | ✓ 一致（**但见 §1(a)**） |
| 7 | **face/site 图映射 raw → (raw−2)%9，hubs 不变** | `shift(s)=(s−2)%9 if s<9 else s` ✓；`assert all(tuple(sorted(map(shift,f))) ∈ canfaces for f in rawF)` ✓（raw 11 面 ⊆ canonical 面集 ✓） | ✓ 一致（有限图检查 ✓） |
| 8 | **norm 界** | `norm2_direct_upper = 1.755579e−7` ✓ < `(431/10^6)² = 1.85761e−7` ✓（`rho2_lower` 同值 ✓） | ✓ 直接界足够；**见 §1(b)** |

---

## §1 两点提示（非"错误"，但影响引用方式）

**(a) width/site 归属（lead 提醒的 `θ_i→θ_{i+1}`、`site_i` 拥有 *previous* width）**：代码取
`width[i] = can[i+1] − can[i]`（`i=0..7`）与 `width[8] = 2π − can[8]` ✓，`y0[i] = (L−width[i])/D` ✓。
C916 的**自身断言**只保证：widths 为正且 `< L` ✓、cube ⊂ `P` ✓、**candidate 落在以 `c` 为心的 box 内** ✓——
但 `c` 与 candidate 的 `y` 都是用**同一套** width 归属算出的 ✓ ⟹ 一个**系统性 off-by-one** 会同时进入 `c` 与 candidate，
**不会被该断言排除** ✗。旁证：`c` 呈**循环移位型**对称（`c_0=c_2` ✓、`c_4=c_7` ✓、`c_5=c_6` ✓、`c_3≈c_8`（差 2/10¹²）✓、
hub 侧的轻微不对称 ✓），与"site 拥有 previous width"的约定**相容** ✓，但**不构成**与 C915（cap 宽度的几何归属）的跨文件一致性的证明 ✗。
**结论**：`site_i ↔ width` 的归属**必须**与 C915 的约定逐点对齐才可跨文件引用 ✓（我未独立重构 root ✗，故只在接口层记录该风险 ✓）。

**(b) "‖A‖ ≤ 4" 的 fallback 对本 ball **不够** ✗**：json 的 `norm2_via_operator4_upper = 7.022e−7` **>** `(431/10^6)² = 1.8576e−7` ✗——
即若只用本目录 C912 的保守界 `‖A‖ ≤ 4`，该 containment **不成立** ✗；C916 实际使用的是**直接区间范数**
`norm2_direct_upper = 1.755579e−7` ✓（< ball² ✓）。⟹ 引用 C916 时**不得**改述为"由 ‖A‖ ≤ 4 得到" ✗。

---

## §2 C916 依赖链（引用时必须带上的条件）

* `status = proved-interval **containment conditional on adaptive ball lemma/constants**` ✓——即：
  **chart containment 部分**由本审计覆盖 ✓；**`V(U(y))² ≥ R*²` 部分依赖 C915 + adaptive ball 常量** ✗（不在本审计范围 ✓）。
* 依赖 `C891`（exact candidate 的源级重构 ✓，非十进制 ✓）与 `C915` ✓。
* 本审计**未**做：独立重构 root ✗、复算 C915 常量 ✗、复算 `R*` ✗。

---

## §3 结论（限 chart containing 接口）

* §0 的 8 项**均一致** ✓（含两处被断言反向校验的项：`2π` 分支、cube ⊂ `P` ✓）。
* **未发现错误** ✓；两点提示见 §1（(a) 跨文件归属待对齐、(b) 勿用 `‖A‖≤4` 改述）✓。
* 因此对该**接口**部分给出 `reviewed` 级复核事件 ✓（证据 = 本文件 + C916 代码/证书路径 ✓；
  **未独立重构 root** 已在 §0/§2 明示 ✓——身份不代表证明 ✓）。
