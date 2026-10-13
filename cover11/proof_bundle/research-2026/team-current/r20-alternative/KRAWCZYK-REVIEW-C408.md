# KRAWCZYK-REVIEW-C408 —— 对 lead 新核的一次独立审查（按 `KRAWCZYK-SPEC.md` 清单）

> 路由 cline2/deepseek-v4.1f；只写 `r20-alternative/`；**未改任何脚本/文件**（仅读取）。
> 审查对象：`research-2026/team-current/lead/repair_tc_krawczyk.py`
> 及其记录输出 `lead/repaired_tc_krawczyk.json`、`lead/repaired_tc_krawczyk.log`。
> 方式：**代码审查 + 已有输出读数**（未重跑，避免覆盖 lead 产物）；一次通过，不扩任务。

## 0. 被审对象与已记录读数（原样引用）

- 脚本自述作用域："Only certifies an isolated 12D root of the explicitly specified symmetric TC KKT
  system. No full-geometry/local-min/global implication. Historical AD is reused; independent derivative
  audit pending."（作用域收窄 ✓）
- 记录读数：`newton` 三轮残差 `3.73e-16 → 7.85e-30 → 1.31e-57`；`pass_inclusion = True`；
  `contraction_inf = 0.0043719716…`（`< 1` ✓）；`radius_hex = 0x1.12e0be826d695p-30`（= `float(1e-9)`，**精确二进制**）；
  `max_K_shift ≈ 4.372e-12`（即包含余量约 `1e-9/4.37e-12 ≈ 229×`）；
  负控制：把第 8 个坐标中心挪 `+0.01` 后 `pass_inclusion = False`、`max_K_shift ≈ 0.01` ✓（判据非空转）。
- 运行耗时 `0.52 s`（复算成本极低）。

## 1. 逐项对照清单（规范 → 该核的实现）

| 清单项 | 实现 | 判读 |
|---|---|---|
| 1. `J(X)` 在**整盒**包络 | `f0,_=system(c,True)`；`_,JX=system(X,True)`，其中 `X=[c[i]+Dlt[i]]`，`Dlt=iv.mpf([-rad,rad])`；`system` 内 `C=iv.mpf`、`bundle` 用 `old.BK2_IV()` | **✓ 结构合规**（区间 Jacobian 覆盖整盒；详见 O2 的区间库严谨性义务） |
| 2. 位移为**完整区间差**且对称 | `Dlt=[iv.mpf([-float(rad),float(rad)]) for _ in uc]`，`X=c+Dlt`，且 `shifts` 里的位移项就是 `Dlt` | **✓**（`x0 = c` 即盒中心，位移对称；未见半径/单侧/点化） |
| 3. `F(x0)` 点值 + 外向舍入 | `system(c,True)`：以**退化区间**在中心求值，`f0` 为区间 | **✓ 可接受**（退化区间求值 ⊇ 点值；舍入严谨性见 O2） |
| 4. `Y` 非奇异 | `Yf = np.linalg.inv(np.array(Jmid,dtype=float))`，再 `iv.mpf(float(v))` | **✓ 已关闭（O1）**：`Q=‖I−YJ(X)‖_∞=0.004372<1` ⇒ 每个点实现 `Y·J` 可逆 ⇒ `Y` 可逆（Neumann 级数），**无需额外 det 检验** |
| 5. `∞`-范数在**区间矩阵**上、严格 `<1` | `Q=max(sum(norm(v) for v in row) for row in E)`，`norm= max(|lo|,|hi|)` | **✓**（`E` 的条目均为区间 ⇒ `Q` 是 `‖I−YJ(X)‖_∞` 的严格上界；`Q=0.00437`） |
| 6. 包含检验**逐坐标严格** | `all(lo(v) > -rad and hi(v) < rad for v in shifts)` | **✓ 严格**（`>`/`<`，非 `≥/≤`） |
| 7. 盒/单位/归一化明确 | `radius_hex`、`center_hex` 逐坐标十六进制记录；作用域限 TC KKT 孤立根 | **✓**（可复算、可引用；未外推到几何/全局） |
| 8. 退化处理 | 盒半径 `1e-9`，未涉及区间奇异/跨零；`Y` 重选规则未给 | **部分**（本例不触发；若用于更宽盒需补） |
| 9. 负控制 | 中心挪动 `0.01` ⇒ `pass_inclusion False` | **✓ 非空转**（但见 O4：建议再加"实现级"回归控制） |

## 2. 义务（O1–O4，按风险排序）

- **O1 —— 已关闭（lead team-message-129b319c）**：`Q = ‖I − Y·J(X)‖_∞ = 0.004372 < 1`
  ⇒（Neumann 级数/标准引理）每个点实现 `J ∈ J(X)` 有 `Y·J` 可逆 ⇒ `Y`（及 `J`）可逆
  ⇒ 不动点 `φ(x*) = x*` 推出 `F(x*) = 0` ✓。**无需额外行列式检验**。
- **O2（仍承重）区间算术与 AD 的严谨性**。`iv.dps=55` 下的 `mpmath.iv` 与复用的 `old.BK2_IV()`、`old.K32.res5`
  必须确认：(a) `res5`/`BK2_IV` 中**无**区间不安全操作（比较、`float()` 转换、分支、`min/max` 混用）；
  (b) 所用超越函数的外向舍入行为有据；(c) `h[k][i][j]`（二阶 AD）本身的正确性——脚本自述
  "independent derivative audit pending"，与本节一致。
- **O3 —— 已撤回（lead team-message-129b319c）**：我此前"不要写唯一性由范数保证"的建议**错**。
  `‖I − YJ(X)‖_∞ < 1` **本身就是**压缩判据，**直接保证唯一性**；无需改引更弱的定理表述。
  正确口径：范数压缩（唯一）与"对称居中盒包含检验"（存在）两条都有效；本核 `Q = 0.004372 < 1`
  已满足前者，**可直接据以断言唯一性**。
- **O4（低成本）实现级回归控制**。把 `KRAWCZYK-SPEC.md §3(b)(c)(f1)` 的**点化** FALSE PASS 族
  （点 Jacobian／点·零位移／点半径）做成该核的单元负控制；§3(f2) 的**单侧半宽**变体**单独**列出
  （不得与 (f1) 混同）。现负控制只验证"盒挪开后失败"，不构成对**实现错误**的防护。

## 3. 审查结论（一次通过）

- **合规**：清单 1、2、3、5、6、7、9 项**结构合规**；该核的包含检验用的是**整盒区间 Jacobian + 对称完整位移 +
  逐坐标严格包含**，与规范一致 ✓。
- **不能宣称**：在 O1、O2 关闭前，证书的"存在 + 唯一"结论应标为**条件性**（依赖 `Y` 可逆与区间库严谨性）；
  该核自述的作用域（仅 TC KKT 孤立根、不含几何/全局含义）**应保留**。
- **与 central coupling / n=11 全局的关系**：无。本审查不产生任何覆盖或下界结论。

## 4. 复现

```powershell
# 只读：不修改 lead 产物
py -3 -B -X utf8 -c "import json;d=json.load(open('research-2026/team-current/lead/repaired_tc_krawczyk.json',encoding='utf-8'));print(d['certificate']['pass_inclusion'], d['certificate']['contraction_inf'], d['certificate']['max_K_shift'])"
py -3 -B -X utf8 research-2026/team-current/r20-alternative/krawczyk_countercontrols.py   # 本目录的 generic 反控制（含 2D）
```
