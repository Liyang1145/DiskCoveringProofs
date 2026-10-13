# claim_review 详证 — C998 (k11) / C999 (nearmerge)

本文件支撑 finite-reduction 对 C998、C999 的 `claim_review`（note 受 2000 字节上限，细节在此）。

## C998 (k11) —— 独立成立的部分
1. **源码/解析审计**（逻辑链逐条）：
   - 环心 $\rho\in[1-U,\sqrt{1-U^2}]$；开核 $B(0,1-2U)$ 只能由 hub 覆盖，hub 盘闭 ⟹ 覆盖其闭包 ⟹ $e\le3U-1$；
   - $e+U\le4U-1<1$ ⟹ hub 盘严格在 $D$ 内 ⟹ 从 hub 盘外侧径向逼近 ⟹ 11 个环盘必须覆盖 $S^1$ **且** $S(h,U)$；
   - 权重 $b_0\ge|b_c|+|b_s|$、$h_0\ge|h_c|+|h_s|$ ⟹ $W,V\ge0$；并集界 ⟹ 需求 $\pi(b_0+h_0)\le\sum C_i\le11\sup C$；
   - 遍历闭合：栈空即全域、**无丢弃节点**、分裂点为精确有理中点、接受 = 区间上端 < 区间下端目标、未定义/异常一律细分、budget 与最小盒宽 assert。
2. **捕获闭式**与**直接高精度求积**（弧上加权测度，角度/2）12 组一致，偏差 <1e−40。
3. **独立核**（`kern80.py`：自写 Machin π 宽 5.4e−20；halving+交错级数括号 sin/cos；asin 全正级数 + 显式尾界 $|x|^{2N+3}/(2(1-x^2))$，$x<0$ 走奇对称；半角归约；acos=π/2−asin）**完整重放 12 个 e 段，12/12 全 accepted**：margin 3.734e−6, 3.509e−6, 1.254e−5, 7.674e−6, **9.742e−7**, 1.458e−5, 4.119e−6, 1.225e−5, 3.307e−5, 1.462e−5, 5.795e−6, 2.767e−5（每段 1.8–3.1 万盒）。
4. **四处点名分支**：K1 权非负（从原始 `segment_U_K1.json` 独立重算聚合 + 精确 $\min_\varphi W\ge0$）；$\ell\ge2-4U=0.5556>0$ 且 $\ell^2\le0\Rightarrow$None⟹细分；$\mathrm{dist}(c,S(h,U))=|\ell-U|\ge U\iff\ell\ge2U$；$q_a\in[0,1]$ 全域成立、未截取 interval 在 200/200 盒越界 ⟹ 截取必要且无害（真值在 $[0,1]$）。
5. $\sin\alpha=\sqrt{1-q_a^2}$ 与复杂 arccos 两种写法均含真值；**未发现 inward truncation**。
6. **记录层**：kernel_sha256/input_sha256 与当前文件逐字节一致；dps=30；`upper_exact`/`target_lower_exact` 与打印区间一致（差 ~1e−34 显示取整）且 12 段严格。

### 我侧核的缺陷（Lead 指出）与处置
- **缺陷**：临界点判据原为 containment（$\text{包络}\subseteq[a,b]$）。若真临界点 $\in[a,b]$ 而包络跨端点则不插 $\pm1$，端点值未必覆盖 ⟹ 包络可能过窄。
- **修复**：改为 intersection（包络与 $[a,b]$ 相交即插 $\pm1$；过度包含对包络恒安全）。
- **尖锐回归**（`test_crit_straddle.py`，非抽样）：以 60 位 $X\approx x^*$ 与包络 $[L,H]$ 构造 $a=(L+X)/2,\ b=H$ ⟹ $x^*\in[a,b]$ 但不被包含；$\sin=\pm1$（$\pi/2,3\pi/2$）、$\cos=\pm1$（$\pi,2\pi$）四例修复后包络均含极值。
- **影响追踪**：最紧段 seg4 修复后 run 中 `sincos_iv` 调用 21 372、intersection 命中 8 116、**straddle 计数 0**（`out/post-fix-seg4-gapstats.json`）。辅助推导界：漏掉量 $\le w^2/2\approx6\times10^{-38}$（$w\approx3.5\times10^{-19}$）小于格单位 $5.4\times10^{-20}$，且 $\pm1$ 为格点，向外取整会抬回 $\pm1$ ⟹ 旧已存储包络仍含极值（仅作辅助）。
- **重放状态**：**修复前 12 段 replay 已 rescinded**；结论只由修复后的 12 段重放承担（`out/post-fix-{0-2,3-6,7-11}.json`），读数与修复前一致但证据已更新。
- **文字更正（未改源码）**：asin 尾界公式 $S_N\le\asin\le S_N+\text{tail}$ 只对 $x\ge0$；$x<0$ 用奇对称得 $[S_N-\text{tail},S_N]$。源码原本已分支（`Iv(s,s+tail) if x>=0 else Iv(s-tail,s)`），故只改 REPORT 文字。
- 另一核不受影响：`taylor-audit` 用 halving+doubling 逐点恒等式 + 显式余项，无临界点表。

### 不成立/未核（C998）
本核为**同一作者**实现（非第三方）；C925/C926 的内根归一化、核心论证、活跃数重分类未在本次重审。

## C999 (nearmerge δ=1/20) —— 独立成立的部分
1. **changed β 域**（独立推导 + 暴力几何）：圆 $S(h,R)$（$R=U+\delta$）与半径 $U$ 环盘（$\ell=|c-h|$）：$\beta=\acos(\mathrm{clip}\frac{\ell^2+R^2-U^2}{2R\ell})$；20 万点采样圆周 10 组随机 $(\rho,e,\varphi)$：cap 测度 $=2\beta$ ✓；inner/全圆分支需 $\ell+R\le U$，但 $\ell+R\ge\rho-e+R\ge2-3U=0.9167>U$（实测 $q_b\ge\sqrt{1-(U/R)^2}=0.478>0$）⟹ 不要下截取；$\ell\ge R+U\iff q_b\ge1\iff\beta=0$；$\beta\le61.5^\circ<90^\circ$ ⟹ 单弧无 wrap；$q_b$ 对 $\ell$ 非单调（min 在 $\ell^*=\sqrt{R^2-U^2}=0.1867$）⟹ 直接表达正确；$\ell\ge2-4U-\delta=0.5056>\delta$。
2. **记录层**：`radius`$=U+\delta$ 与 `offset_max`$=3U-1+\delta$ 与精确重算逐字符一致；两 assert（$4U-1+2\delta<1$、$2-4U-\delta>\delta$）成立；`target_ring_count=10`；12 段 e-区间相邻覆盖 $[0,1]$；**12 段全严格接受** margin 4.235e−8…7.309e−6；盒数合计 1 023 404 / max 128 771。
3. 源码改动审：相对 k11 核只改 $R$、$e$ 域、`ring_count`、β 一般式与上下截取。

### 审计等级（C999）
**source/inference + records 独立审；不是独立 complete replay**（nearmerge 未重放，按 Lead 指示停止）。几何 midpoint-circle 必要性取自 C999 自身接口（structure 已独立审）。
