# onehub-audit — 承重链（k11 独立核复核 + nearmerge 源/推理/记录复核）

复核者：finite-reduction。**只读** Lead 文件（`lead/{onehub_interval_certificate.py, nearmerge_interval_certificate.py, K11-DUAL-EXCLUSION.md, K10-NEAR-MERGE-REDUCTION.md}`、三个 evidence JSON、`members/structure/onehub-dual/segment_U_K1.json`）。
**结论：未发现 Lead 证明或代码的错误。** 等级：审计读数（非认证）；不新增 claim；k9/root 未再评。

---

## 1 承重链（先说结论）

**B1 k11 逻辑链**（source audit，逐条通过）：环心 $\rho\in[1-U,\sqrt{1-U^2}]$；hub 必须覆盖核心闭包 ⟹ $e\le3U-1$；hub 盘严格在 $D$ 内 ⟹ 环盘必须覆盖 $S^1$ **且** $S(h,U)$；权重非负 + 并集界 ⟹ 需求 $\pi(b_0+h_0)\le11\sup C$；接受条件为"区间上端 < 区间下端目标"、无丢弃节点、分裂点为精确有理中点、未定义/异常一律细分（另有 budget 与最小盒宽 assert）—— 证明闭合成立。

**B2 捕获闭式**（承重：这是被上界的量）：$C=b_0\alpha+\sin\alpha(b_c\cos\varphi+b_s\sin\varphi)+h_0\beta+\sin\beta\big(h_c\frac{\rho\cos\varphi-e}{\ell}+h_s\frac{\rho\sin\varphi}{\ell}\big)$，$\alpha=\acos\frac{1+\rho^2-U^2}{2\rho}$，$\beta=\acos\min(1,\frac{\ell}{2U})$。我用**直接高精度求积**（对两条弧上的加权测度积分，角度/2 测度）在 12 组随机参数复核闭式，偏差 $<10^{-40}$ ✓。

**B3 自写核的 acos/asin 尾界（proof，非启发式）**：$\asin x=\sum c_kx^{2k+1}$，$c_k=\frac{(2k)!}{4^k(k!)^2(2k+1)}$ 全正且 $k\ge1$ 时 $c_k\le c_1=\frac16\le\frac12$（且随 $k$ 递减）。故对 $N\ge1$
$$S_N(x)\;\le\;\asin x\;\le\;S_N(x)+\frac{|x|^{2N+3}}{2(1-x^2)}\qquad(|x|<1),$$
尾界由 $\sum_{k>N}c_k|x|^{2k+1}\le\frac12\sum_{k>N}|x|^{2k+1}$ 得来（$N=24$）。$|x|\in(1/2,1]$ 用半角归约 $\asin x=\frac\pi2-2\asin\sqrt{\frac{1-x}{2}}$（内层落在 $[0,1/2]$，被开方的正值性由区间 sqrt 向外舍入保证），$|x|\le1/2$ 直接级数；$\acos=\frac\pi2-\asin$；区间情形用 $\asin$ 单调 ⟹ 取端点包络。π 由 Machin（$16\atan\frac15-4\atan\frac1{239}$）交替有理界给出，宽 5.4e−20。

**B4 自写核的 critical-point coverage —— 曾有 real 缺陷（Lead 指出），已修 + 尖锐回归 + 影响追踪 + 重放**

- **缺陷（原版）**：判据是"临界点 π 包络 **包含于** $[a,b]$"（containment）。若真临界点 $x^\*\in[a,b]$ 而包络跨端点，则不插 $\pm1$，而端点值**未必**覆盖到 1 ⟹ 包络可能过窄（不安全）。Lead 判断正确：`kern80.py` 原代码确为 containment（`a <= iv.lo and iv.hi <= b`）。
- **修法**：改为"包络与 $[a,b]$ **相交**即插 $\pm1$"。过度包含只会纳入未被取到的值，对包络恒安全。
- **尖锐回归测试**（`test_crit_straddle.py`，不靠抽样）：用 60 位 $X\approx x^\*$ 与包络 $[L,H]$ 构造 $a=(L+X)/2<b=H$ ⟹ $x^\*\in[a,b]$ 但包络不被包含；对 $\sin=\pm1$（$\pi/2,3\pi/2$）、$\cos=\pm1$（$\pi,2\pi$）四例，**修复后包络确实含 $\pm1$** ✓。
- **影响追踪**（最紧段 seg4 的修复后 run）：`sincos_iv` 调用 21 372 次 / intersection 命中 8 116 次 / **straddle（旧条件会漏）计数 = 0**。辅助推导界：若命中 straddle，端点值距 $\pm1$ 至多 $w^2/2\le6\times10^{-38}$（包络宽 $w\approx3.5\times10^{-19}$），小于格单位 $5.4\times10^{-20}$，而 $\pm1$ 是格点，向外取整会把端点值抬回 $\pm1$ ⟹ 旧的**已存储**包络仍含极值；此界只作辅助。
- **重放状态（不静默补源码后称旧 run 有效）**：**修复前 12 段 replay 不再作证据（rescinded）**，已用修复后核在**全部 12 段重跑**（读数与修复前一致：margin 9.742e−7 … 3.307e−5，全 >0；盒数相同），结论现只由**修复后**重放承担。证据 `out/post-fix-{0-2,3-6,7-11,seg4-gapstats}.json`。
- 另一核不受影响：`taylor-audit` 的 trig 用 halving+doubling 的**逐点恒等式**扩展 + 显式余项，不用临界点表 ⟹ 无同类内含条件（已核）。

覆盖口径：包络 = hull{端点值} ∪ {相交的临界点 $\pm1$}；宽 $\ge2\pi_{\rm hi}$ 直接 $[-1,1]$；临界点包络预计算覆盖 $[-13,13]$ 内全部 $(\frac12+k)\pi,(\frac32+k)\pi,2k\pi,(2k+1)\pi$；本审计参数在 $[0,2\pi]\subset[-13,13]$。

**B5 k11 全 12 段独立 box-cover（全 accepted；这是本次唯一的完整独立 replay）**

| seg | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 我的 margin | 3.73e−6 | 3.51e−6 | 1.25e−5 | 7.67e−6 | **9.74e−7** | 1.46e−5 | 4.12e−6 | 1.23e−5 | 3.31e−5 | 1.46e−5 | 5.80e−6 | 2.77e−5 |

（每段 1.8–3.1 万盒；Lead exact margin 另列于 `out/`，两者都是同一 $\sup C$ 的合法上界。）

**B6 nearmerge 的 changed β 域：正确**（独立**推理**复核，非 replay）：$\beta=\acos(\mathrm{clip}\frac{\ell^2+R^2-U^2}{2R\ell})$，$R=U+\delta$。① **暴力几何**：20 万点采样圆周，10 组随机 $(\rho,e,\varphi)$ 得 cap 测度 $=2\beta$ ✓；② 全圆/inner 分支不可能（需 $\ell+R\le U$，但 $\ell+R\ge\rho-e+R\ge2-3U=0.9167>U$；且实测 $q_b\ge\sqrt{1-(U/R)^2}=0.478>0$）⟹ **不写下截取安全**；③ 上截取精确：$\ell\ge R+U\iff q_b\ge1\iff\beta=0$ ✓；④ $\beta\le61.5^\circ<90^\circ$ ⟹ 单弧、无 wrap；⑤ $q_b$ 对 $\ell$ **非单调**（min 在 $\ell^*=\sqrt{R^2-U^2}=0.1867$）⟹ 代码"直接表达、不设单调假设"正确 ✓；⑥ $\ell\ge2-4U-\delta=0.5056>\delta$ ✓。

**B7 四处点名分支（k11，全部通过）**：K1 权非负（从**原始** `segment_U_K1.json` 独立重算聚合，24 组 $b_0\ge|b_c|+|b_s|$ 且精确 $\min_\varphi W\ge0$）✓；$\ell>0$（$\ell\ge2-4U$；$\ell^2\le0\Rightarrow$ None ⟹ 细分）✓；β cut（$\mathrm{dist}(c,S(h,U))=|\ell-U|\ge U\iff\ell\ge2U$）✓；**acos clip**（$q_a\in[0,1]$ 全域成立；未截取 interval 在 200/200 盒中越界 ⟹ 截取必要，真值在 $[0,1]$ ⟹ 无害）✓；$\sin\alpha=\sqrt{1-q_a^2}$ 与复杂 arccos 两种写法**都**包住真值，**无 inward truncation** ✓。

**B8 nearmerge 记录层**：`radius=U+\delta`、`offset_max=3U-1+\delta` 与精确重算**逐字符一致** ✓；两 assert（$4U-1+2\delta<1$、$2-4U-\delta>\delta$）✓；`target_ring_count=10` ✓；12 段 e-区间相邻覆盖 $[0,1]$ ✓；**12 段全严格接受**（margin 4.235e−8 … 7.309e−6）✓；盒数合计 1 023 404 / max 128 771 ✓。k11 侧 `kernel_sha256`/`input_sha256` 与当前文件**逐字节一致** ✓、`dps=30` ✓、`upper_exact`/`target_lower_exact` 与打印区间一致（差 ~1e−34 = 显示取整）且 12 段严格 ✓。

## 2 nearmerge 的审计等级（明确）

**source/inference + records 独立审：是；独立 complete replay：否**（按 Lead 指示已停止；无 duplicated pass 要求）。即：β 域公式与其分支被独立**推导并几何复核**、域与常量被独立重算、记录被逐项复核；但**未**用我的核重跑 12 段 box-cover（我的核 ~350 盒/秒，tail 段超 shell 上限）。

## 3 secondary controls（非承重，仅供参考）

mpmath 160 位标定（π/点·区间 sin-cos/asin·acos/sqrt 全包含，最小余隙 2.2e−21）；mpmath.iv 探针（`iv.cos/sin([0,2π])=[−1,1]`、`iv.atan2` 双区间参数覆盖采样矩形、`iv.mpf([lo,hi])` 保端点、`iv.sqrt` 外舍）；$\varphi=0$ 与 $2\pi$ 周期性一致（无 wrap，容差 1e−15 ≪ margin）；每段 8 个角点单独评估均 $<$ 目标。

## 4 我自己的代码问题（审计中修正，留痕）

负参数 sin 括号方向；临界点乘数写错（由标定暴露，正是 B4 关注的失效模式）；wrap 探针容差 1e−18→1e−15；mpmath `.a/.b` 是退化区间（需 `._mpi_`）；`parents[]` 路径与探针细节。**Lead 侧零 issue。**

## 6 claim_review 口径（C998 k11 / C999 nearmerge；本成员不新增 claim）

**C998（k11）—— 独立成立的部分**：① source/analytic audit：必要几何（核心闭包 ⟹ $e\le3U-1$；hub 盘在 $D$ 内 ⟹ 环盘须覆盖 $S^1$ 与 $S(h,U)$）、非负权并集界、需求 $\pi(b_0+h_0)$、遍历的证明闭合（空栈/无丢弃/有理中点/接受条件/异常细分/两个 assert）；② 捕获闭式与直接高精度求积一致（12 组 <1e−40）；③ **独立核**（自写 Machin π、halving+交错级数 sin/cos 且用修复后的 **intersection** 判据 + 尖锐 straddle 回归、asin/acos 正项级数尾界 + 奇对称分支）；④ **修复后的完整独立 replay：12/12 段全 accepted**（margin 9.742e−7…3.307e−5，全 >0）；⑤ 四处点名分支（K1 权非负、$\ell>0$、β cut、acos clip）与 $\sin\alpha$ 两种写法等价性；⑥ 记录层（kernel/input sha256 与当前文件一致、dps=30、`upper_exact`/`target_lower_exact` 一致且 12 段严格）。
**不独立成立/未核**：我的核为同一作者实现（非第三方）；内根归一化、核心论证、活跃数重分类等输入取自 C925/C926（本次未重审）；**修复前的 replay 已 rescinded**，结论由修复后重放承担。

**C999（nearmerge）—— 独立成立的部分**：① **changed β 域**的独立推导 + 暴力几何（cap 测度 $=2\beta$，10 组；inner 分支不可能；$\ell\ge R+U\iff\beta=0$；$q_b$ 对 $\ell$ 非单调；$\beta\le61.5^\circ$）；② 记录层（`radius`$=U+\delta$、`offset_max`$=3U-1+\delta$ 精确一致；两 assert；`target_ring_count=10`；12 段 e-区间相邻覆盖 $[0,1]$；12 段全严格接受 margin 4.235e−8…7.309e−6；盒数 1 023 404/max 128 771）；③ 相对 k11 核的源码改动审（R、EM、ring_count、β 一般式与上下截取）。
**审计等级**：**source/inference + records 独立审；不是独立 complete replay**（nearmerge 未重放，按 Lead 指示停止）；几何 midpoint-circle 必要性取自 C999 自身接口（structure 已独立审）。

```powershell
cd research-2026/n12-global/members/finite-reduction/onehub-audit
py -3 -B calib_kern80.py            # 核标定（B3/B4）
py -3 -B audit_onehub.py <segs>     # k11 独立 box-cover（B5）
py -3 -B audit_branches.py          # B7
py -3 -B check_evidence.py          # B8
py -3 -B audit_nearmerge.py         # B6（Part I；不带段号则不做 box-cover）
```
产物：`out/{kernel-calibration.json, onehub-audit.json, chunk-0-2.json, chunk-3-5.json, chunk-6-8.json, chunk-9-11.json, chunk-11.json, onehub-branches.json, evidence-checks.json, nearmerge-audit.json}`；`kern80.py`（自写核）、`REPORT.md`（本文）。
