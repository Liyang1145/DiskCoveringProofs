# coverage-audit — 独立复核 `lead/IDEAL-COVERAGE-PROOF.md` + `ideal_coverage_certificate.py`

复核者：finite-reduction（本成员）。**只读** `lead/{IDEAL-COVERAGE-PROOF.md, ideal_coverage_certificate.py, root_t_certificate.py, stress_interval.py}`、`evidence/{ideal-coverage-certificate.json, root-t-certificate.json}`；未修改任何 Lead 文件。
结论：**32/32 检查通过，未发现 Lead 证明或代码的错误**。等级：审计读数，不是认证；本文件不新增 claim。

---

## 1 被核的六条逻辑与结论

| # | Lead 的论证环节 | 本次复核方式与结果 |
|---|---|---|
| C1 | 坐标身份：$b=(1+a+r)/2$、$v=w/\sqrt3$、$d=2b-1$；缩放系 $(x,Y)$（物理 $y=Y/\sqrt3$）下 120° 旋转是 $(x,Y)\mapsto((-x\!-\!Y)/2,(3x\!-\!Y)/2)$ | ✓ 逐条精确验证：$d-(2b-1)\ni0$；旋转在**物理度量**下满足 $\langle p,Rp\rangle=-\|p\|^2/2$、$\det(p,Rp)=\tfrac32\|p\|^2$、$\|Rp\|=\|p\|$（50 个随机理点）；证书里 12 个中心与公式**逐坐标一致**（$\le10^{-40}$） |
| C2 | 边界恒等式：$H=0\Rightarrow(1-b)^2+v^2=r^2$；$G=0\Rightarrow\cos\alpha=\frac{1+t^2-r^2}{2t}$；$\cos(\pi/3-2\beta)=\frac{3b^2-w^2+6bw}{2(3b^2+w^2)}$；$F=0\Rightarrow a^2+(t-r)^2-a(t-r)=r^2$ | ✓ sympy 精确：记录的 $F,G,H$ 与我的恒等式**成正比**，比值 $1,\,4,\,12$（即 `clear_denoms` 因子）；$\cos(\pi/3-2\beta)$ 公式与 $G$ 推出的 $\cos\alpha$ 等式均符号验证通过 |
| C3 | 边界三段弧拼接 $[0,2\beta]\cup[2\beta,120^\circ\!-\!2\beta]\cup[120^\circ\!-\!2\beta,120^\circ]$，旋转 120°/240° 覆盖 $S^1$ | ✓ 端点恒等式（$H$）与半角恒等式（$G$）在 root box 上均含 0；$\cos\alpha\approx0.9498729\in(1/2,1)$ ⟹ $\alpha\in(0,\pi/3)$ ✓；单调性条款（$|\theta-\beta|\le\beta<\pi/6\Rightarrow\cos(\theta-\beta)\ge\cos\beta$）为解析事实，逐条核对成立；三段弧的**端点重合**与旋转由 C1 的精确旋转保证 |
| C4 | 13 三角形：333 图面 + 重标号 $i\mapsto i-2$；全 determinant>0；有向面链 = 9 边环多边形链；严格凸/原点在内/环心在 $D$ 内 | ✓ 我从 333 面表**独立重建**并重标号，与证书 13 面**同一集合**；13 个 determinant 严格正；有向链与 9 边边界**逐边相等**（含内部边双向抵消=0）；每条环边对其余全部中心严格左转；原点严格在内；12 中心 $\|c\|^2<1$ ✓ |
| C5 | 7 个 slack 面：外接半径严格 $<r$，带精确有理正 margin | ✓ 用**不同公式**（$R=\frac{abc}{4K}$，物理面积换算含 $\sqrt3$ 因子 $3/4$）重算，7 个 $R^2$ 区间与证书记录**完全相同**；margin：6 个面 $4.291126\times10^{-5}$、HHH 面 $[9,10,11]$ 为 $5.297693\times10^{-2}$（与记录一致） |
| C6 | 6 个 active 面：HRR 用 $d\,u(120j^\circ)$、HHR 用 $(t-r)u(60^\circ+120j^\circ)$ 作公共见证，距离**恰为 $r$** | ✓ 在 root box 上计算 $\text{dist}^2-r^2$ 的精确区间：18 个值**全部含 0**（宽度 $4\times10^{-30}\sim9\times10^{-30}$，即 ±10⁻³⁰ root box 的一阶传播）；即 $H/F$ 恒等式在盒上成立 ✓ |
| C7 | 公共见证方差恒等式 $\sum\lambda_i|x-c_i|^2=\sum\lambda_i|z-c_i|^2-|x-z|^2\le r^2$ | ✓ 200 组随机有理点**精确等于**（纯代数）✓；推论"至少一个 $\lambda_i>0$ 的距离 $\le r$"成立 ✓ |
| C8 | 壳外：$y=$ 投影、$v=x-y$，$\forall c\in P: v\cdot(y-c)\ge0$；沿 $x+sv$ 各距离严格增；射线交 $S^1$ 于 $u$；边界覆盖 ⟹ $x$ 被覆盖 | ✓ 18 个精确样本：投影最优条件 $(x-y)\cdot(c-y)\le0$ 对全部 12 顶点成立（边的两端点处精确为 0，按 box 舍入给 $10^{-25}$ 容差）；沿射线对所有中心的**严格**单调性成立；样本处 $\min_i|x-c_i|^2$ 严格 $<r^2$ ✓ 一般论证（投影性质 + 导数 $2[v\cdot(y-c)+(1+s)|v|^2]$）逐步核对成立 |

## 2 关键读数（精确有理）

- root box：$a,t,r,w$ 均为宽 $2\times10^{-30}$ 的有理区间；$r\in[0.36110296374450864,0.36110296374450866]$（显示值），$r^2$ 区间 $\ni0.13039535042506792$；$b>w>0$ ✓，$r<1/2$ ✓。
- slack 面 $R^2$：6 个为 $0.13035243916805181$（margin $4.2911\times10^{-5}$），HHH 面为 $0.07741842184616014$（margin $5.2977\times10^{-2}$）——**与记录逐位一致**（独立公式）。
- 与登记阈值的关系：root 证书自带断言 $r_{\rm hi}<U=0.361102963744508672616920293904$ ✓；故本证明给出 $r_D(12)\le r_*<U$（比登记上界小约 $2.9\times10^{-17}$）。此结论依赖 root 隔离（未由本次复核）。

## 3 复核中发现的问题（全部在我自己的审计代码，已修并留痕）

1. 我的外接半径公式漏了缩放因子：物理 $2K=\det_{\rm scaled}/\sqrt3$，正确为 $R^2=3\,l_1l_2l_3/(4\det^2)$（我原先写成 $l_1l_2l_3/(4\det^2)$，偏小 3 倍）。
2. 投影检验中把**边上两端点**的精确 0 值当严格负值处理（box 舍入给出 $\pm3\times10^{-30}$）：改为对两端点给 $10^{-25}$ 容差（并说明其精确值为 0）。
3. sympy 身份核验：`sympify` 产生的无假设符号与我 `symbols(...,positive=True)` 的符号**不同**，`subs` 静默失配；改为从记录表达式取符号。
4. 比例核验 `is_rational` 对未化简的 $p/p$ 误判；改为点值法定 $k$ 再作多项式恒等判别。
（以上均为审计实现问题；修正后 32/32 通过，且独立读数与 Lead 记录一致。）

## 4 范围与限制（诚实声明）

- **未**复核 `root_t_certificate.py` 的 Krawczyk 收缩/自映射（按指令视为 box 接口，未重跑）。
- C3 的"中间角距离更小"用解析单调性核对；本审计只对恒等式与常量做精确区间/符号验证，不重复做采样。
- 证书 JSON 本身只含几何与 13 面覆盖（其 `scope` 字段亦声明"boundary cap analytic argument separate"）；边界与壳外两段在 `.md` 中，本审计按其公式在 box 上逐条验证。
- 6 个 active 面的见证恒等式在 Lead 代码里**只标为 symbolic**（未数值检查）；本审计补了数值检查（见 C6）✓。
- 结论 $r_D(12)\le r_*$ 仍**不含**任何下界、不含 k10/k11 排除。

## 5 复现

```powershell
cd research-2026/n12-global/members/finite-reduction/coverage-audit
py -3 -B audit_coverage.py        # 32 项检查，全 PASS，exit 0
py -3 -B print_numbers.py         # 可读读数汇总
```
证据：`out/coverage-audit.json`（SHA256 前 16 位 `170C786E8C031B86`）、`out/coverage-audit-stdout.txt`（`AD398E44EBFB4D24`）。
