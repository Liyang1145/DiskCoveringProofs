# 有限候选归约定理（v2，精简核心；已按 Lead 审计修正）

作用域：**任意**非空有限 $C\subseteq D$（允许重复中心、允许 $0\in C$）；无一般位置、无互异、无对称、无接触图假设。
本文件只证明**有限判据**（消去覆盖判据里定义域上的 $\forall x$）；**不**证明 n=12 全局最优。
配套：[`QE-interface.md`](QE-interface.md)（无分母多项式接口）、[`NUMERICS.md`](NUMERICS.md)（仅校准）。
v2 修正：L2' 的 $w$ 定义文字统一；L3(ii) 中点情形的方向与数值；L3(i) $w=0$ 的取值；§5 提升表述（删去错误的"上凸包/farthest Delaunay"读法，$K_d$ 只是代数超集）；基数改为上界；"位于 $D$ 内"过滤的作用改为"等价性所必需"。

---

## 0 对象、候选集、主定理

- $D=\{x\in\mathbb R^2:|x|\le1\}$；$C\subseteq D$ 非空有限（$n=|C|\ge1$，允许重复、允许 $0\in C$）。
- $f_C(x)=\min_{c\in C}|x-c|$；$R(C)=\max_{x\in D}f_C(x)$；$D\subseteq\bigcup_c B(c,r)\iff R(C)\le r$。
- $P$：$C$ 的**不同位置**集合，$n'=|P|$；$f_C,R(C)$ 只依赖 $P$。
- **候选集**（按不同位置）：
  $K_a=\{(1,0)\}$；
  $K_b=\{-\frac{c}{|c|}:c\in P,\ c\ne0\}$；
  $K_c=\{x\in\partial D:\exists\,c\ne c'\in P,\ |x-c|=|x-c'|\}$（每对不同位置恰给 2 个互异交点，L2'）；
  $K_d=\{$非共线三元组 $\{c,c',c''\}\subseteq P$ 的外心 $x$，**仅当** $|x|\le1\}$；
  $K(C)=K_a\cup K_b\cup K_c\cup K_d\subseteq D$。
- **基数上界** $|K(C)|\le 1+n'+2\binom{n'}{2}+\binom{n'}{3}$（**上界**：不同对/三元组的点可以重合，取等号一般不成立）。$n'=12$ 时 $\le365$。

**主定理** $\;R(C)=\max_{x\in K}f_C(x)$。等价地，对任意 $r\ge0$：
$$(\star)\qquad\Big[\forall x\in D:\ f_C(x)\le r\Big]\iff\Big[\forall x\in K(C):\ f_C(x)\le r\Big].$$
**加强版（本稿实际证明的）**：$f_C$ 在 $D$ 上每个**局部**最大点的值都在 $K$ 上取到（该点本身不一定属于 $K$，例如平台内部点）。

---

## 1 引理

**L1（存在）** $f_C$ 连续、$D$ 紧，$R(C)$ 取到；$K\subseteq D$ 给出 $\max_K f_C\le R(C)$，故只需找 $x_0\in K$ 使 $f_C(x_0)=R(C)$。

**L2（不同位置的中垂线过圆内部点）** 设 $c\ne c'\in D$，$m=\frac{c+c'}{2}$。$|m|\le\frac{|c|+|c'|}{2}\le1$；若 $|m|=1$ 则 $|c|=|c'|=1$ 且 $|c+c'|=2=|c|+|c'|$，三角形不等式取等给出 $c,c'$ 同向且等长，即 $c=c'$，矛盾。故 $|m|<1$：中垂线 $\ell$ 过内点 $m$，与 $\partial D$ 恰交两点。

**L2'（交点参数化；全稿统一的 $w$ 约定）** 记 $n=c'-c$，$\nu=|n|$，$N=\nu^2$，$H=|c'|^2-|c|^2$，$d=|H|/(2\nu)=|m\cdot\hat n|$（$\hat n=n/\nu$，即原点到中垂线的距离；由 L2，$d\le|m|<1$）；
$$\ell:\ 2x\cdot n=H,\qquad
x_\pm=\frac{H\,n\pm 2w\,n^\perp}{2N},\qquad n^\perp=(-n_2,n_1),\qquad
w:=\sqrt{N-\tfrac{H^2}{4}}=\nu\sqrt{1-d^2}>0 .$$
（即 $4w^2=4N-H^2=4\nu^2-H^2$，两式完全一致。）代入可验证 $x_\pm\cdot n=H/2$、$|x_\pm|=1$、$|x_+-x_-|=2\sqrt{1-d^2}>0$。
故**中垂线与圆相切/相离在 $C\subseteq D$ 下不可能**；$K_c$ 由每对**互异**两点组成。（集合基数可能因跨对重合而小于 $2\binom{n'}{2}$。）

**L3（内点分离方向）** 设 $x\in\operatorname{int}D$，$S=\{i:|x-c_i|=f_C(x)=:\rho\}$，$V=\{x-c_i:i\in S\}$（重复位置给同一向量）。若 $0\notin\operatorname{int}\operatorname{conv}(V)$，则 $x$ 不是 $f_C$ 的局部最大点。
*证*：情形 (a) $0\notin\operatorname{conv}V$：严格分离给出 $v\ne0$，$v\cdot w>0\ \forall w\in V$；情形 (b) $0\in\partial\operatorname{conv}V$：支撑超平面给出 $v\ne0$，$v\cdot w\ge0\ \forall w\in V$。取 $x+tv$（小 $t>0$，$x\in\operatorname{int}D$ 保证在 $D$ 内）：对 $i\in S$，
$|x+tv-c_i|^2=\rho^2+2t\,v\cdot w_i+t^2|v|^2>\rho^2$（情形 (a) 一阶项 $>0$；情形 (b) 一阶项 $\ge0$ 且二阶项 $>0$）；对 $i\notin S$，小 $t$ 时距离仍 $>\rho$。故 $f_C(x+tv)>\rho$。$\square$

*几何读法*（内点局部最大必须 $0\in\operatorname{int}\operatorname{conv}V$）：
(i) 不同最近位置数为 1：$V=\{w\}$。若 $w\ne0$ 取 $v=w$（背离该中心径向增大）；若 $w=0$（$x$ 本身是中心，$f_C(x)=0$），则**任意**非零 $v$ 都行：对某个 $c_i=x$ 有 $|x+tv-c_i|=t|v|>0=f_C(x)$，只要 $v$ 避开有限多个使某中心恰落在射线 $x+tv$ 上的方向。
(ii) 不同最近位置数为 2：$V=\{w_1,w_2\}$，$|w_1|=|w_2|=\rho$。若 $w_1\ne-w_2$，取 $v=w_1+w_2$（两心连线垂向），$v\cdot w_i=\rho^2+w_1\cdot w_2>0$，两距离同时**一阶**增大；若 $w_1=-w_2$（$x$ 是两心中点），取 $v\perp u$，$u=(c_i-c_j)/|c_i-c_j|$：此时 $v\cdot w_1=v\cdot w_2=0$，两距离按 $|x+tv-c_i|^2=\rho^2+t^2|v|^2>\rho^2$ 同时**二阶**严格增大，故中点非局部最大点（沿 $\pm u$ 的一阶导数为 $\mp1$，只说明它不是严格极小，**不**用于结论）。
(iii) 不同最近位置数 $\ge3$：$0\in\partial\operatorname{conv}V$ 时由 (b) 排除；只剩 $0\in\operatorname{int}\operatorname{conv}V$。

**L4a（三点等距必非共线）** $\rho>0$，三个**不同位置**到 $x$ 距离都为 $\rho$ $\Rightarrow$ 不共线（三点在 $\partial B(x,\rho)$ 上，直线与圆至多交两点）。$\square$

**L4b（圆上单最近心的切向极大点 = 反径点）** $c=\rho_c e^{i\varphi}$，$\rho_c>0$，$g(\theta)=|e^{i\theta}-c|$：$g^2=1+\rho_c^2-2\rho_c\cos(\theta-\varphi)$，临界点仅 $\theta\equiv\varphi$（极小）与 $\theta\equiv\varphi+\pi$（极大，$g=1+\rho_c$）。
*推论*：若 $x^*\in\partial D$ 是最大点且唯一最近心 $c\ne0$（严格最近），则 $h=f_C|_{\partial D}$ 在 $x^*$ 邻域等于 $g$，$x^*$ 是 $g$ 的临界点且非极小，故 $x^*=-c/|c|\in K_b$。$\square$

**L5（原点平台）** 设 $0\in C$，$x^*\in\partial D$ 是最大点且 $0\in S$（原点取到最小距离）。则 $f_C(x^*)=|x^*-0|=1$，且 $f_C\le1$ 于 $D$。记 $T=\{x\in\partial D:f_C(x)=1\}$（闭，$\ni x^*$）。
- 若 $T=\partial D$：对每个 $c\ne0$、每个 $x\in\partial D$ 有 $|x-c|\ge1$；取 $x=c/|c|$ 得 $|x-c|=1-|c|<1$，矛盾。故 $P=\{0\}$（全中心在原点），此时 $R=1=f_C((1,0))$，$(1,0)\in K_a$。
- 若 $T\subsetneq\partial D$：取 $T$ 在 $\partial D$ 中的边界点 $x_0\in T$ 与 $x_k\in\partial D\setminus T$，$x_k\to x_0$；$f_C(x_k)<1$，取 $j_k$ 使 $|x_k-c_{j_k}|<1$，有限下标给出子列与固定 $j$：$|x_0-c_j|\le1$。又 $x_0\in T$ 给出 $1=f_C(x_0)\le|x_0-c_j|$，故 $|x_0-c_j|=1=|x_0|=|x_0-0|$；由 $|x_k-c_j|<1=|x_k|$ 得 $c_j\ne0$，于是 $(0,c_j)$ 是不同位置对且 $x_0\in\partial D$ 到二者等距：$x_0\in K_c$，$f_C(x_0)=1=R$。$\square$

---

## 2 主定理证明

取最大点 $x^*$（L1），$S=\{i:|x^*-c_i|=R\}$。

**情形 I：$x^*\in\operatorname{int}D$。** 由 L3，$0\in\operatorname{int}\operatorname{conv}(V)$；于是 $V$ 的仿射包为 $\mathbb R^2$，取 $3$ 个仿射无关向量，对应 $3$ 个**不同位置**、到 $x^*$ 等距、非共线（或用 L4a），故 $x^*$ 是它们的外心；又 $|x^*|<1$，所以 $x^*\in K_d$。$\square$

**情形 II：$x^*\in\partial D$。**
- **II.a $0\in S$**：由 L5，$K$ 中有点取到值 $1=R$。
- **II.b $0\notin S$ 且至少两个不同最近位置**：取 $c_i\ne c_j\in S$，$x^*$ 到二者等距且 $\in\partial D$，故 $x^*\in K_c$，$f_C(x^*)=R$。
- **II.c $0\notin S$ 且唯一最近位置 $c$**：$c\ne0$（否则 $0\in S$）且严格最近，由 L4b，$x^*=-c/|c|\in K_b$，$f_C(x^*)=R$。$\square$

**结论**：存在 $x_0\in K$ 使 $f_C(x_0)=R$；配合 L1 得主定理与 $(\star)$。把"最大点"换成"局部最大点"逐步仍成立（L3 只需局部最大性；L5 只用"值 $1$ 在某点被取到"；II.b/II.c 只用等距/严格最近），故加强版成立。$\blacksquare$

---

## 3 退化清单（逐项；均无附加假设）

| # | 退化 | 处理与依据 |
|---|---|---|
| 1 | **重复中心** | $R$ 只依赖 $P$，$K$ 按 $P$ 定义。重复对给 $n=0$，L2/L2' 前提不成立，故 $K_c$ 必须按**不同位置对**取（本定义如此）；$K_d$ 的 $\Delta_{ijk}:=\det(c_j-c_i,c_k-c_i)\ne0$ 自动排除含重复位置的三元组；$K_b$ 上重复只是同点重复列。$P=\{0\}$ 时 $K_b=K_c=K_d=\varnothing$，只有 $K_a$，而 L5 说明此时 $R=1=f_C((1,0))$：**$(1,0)$ 在此情形是唯一可用候选**。 |
| 2 | **共线三元组 / 全共线中心集** | $\Delta=0$：无外心，$K_d$ 不贡献（正确）。更强：L4a 给出"$\ge3$ 个不同位置同时最近 $\Rightarrow$ 自动非共线"，故共线三元组不可能是内点最大点来源。若全部中心共线，则最近不同位置数 $\le2$，由 L3 读法 (i)(ii) 内点无局部最大点，最大点在 $\partial D$，由 $K_a/K_b/K_c$ 覆盖。 |
| 3 | **边界相切**（两处，须分清） | (i) $K_c$ 那半**不可能**：$L2/L2'$ 给不同位置的中垂线必过圆内点、与 $\partial D$ 恰交两点（无相切、无相离）。(ii) 真正相切的是**最近心的等距圆** $\partial B(c,R)$ 与 $\partial D$ 在最大点 $x^*$ **相切**（$x^*$ 是该圆上的点，不是圆心：$x^*=-c/\|c\|$，两圆在 $x^*$ 的法向共线）；这正是 L4b 的切向临界条件。(iii) 三元组外心**恰落在** $\partial D$（$|x^*|=1$）不是缺口：此时它同时属于 $K_c$（II.b）与 $K_d$（$|x|\le1$），只是重复计数。 |
| 4 | **原点平台（唯一最近心为原点）** | L5：$0\in C$ 时 $f_C\le1$；含 $0$ 的边界最大点给出 $R=1$。$T=\partial D$ $\iff$ 全中心在原点（用 $(1,0)$）；$T\subsetneq\partial D$ 取平台分量端点 $x_0$（与原点及某非零中心 $c_j$ 同时等距 $1$）$\in K_c$ 且取到 $R$。$0$ 是最近心但非唯一时同样适用。 |
| 5 | **$K_d$ 的 $|x|\le1$ 过滤** | 其精确作用是保证 $K\subseteq D$，从而 $\max_Kf_C\le R(C)$，即 $(\star)$ 的"$\Rightarrow$"方向（$D$ 被覆盖 $\Rightarrow$ 所有候选点被覆盖）与判据的**等价性**。若去掉过滤，$K'$ 含 $D$ 外点，$\max_{K'}f_C$ 可以远超 $R$（校准读数：`collinear-3+random` 未过滤 $76.441$ 而 $R=1.000$），此时判据**只剩充分方向**（sound：$K'$ 仍含最大点，故"各点被覆盖 $\Rightarrow R\le r$"），但不再等价——真实覆盖可能通不过判据。 |
| 6 | **$n=1$ / 全重合 / 部分类为空** | $K_a$ 恒非空。$P=\{c\},c\ne0$：$K=\{(1,0),-c/\|c\|\}$，$R=1+\|c\|$ 在反径点取到。 |
| 7 | **中心恰在边界（$\|c\|=1$）** | 无额外退化：中垂线仍过内点（L2）；反径点仍 $\in\partial D$。 |

---

## 4 四类候选的不可省性（每类都必需）

| 类 | 见证 $C$ | $R(C)$ 与取到点 | 其余类的最大值 |
|---|---|---|---|
| (a) | $\{(0,0)\}$ | $1$，$(1,0)\in K_a$ | $K_b=K_c=K_d=\varnothing$（去掉 (a) 则 $K=\varnothing$） |
| (b) | $\{(0,0.9)\}$ | $1.9$，反径点 $(0,-1)\in K_b$ | $K_a$ 上 $1.345362404707371$ |
| (c) | $\{(\frac12,0),(-\frac12,0)\}$ | $\frac{\sqrt5}{2}=1.118033988749895$，$(0,\pm1)\in K_c$ | $K_a=K_b$ 上 $0.5$ |
| (d) | 正十二边形（$\rho=1$） | $1$，原点 $\in K_d$（三元组 $0°,120°,240°$ 的外心） | $K_a\cup K_b\cup K_c$ 上 $\le2\sin7.5^\circ=0.261052384440103$（反径点即顶点，值 $0$；$K_c$ 全在 $\partial D$） |

读数来源：`evidence/battery.json` 的 `argmax_kind`、`evidence/battery-stdout.txt` 的 `ess-*` 段落。

---

## 5 两个等价表述（压缩；均与 §2 同一分类一致）

**A. Voronoi 裁剪单元 + 凸性。** 按不同位置 $c$ 定义 $V_c=\{x:|x-c|\le|x-c'|\ \forall c'\in P\}$，$D_c=V_c\cap D$（凸紧，$D=\bigcup_cD_c$，$f_C\equiv|\cdot-c|$ 于 $V_c$），故 $R(C)=\max_c\max_{D_c}|x-c|$。紧凸集上的**凸**函数 $x\mapsto|x-c|$ 在极点取到最大值，而 $D_c$ 的极点只可能是：(i) 两条不同中垂线约束的交点 = 三元组外心 $\in K_d$；(ii) 中垂线与 $\partial D$ 的交点 $\in K_c$；(iii) $\partial D$ 弧段上的点：弧内临界点为反径点 $\in K_b$（L4b），或沿弧为常数（$c=0$，其值 $1$ 在弧端点 $\in K_c$ 或全圆时 $(1,0)\in K_a$ 取到, 见 L5）。故 $\max_{D_c}|x-c|\le\max_Kf_C$ 对每个 $c$ 成立。$\square$

**B. 抛物面提升（线性化）。** 记 $h(x)=|x|^2$、$L_c(x)=2c\cdot x-|c|^2$（抛物面在 $\Phi(c)=(c,|c|^2)$ 的切平面的线性部分），恒等式 $|x-c|^2=h(x)-L_c(x)$ 把距离比较化为**线性**比较 $|x-c|^2\le|x-c'|^2\iff L_c(x)\ge L_{c'}(x)$（$|c|^2$ 线性出现，无分母、无根号）。于是 $V_c$ = 上包络 $U=\max_c L_c$ 的分支，$f_C^2=h-U$，$R(C)^2=\max_D(h-U)$。局部极大的读法：
- $U$ 的**折点**本身不是极大的充分条件：若只有 2 个分支活跃（点在 Voronoi 边内部），由 L3 排除；只有活跃分支 $\ge3$ 且梯度 $\{2(x-c_i)\}$ 的凸包以 $0$ 为内点时才可能是内点极大，此时 $x$ 是三元组外心 $\in K_d$；
- $U$ 的光滑点：$\nabla(h-U)=0\iff x=c$，是**极小**（与 L3(i) 一致）；
- $\partial D$ 上的切向临界点 $\to K_b$；$U$ 分支与 $\partial D$ 的交点 $\to K_c$；平台 $\to K_a$（L5）。

**读法纠正**：上述结构是 **nearest-point** Voronoi（提升点集的**下**凸包与切平面上包络互为对偶），**不是** farthest-point Delaunay；且 $K_d$ **不等于**任何凸包/包络的投影集合——它是"所有可能的内点极大点"的**代数超集**（任意非共线三元组的外心 + $|x|\le1$ 过滤）。超集是必要的：$K_d$ 中大量点不是任何 Voronoi 顶点（例：ring+origin 族里 \(D\) 内的圆外心落在三角形外），它们只影响候选规模、不影响正确性（正确性只需超集含最大点，见 §2）。

---

## 6 与 n=12 主目标的接口与范围

**能做什么**
1. 对**固定**构型：$(\star)$ 把"$D$ 被 $n$ 个半径 $r$ 闭盘覆盖"化为有限多个代数点上的检查（$n'=12$ 时至多 $365$ 个：1 固定点 + 12 反径点 + 每对 2 个中垂线圆交点 + 每个非共线三元组 1 个 $D$ 内外心）。任意构型、含全部退化均成立，无需接触图/一般位置假设。
2. **最大点类型分类**：最优半径处的最大点只能属于 §2 的四类之一，故紧性条件可用"等距 / 切向 / 外心 / 平台端点"的代数条件表述。
3. 消去定义域上的 $\forall x$：后续量词消元只需处理"$\forall$ 中心位置"与有限代数条件（见 `QE-interface.md`）。

**不能做什么**：不给 $r_D(12)$、不排除任何 $r<r_D(12)$ 的覆盖；全局最优仍需对所有中心位置的量词消元或构型分类。中心允许在 $D$ 外时 L2 与 L5 第 3 步需重证（本稿只按 $C\subseteq D$）。

**接口观察（只读，不作裁决）**：旧 D2 装置 `research-2026/session2/n1314/py/cert_cand.py` 的候选族正是 (b)(c)(d)，其 `__main__` 断言中心互异；结构缺口即 **(a) 固定点/原点平台**与**重复、共线、原点退化**。$12+132+220=364$ 与旧输出 `cover_n_cand=364` 一致；`cover_n_uncovered=36` 与 REPORT 的 $0/328$ 的口径差异仍以旧脚本自身语义为准，本目录不据此改任何旧 claim。

**数值校准**：222 例 battery（含退化族、四类不可省性见证、C182 只读诊断）+ 28 例两边界检查。关键**反证式**读数（不依赖优化器）：密格点上 $\max_{\rm grid}f_C-R_{\rm cand}$ 的最大值为 $0.0$（从未出现"格点值 > 候选最大值"）；高分辨检查同。C182 只读诊断 $R_{\rm cand}=0.361102963745$，与登记上界 $0.361102963744508672616920293904$ 在 $10^{-12}$ 内一致（诊断读数，非重认证）。详见 [`NUMERICS.md`](NUMERICS.md)。
