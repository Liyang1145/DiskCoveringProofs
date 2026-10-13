# taylor-audit — 独立复核 k9 非候选 witness-network Taylor 证书 + graphs.json 枚举

复核者：finite-reduction（本成员）。**只读** `lead/network_interval_certificate.py`、`lead/stress_interval.py`、`lead/network_graph.py`、`members/nine-topology/{gen_graphs.py,graphs.json}` 与 `evidence/network-certified-*.json`；未做任何修改。
结论：**未发现被复核代码或证明的错误**；60 个证书全部通过我的独立核；`graphs.json` 的 56 个类型与我的独立穷举枚举**一一对应**。
等级声明：PASS 是**审计读数**，不是认证；本文件不新增 claim、不改变任何结论的等级。

---

## 1 复核对象与口径

- 每个证书主张：对记录的**精确有理**边应力 $\alpha$、精确有理单纯形参考 $y$ 与记录的 $\kappa$，
  $$\underbrace{E(\theta_0)}_{E_0}+\min_{\text{vertex}}\big(\nabla E(\theta_0)\cdot(\theta-\theta_0)\big)-\frac{\kappa}{2}\max_{\text{vertex}}\|\theta-\theta_0\|^2\;>\;U^2,\qquad U^2=0.13039535042506794487662692772894\ldots$$
  其中 $q$ 来自 25 个内部节点的 Dirichlet 消元，$M$ 由 $\cos(dL)=T_d(1-2U^2)$ 构造，且 $M+\kappa I$ 在**全 9 维**上正定（非仅某个方向）。
- 本次复核 60 个证书：`network-certified-{117,126,135,144,225,234}.json`（原 6 个 T3）+ `M1`、`M2-*`(4)、`P2-*`(4)、`P3-*`(16)、`P4-*`(20)、`T2-*`(4)、`T3-*`(5，与原 6 个 T3 中 5 个同名重复) = 55 个**不同类型** + 5 个重复文件。
- scope：只核证书自身的数学内容（Schur 应力能量 → Taylor 下界 → 排除该 witness 网络）。**未**核"半径 $\le U$ 覆盖 $\Rightarrow$ 此 witness 网络/锚点间隙 $\le L$"这一几何接口，也**未**核 k10/k11 分支。

## 2 独立性（与 Lead 实现不同的推理/实现）

| 环节 | Lead 实现 | 本次独立实现 |
|---|---|---|
| Dirichlet/Schur 消元 | $10^{-45}$ 十进制区间网格 | **精确 `fractions.Fraction`，两条不同路径**：(a) 原地对称消元（Lead 的节点顺序）；(b) 不同路径——Gauss–Jordan 解 $A_{\rm int}X=B$ 后 $S=L_{aa}-B^{T}X$。两者**逐项相等**才算通过 |
| $M+\kappa I$ 正定 | 区间 LDL | **精确有理 LDL**（全部 9 个主元 $>0$；数据全为精确有理，无需区间） |
| 三角函数 | 40 项区间 Taylor + Lagrange 余项 | **二进制定点（$2^{-240}$）区间核**：参数折半 + 倍角恒等式 + 交错级数核心，余项用**交错级数首遗漏项**界；整数 floor/ceil 外舍 |
| $\pi$ | Machin 65/20 项 | 独立 Machin 110/32 项（精确有理交错界），检查**我的窄区间 $\subseteq$ 记录的宽区间** |
| $L=2\asin U$ | 断言 $\sin(l_o/2)<U<\sin(l_i/2)$ | 用**我自己的定点 sin** 重验该断言 |

定点核自校准：400 个随机有理 $x\in[-2.9,2.9]$ 的 $\sin/\cos$ 区间对 mpmath（160 位）**全部包含**，最小余隙 $\ge1.9\times10^{-70}$。

## 3 批量结果（60 个证书，全部通过）

每个证书 18 项检查全部 PASS：face mapping（我按"锚点 $i$ ↔ 站点 $i,i+1$ + 各 face 及其三顶点"独立重建的边表与记录**逐项一致**）、权重正且归一（且与 proposal 的 $10^{-10}$ 四舍五入规则一致）、两条 Schur 路径一致、Dirichlet 主元全正、Schur 非对角 $\ge0$ 且湮灭常数向量、$M+\kappa I$ 精确正定、$\pi/L/D$ 常量核对、参考点在单纯形内且间隙合法、**Taylor 下界 $>U^2$**；且 $E_0$、线性项最小值、$\max\|\cdot\|^2$、下界四项与记录区间**全部相交且我的更窄**。

| 族 | 证书数 | 我的 margin（float） |
|---|---|---|
| M1 | 1 | 2.4452e-02 |
| M2 | 4 | 9.59e-03 … 2.45e-02 |
| P2 | 4 | 9.59e-03 … 2.42e-02 |
| P3 | 16 | **4.5171e-03**（P3-3-2-4，最小）… 2.32e-02 |
| P4 | 20 | 9.49e-03 … 2.39e-02 |
| T2 | 4 | 9.59e-03 … 2.45e-02 |
| T3 | 6（原） | **2.9260e-04**（234，最小）… 1.48e-02 |

与 Lead 报告的"最小 margin .004517111744（P3-3-2-4）"一致；closest 234 的 margin 2.926038e-04 与记录一致。**无任何 FAIL**。

## 4 graphs.json 枚举复核（不靠数量）

1. **结构复验**：56 个图的 Euler（$V-E+F=1$）、$F=7+2m$、$E=15+3m$、9 条 RR 边仅边界 spokes、hub 图连通、每环的 hub 邻接构成 $H$ 中的路且环上内面数 $=t_i-1$、环度 $=t_i+2$ —— **0 失败**（独立实现）。
2. **完备性（穷举，非计数）**：对 $H\in\{K_1,K_2,K_3,P_3\}$（$m\le3$）穷举全部 9 个环标号序列 $\times$ 每个 transition 的链选择（一步/故意的两步链），施加 `K9-TYPE-LIST.md` §1 的三条件：$q_i$ 是 $H$ 中的简单路、$\sum_i(t_i-1)=(2m-2)-[H=K_3]$、$q_1..q_9$ 拼接（$K_3$ 时加 $(0,3)$ 三角边界）每条 hub 边恰走两次。
   - 结果：**独立穷举得 56 个规范类型**，与 `graphs.json` 的 56 个**一一对应**（enumerated∖listed $=0$，listed∖enumerated $=0$）。
   - 结论：就"链/walk 刻画"而言，类型表**完备且无冗余**；**零块退化**（T2 的单空块、P2 的双空块、P3 的两步链）由穷举自身产生，未被遗漏——即 INTERFACE.md §D.4(c) 所说的"零块面已含在内"在我这层得到确认。
3. **未核部分（界限）**：我只把 §1 的链/walk 刻画当作**输入**；从几何（E1–E5、`K9-DUAL-DISK.md` Theorem A/B）导出该刻画不在本次范围。类型计数的等价关系（旋转/反射/hub 改名）按 `K9-TYPE-LIST.md` §2 的口径实施。

## 5 复核中发现的问题（全部在我自己的审计代码里，已修）

1. 定点级数递推有**双重取负**符号错（导致 $\sin/\cos$ 全错）。
2. $K_3$ 边写为 `(2,0)` 未排序，导致 $(0,2)$ 邻接判断失败（漏掉 T3/T2）。
3. 规范化的循环 run 未跨首尾合并（产生伪类型）。
4. $H=K_1$ 的枚举项被 `nh != m` 跳过（漏掉 M1）。
5. "可用两步链"条件写成"链数 $\ge2$"（应"存在长度 3 的链"），漏掉 P3/P2 族。
以上均为我的实现错误；修正后结果自洽（56↔56）。**被复核的 Lead 代码与证明未发现错误**。

## 6 复现

```powershell
cd research-2026/n12-global/members/finite-reduction/taylor-audit
py -3 -B audit_taylor.py            # 6 个原 T3 证书
$f = Get-ChildItem ..\..\..\evidence\network-certified-*.json | % FullName
py -3 -B audit_taylor.py --files @f # 全部 60 个
py -3 -B audit_graphs.py            # graphs.json 结构与完备性
```
输出：`out/audit-report.json`、`out/graph-enumeration-audit.json`。
