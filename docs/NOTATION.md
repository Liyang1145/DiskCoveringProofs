<!-- SPDX-License-Identifier: MIT -->
# Notation and archive dictionary / 记号与内部编号词典

Internal identifiers locate an archived statement or run. They are not standard
geometric terminology, certification levels, polynomial names, or theorem
numbers in an external publication. The same mathematics should be read through
the statement and its domain. Start with [MATHEMATICAL_GUIDE.md](MATHEMATICAL_GUIDE.md).

## Geometric and certificate notation

| Symbol or term | Mathematical meaning / 中文释义 | Scope caution |
|---|---|---|
| $D$, $S^1$ | The closed unit disk and its boundary circle / 单位闭盘、单位圆周 | The problem includes the interior, not just the boundary. |
| $r_D(n)$ | Minimum radius for an $n$-disk cover / $n$ 个等半径闭盘的最小覆盖半径 | Centers are arbitrary in $\mathbb R^2$. |
| $r_*$, $R^*$ | An exact candidate radius / 精确候选半径 | Equations and an isolating box define it; a decimal does not. |
| $U$, $R_0$ | A certified rational comparison radius / 有理比较半径 | Its use and enlargement rule are specific to each reduction. For the eleven-disk metric certificates, $R_0=19/50$. |
| Site / center | A covering-disk center / 覆盖圆心 | A site in a relaxed network need not retain every property of a true covering center. |
| Ring or boundary-active disk | A disk meeting the target boundary / 与目标圆周相交的盘 | The activity definition may include a single tangency; ownership is a separate property. |
| Hub | An interior center in the reduced graph / 归约图中的内部圆心 | Hub status is proved by a reduction, not assumed for arbitrary competitors. |
| Owned boundary arc | Points on $S^1$ where a site is nearest / 最近点圆周所有权弧 | Disk footprints and owned arcs need not be identical. |
| Switch / anchor | A boundary transition between nearest sites, used as a fixed network node / 圆周所有权切换点、网络锚点 | Index conventions may shift; use the source incidence map. |
| Face witness | A common point within radius $r$ of the face's sites / 面各顶点的共同距离见证 | A true Voronoi witness can become a free node in a relaxation; a converse implication is unnecessary. |
| Clipped Voronoi cell | A nearest-site cell intersected with $D$ / 截于目标盘的 Voronoi 胞腔 | Replacing centers requires rebuilding ownership. |
| Ear, $q$ | A boundary triangle removed in a graph reduction; $q$ counts ears in the eleven-disk reduction / 边界耳三角形及其数量 | $q$ is not the disk count. |
| Stress / force certificate | Nonnegative network energy weights or balanced vector flows giving a rigorous bound / 应力能量或平衡杆流证书 | Distinguish squared-distance energies from vector work bounds. |
| Oracle $V(U)$ | Minimum feasible radius of a network with fixed anchors $U$ / 固定锚点网络的最小可行半径 | Here $U$ denotes anchor data, not a rational scalar radius. |
| DBM | Difference-bound matrix for linear difference constraints / 差分约束矩阵 | The complete closed split tree is required, not just sampled feasible points. |
| Leaf / terminal box | An endpoint of a domain-partition tree / 域划分树终端盒 | A leaf can be infeasible, strictly excluded, locally bounded, or still open. |
| Krawczyk / contraction check | An interval or rational test establishing a boxed system root / 隔离盒根的区间或有理压缩验证 | The local uniqueness it proves is not global uniqueness of optimal covers. |
| Manifest / SHA256 | Inventory and identity of bytes / 文件清单、内容身份 | Integrity supports reproduction but does not imply a mathematical inequality. |
| Source acceptance | A saved acceptance of the analytic/computational chain / 源证明历史接受记录 | Separate from fresh replay, proof-assistant formalization, and peer review. |

## Frequently encountered internal identifiers

| Identifier | Standard description / 标准描述 | Authoritative reading entry |
|---|---|---|
| `C450` | Eleven-disk weighted two-circle capacity inequality; excludes ten boundary disks plus one hub at radii $\leq19/50$, and supplies a stronger per-disk atom / 加权双圆容量不等式 | [Eleven-disk interface ledger, §§1 and 3](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md) |
| `C891` | Unique isolated contact/stationarity root defining the eleven-disk radius / 十一盘接触与驻定系统的隔离根 | [Eleven-disk theorem, exact definition](../cover11/proof_bundle/research-2026/team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md) |
| `C892` | Whole-disk attainment by that same eleven-disk root / 同根构型覆盖整个闭盘 | [Eleven-disk theorem](../cover11/proof_bundle/research-2026/team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md) |
| `C919`, `C920` | Local angular/stress lower bounds near the same eleven-disk root / 同根附近角域与应力局部下界 | [Interface ledger, §§7–8](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md) |
| `C921` | Full closed anchor-simplex lower bound for the canonical eleven-disk oracle / 标准网络全闭锚点单纯形下界 | [Interface ledger, §§6–7](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md) |
| `C922` | Exact comparison between the eleven-disk isolated root and the energy threshold / 隔离根与能量阈值的精确比较 | [Interface ledger, §8](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md) |
| `C923` | Reduction of unrestricted eleven-disk covers to the certified oracle / 任意十一盘覆盖至认证网络的归约 | [Interface ledger](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md) |
| `C924` | Assembled eleven-disk global optimum / 十一盘全局最优性合成 | [N11-GLOBAL-OPTIMALITY-THEOREM.md](../cover11/proof_bundle/research-2026/team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md) |
| `C985` | Exact twelve-disk attaining construction / 十二盘精确达到构型 | [Twelve-disk synthesis](../cover12/proof_bundle/research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md) |
| `C986` | Sharp lower bound for twelve-disk covers with nine boundary-active disks / 十二盘九个边界活跃盘分支的尖锐下界 | [Twelve-disk synthesis, step 3](../cover12/proof_bundle/research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md) |
| `C1139` | Complete ten-active-disk branch exclusion for twelve disks / 十二盘十活跃盘完整分支排除 | [K10-FULL-EXCLUSION.md](../cover12/proof_bundle/research-2026/n12-global/lead/K10-FULL-EXCLUSION.md) |
| `C1141` | Assembled twelve-disk global optimum / 十二盘全局最优性合成 | [GLOBAL-SYNTHESIS.md](../cover12/proof_bundle/research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md) |
| `C1372` | Assembled fourteen-disk global optimum / 十四盘全局最优性合成 | [FINAL-THEOREM-CHAIN.md](../cover14/proof_bundle/research-2026/next-cover-global/lead/FINAL-THEOREM-CHAIN.md) |
| `k9`, `k10`, `k11` in $n=12$ | Counts of boundary-active disks / 十二盘分支的边界活跃盘数 | [Twelve-disk synthesis](../cover12/proof_bundle/research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md). `k10` still concerns **twelve** covering disks. |
| `7041` | Terminal hub-pair boxes in the complete twelve-disk `k10` tree / 十二盘十活跃分支的终端盒总数 | [K10 certificate, §3](../cover12/proof_bundle/research-2026/n12-global/lead/K10-FULL-EXCLUSION.md): 318 infeasible + 6723 atomic. |
| `root25` in $n=26$ | Label of an independent arithmetic branch of unfinished twenty-six-disk work / 二十六盘未完工作的一条独立算术支编号 | [cover26/README.md](../cover26/README.md). It is not the optimum for $n=25$. |

## Index conventions

Site, face, anchor, edge, and root-coordinate numbers usually start at zero in
the programs. Permutations transport several kinds of objects and can shift
their indices differently. A diagram or the matching of graph labels alone
does not certify the coefficient or witness transport. Use the incidence map
and the explicit transport identities in the relevant source.

中文使用建议：引用时写“加权双圆容量引理（归档编号 `C450`）”或“十二盘十活跃盘
分支排除（`C1139`）”，先给数学名称，再保留编号供查证。`C891` 的唯一性仅指所给
隔离盒，`C924` 的全局性来自覆盖到证书域的完整归约；两者不能互换。
