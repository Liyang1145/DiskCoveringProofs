<!-- SPDX-License-Identifier: MIT -->
# Mathematical reader's guide / 数学读者导读

This guide translates the archived source arguments into standard mathematical
language. It describes what those sources claim and where their bearing
arguments are located. A saved acceptance report, a claim identifier, or a
matching hash is not an additional mathematical proof. For the scope of a
fresh execution, read the checker output and its documented check list.

## 1. The problem and the kinds of evidence

Let $D=\{x\in\mathbb R^2:\lVert x\rVert\leq1\}$. For $n$ congruent closed disks,
write

$$
r_D(n)=\inf_{c_1,\ldots,c_n\in\mathbb R^2}
\max_{x\in D}\min_{1\leq i\leq n}\lVert x-c_i\rVert.
$$

The competing centers are arbitrary. Repeated centers, centers outside $D$,
tangencies, and degeneracies must be handled by the lower-bound reduction.
Symmetry of an attaining configuration does not impose symmetry on a competitor.

An equality $r_D(n)=r_*$ requires two different arguments:

1. **Attainment:** explicitly defined centers cover every point of the closed
   disk at radius $r_*$, including its interior.
2. **Lower bound:** every hypothetical cover of radius $r<r_*$ is reduced to
   necessary geometric constraints, and every resulting case is excluded.

An exact root needs equations, a specified branch or isolating box, and a root
existence/uniqueness proof. A printed decimal or a successful numerical Newton
solve alone does not define the exact answer. Uniqueness in an isolating box
also does not classify all optimal configurations.

The archive contains analytic arguments, computer-assisted rational or directed
interval certificates, and historical source acceptance records. It does not
claim complete Lean/Coq formalization or external peer review. In particular,
the separate ongoing $n=11$ Lean project must not be confused with the completed
archived $n=11$ **source-proof claim**.

## 2. Eleven disks: from arbitrary covers to a network inequality

Read the [global theorem](../cover11/proof_bundle/research-2026/team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md)
first, then its [interface ledger](../cover11/proof_bundle/research-2026/team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md).
The latter explains the reductions, degeneracies, graph classes, and exact
domains which make the numerical certificates relevant.

| Standard mathematical step | Archive identifier | What must be established |
|---|---|---|
| Define the exact candidate | `C891` | A unique root of the specified 12-equation contact/stationarity system in its dyadic box; its radius is coordinate 6, with zero-based indexing. |
| Prove attainment | `C892` | Boundary arcs and all interior nearest-distance maxima are covered by the same root configuration. |
| Exclude ten boundary disks and one hub | `C450` | A weighted two-circle capacity bound, including its full parameter domain. Its single-disk inequality is also used to force hub adjacency. |
| Reduce arbitrary covers | `C923` | Nine boundary disks, two interior hubs, connected owned arcs, an embedded refined dual, and exhaustive topology/metric exclusions. |
| Lower-bound the surviving network | `C921` | A convex oracle inequality over the entire closed eight-dimensional anchor-deficit simplex. |
| Identify the same radius in all certificates | `C922` | The rational energy threshold lies above the very same `C891` radius, and below $19/50$. |
| Assemble attainment and lower bound | `C924` | $r_D(11)=r_*$ without symmetry or a prescribed topology for competitors. |

The lower-bound chain in ordinary language is as follows.

1. Boundary arc capacity and the weighted two-circle inequality force nine
   boundary disks and two indispensable interior disks. Replacing a boundary
   center by the inner radial root of its **actual** arc preserves coverage.
   Nearest-site ownership is then rebuilt.
2. The two hub Voronoi cells share an edge. Locality bounds restrict ring edges;
   refined Delaunay faces retain genuine nearest-point witnesses. Classification
   and full-domain metric exclusions leave the no-ear, hub-degree $(6,7)$ graph.
3. Keep nine boundary switches as anchors. Eleven site nodes and eleven face
   witnesses enter a convex network relaxation with 51 distance constraints.
   A real cover supplies a feasible network, hence its optimum $V(U)$ satisfies
   $V(U)\leq r$. This implication is only needed in this direction.
4. Owned arc-width deficits give an unrestricted closed eight-dimensional
   simplex. Positive network stresses, exact Schur elimination, interval cosine
   minorants, and closed-domain splits prove $V(U)\geq r_*$. The final source
   tree has **2386 energy leaves and 120 direct local leaves**. These counts
   describe this particular certificate tree, not the twelve-disk tree below.

Thus a smaller cover would imply $r_*\leq V(U)\leq r<r_*$.
The exact eleven centers give the reverse inequality.

The source theorem encloses the radius between
`0.3799838531198386897222616061358` and
`0.3799838531198386897222616061364`.
The isolating system and box, rather than either endpoint, define $r_*$.

中文路线：`C891` 定义同一个精确候选根，`C892` 证明达到整个闭盘。
下界先由双圆容量与最近点所有权得到九个边界盘、两个内部盘，再由完整图分类与
度量排除留下无耳的 $(6,7)$ 图。真实覆盖给固定锚点网络一个可行解，因此
$V(U)\leq r$；全八维角域的能量叶和局部叶给 $V(U)\geq r_*$，从而排除更小半径。
候选的反射对称性不约束竞争覆盖，隔离盒唯一性也不证明最优构型全局唯一。

## 3. Twelve disks: three boundary-activity cases

Read [GLOBAL-SYNTHESIS.md](../cover12/proof_bundle/research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md)
for the statement registered as `C1141`, and
[K10-FULL-EXCLUSION.md](../cover12/proof_bundle/research-2026/n12-global/lead/K10-FULL-EXCLUSION.md)
for the largest finite branch.

The exact answer is the radius coordinate of the uniquely isolated solution
of the four algebraic equations $F=G=H=T=0$ stated in the synthesis. Its printed
value begins `0.36110296374450864411308770201706518`.
The explicit three-hub construction is checked over the whole closed disk.

The lower bound first projects centers to $D$ and bounds the number $k$ of
boundary-active disks. The only possible counts are $k=9,10,11$; tangencies
are included in activity. The nine-active case has its own network lower
bound. For ten or eleven active disks, enlargement to a fixed exact rational
radius $U>r_*$ is used, with the activity count controlled after enlargement.
Eleven active disks are excluded. Ten active disks leave two strict interior
hubs. Near-coincident and excessively separated hubs are excluded separately.

For the remaining pair, rotation, reflection, and relabeling give
$h_1=(x-s,y)$, $h_2=(x+s,y)$ in the rational box

$$
[1/20,U]\times[0,1-U-1/20]\times[0,3U-1].
$$

The `k10` certificate partitions this **whole** necessary hub-pair domain.
The archived complete tree has **7041 terminal boxes**:

- **318 infeasible boxes:** a necessary inactivity or core-coverage condition
  is contradicted.
- **6723 atomic certificates:** screened boundary/hub atoms must be covered
  by the ten ring disks; nonnegative integer weights give demand $T$ and a
  rigorous per-ring capture bound $M$, with **$10M<T$**.

The tree has 7040 internal binary nodes and no pending terminal box in its
historical complete manifest. Both domain coverage and the inequality at every
terminal box are necessary. A content join, saved `pass` flags, or a partition
check does not rerun all atomic ring-center subdivisions. Fresh commands must
report precisely which of these obligations they check.

The finite atomic measure is not a quadrature approximation. Numerical LP
solutions propose weights; exact weight signs and capture inequalities, rather
than numerical optimality, carry the exclusion. The analytic screening rule
which makes a moving atom necessary must also be retained.

中文路线：十二盘按边界活跃盘数分成九、十、十一三类。`k10` 指十个盘接触圆周，
总覆盖盘数仍是十二；剩余两个内部盘的规范化参数进入一个三维有理根盒。
全部 7041 个终端盒必须覆盖此根盒，318 个用必要条件判不可行，6723 个用
非负整数权原子容量严格排除。检查树的覆盖或证书来源一致性不能替代逐个重新
计算 $10M<T$。LP 仅生成候选权，数学负担在精确符号、筛选条件和容量上界。

## 4. Other orders and the unfinished frontier

The individual [fourteen-disk theorem](../cover14/proof_bundle/research-2026/next-cover-global/lead/FINAL-THEOREM-CHAIN.md)
is registered as `C1372`. It joins exact attainment, arbitrary-cover topology
reduction, continuous-domain exclusions, and a local same-root lower bound.
Its internal claim numbers do not change the meanings of the eleven- or
twelve-disk results.

For $n=21$ through $25$, start with the per-order README and its final acceptance
record. They distinguish the final chain from earlier shared drafts. In
particular, an old shared manuscript saying that other orders remain open is
historical, not a replacement for a later per-order final record.

The [twenty-two-disk source theorem](../shared/proof_bundle/research-2026/n21-25-synthesis/round3-high/N22-GLOBAL-PROOF.md)
uses $r_*=\sqrt{t_*}$, where $t_*$ is the unique root of
$29t^3-55t^2+19t-1=0$ in $(641/10000,321/5000)$. The polynomial is in the
**squared radius**, not the radius. Its attaining candidate has $D_7$ symmetry;
that symmetry is not a premise for competing covers.

[The twenty-six-disk project](../cover26/README.md) remains incomplete.
Its `root25` arithmetic branch is an internal label within the **$n=26$** work.
Formal candidate-root counts and arithmetic open-subdomain counts are different
objects and cannot be substituted for one another or subtracted.

## 5. A practical reading and checking order

1. Read the per-order theorem and its scope, then the analytic reduction and
   certificate interfaces. Use the [notation dictionary](NOTATION.md) for names.
2. Verify the delivered bytes and restore losslessly packaged files. These
   operations establish which inputs you have; they do not establish a lower
   bound.
3. Run the mathematical checks and inspect their fresh report. Root isolation,
   whole-disk attainment, complete domain partition, and all leaf inequalities
   are separate obligations. A partial check must remain explicitly partial.
4. Resolve the unsubmitted dependencies and original path mappings before
   attempting an archived full-chain replay. Consult
   [DELIVERY_SCOPE.md](DELIVERY_SCOPE.md) and [PROVENANCE.md](PROVENANCE.md).

中文导读：先读分阶定理，再读任意覆盖如何进入证书域的归约；编号是查找索引，
不是数学论证。上界需要覆盖整个闭盘，下界需要排除所有更小半径的任意配置。
$n=11$ 的源证明与另一个尚未完成的 Lean 形式化项目须区分；$n=12$ 的
7041 个终端盒属于十个边界活跃盘分支，其中 318 个不可行、6723 个原子证书。
字节完整性、同根关联、树的完备覆盖和逐叶数学不等式是不同检查。历史接受记录
保存其原作用域；本次复现通过多少项目，应以新鲜执行报告为准。$n=26$ 仍未闭合。
