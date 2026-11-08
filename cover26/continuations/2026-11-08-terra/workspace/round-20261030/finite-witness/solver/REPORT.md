# 有限点覆盖排除器原型

当前五圈 241 点实例并不能证明需要 27 盘。`geometry/five_ring_exact.json` 含 913 个极大覆盖 mask；`five_ring_cover23.json` 给出 23 个 mask 已覆盖全部 241 个点，`verify.py` 已用逐位整数运算重放。`geometry` 侧另行给出圆心见证并进行精确几何核验。这个点集的弱度已被明确证实，不需要继续搜索它的 26 盘不可行证书。

## 数据与程序接口

输入 JSON（可 gzip）至少包含 `points` 数组与 `masks` 数组。每个 mask 是 Python 可解析十六进制字符串，位 i 表示覆盖 points[i]。生成器独立保证：每个可能圆心所得的 mask 被输入列表中的某个 mask 包含；同时为证明可行覆盖时提供每个 mask 的可实现圆心。**本目录的组合验证器不证明这两个几何性质。** 生成器是否完整、点是否在目标圆盘内、最大 mask 列表的精确性均由几何侧另行证明。

`solve.py` 使用 SciPy MILP 与 LP 作诊断，再在固定超时和最大节点下尝试构造可审核分支证书：

* 一个节点维护尚未覆盖的位集合 U 与剩余圆盘数 k。分支取 U 内一个点，并覆盖所有不同的 `mask ∩ U`。任意真正的覆盖必选某个含该点的 mask，所以这些分支穷尽；等投影去重不会丢失覆盖可能性。
* 有理权重叶由非负整数 `w_i` 给出：若未覆盖点总权 `sum_U w` 严格大于 `k * max_mask sum_(mask ∩ U) w`，则不可能由 k 个 mask 覆盖 U。权重可以由浮点 LP 提议，但验收只用整数。
* packing 叶列出 U 内超过 k 个点，每个 mask 最多包含其中一个；这些点不能被 k 个 mask 覆盖。
* 时间或节点限制触发即 `PENDING`，不产生排除证书。数值 LP/MILP 的 `infeasible`、最优值或界本身均不作为数学结论。

`verify.py` 是独立标准库验收器，校验原始输入 SHA256、每个分支的穷尽、每个叶的整数不等式或 packing 关系；也可检查覆盖见证。它只证明给定有限集合系统的结论，不能自行为几何域补全。

## 执行与回归

以下命令从 `n26-terra` 目录运行，限额均为有界，可自行减小：

    python round-20261030/finite-witness/solver/solve.py round-20261030/finite-witness/geometry/five_ring_exact.json --milp-seconds 20 --tree-seconds 15 --max-nodes 2000 --cover round-20261030/finite-witness/solver/five_ring_cover23.json
    python round-20261030/finite-witness/solver/verify.py round-20261030/finite-witness/geometry/five_ring_exact.json round-20261030/finite-witness/solver/five_ring_cover23.json
    python round-20261030/finite-witness/solver/solve.py round-20261030/finite-witness/solver/toy_integer_gap.json --target 2 --milp-seconds 5 --tree-seconds 5 --max-nodes 1000 --certificate round-20261030/finite-witness/solver/toy_integer_gap_certificate.json
    python round-20261030/finite-witness/solver/verify.py round-20261030/finite-witness/solver/toy_integer_gap.json round-20261030/finite-witness/solver/toy_integer_gap_certificate.json

前两个命令严格验证给定 mask 中23个覆盖全部点，后两个是**纯合成集合系统**测试（与圆盘几何无关）：其 LP 值为2，3个集合覆盖而2个不行，验收器接受7节点证书。删除一个必要分支的篡改测试已被拒绝。LP 和 MILP 输出仅为诊断，排除结论由证书独立验收提供。

这条路线要推进 n26 仍须找到有限点实例，其对应完整 mask 系统确实不可能由26个 mask覆盖，并提供可独立验收的排除树及几何完整性证明。当前没有这样的实例或证书；n26 已知数学结论及 16/4957/344 原始未付义务均不因此改变。

当前文件 SHA256：`solve.py` = `7a3eac2062048d9b8bdd01a6d44fc3df4276fa8ac8a6cb98246083ed9be0f5f3`；`verify.py` = `24da3122f0e2315584d418217dd94c90f95d8c8308cb76eaa961a532b04ca427`；实例 `five_ring_exact.json` = `7e8bdf16b885cab4e1c552d8a854a3ed77fa5595b6afa70cd1863858ac8ae239`。

`project_subset.py` 可把某个完整或保守超集 mask 家族投影到指定≤400个点，输入为索引 JSON，或用 `--count 400` 按源顺序均匀抽取；输出保留源 SHA 和索引。理由是原家族中包含任意圆心 mask 的集合，投影后仍包含该圆心在子集上的 mask。若源家族只是保守超集，投影后的不可覆盖证书仍可用于排除，但其中某个 mask 未必可实现，其有限 mask 覆盖见证不能单独证明几何覆盖。对已精确完成的241点实例取120点并投影、去重后，已用验收器验证一个22-mask覆盖；这只是接口回归。
