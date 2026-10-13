# n=26：957 根未闭合叶由十个缩减至两个

2026-10-11。目标保持进行中；n=26 尚未完成，n=27 尚未开始。

本轮从实际已经验收的 957 根部分森林继续，只细分原来的十个 OPEN 叶。
原来的六个能量叶、十五个闭分割及共享中点均在原索引处保持完全相同。
新独立冻结验收已经通过。

| 指标 | 已验收来源森林 | 本轮独立验收森林 |
| --- | ---: | ---: |
| 完整闭分割 | 15 | 68 |
| 严格能量叶 | 6 | 67 |
| OPEN 叶 | 10 | 2 |
| 总节点 | 31 | 137 |
| 最大深度 | 4 | 8 |

新增 61 个严格能量叶。两个剩余 OPEN 叶没有被删除或视作空；
957 整根仍未闭合，全部原始闭根区间继续保留。实际候选待证整根数仍为 27。
这不是新增一个整根排除，也不是新的全局最优性证明。

所有叶域均由原始闭根重建，独立 BFS 与精确 DFS 的闭域一致。
每个新能量叶都用原始 92 条正权约束的严格有理能量界核验，
包括精确正 LDL、完整重建、舍入误差账本和非负差分对偶。
浮点搜索仅生成证书和分割方向。原 62 个顶点、16 个锚点、46 个接地自由顶点、
52 坐标映射、同根 Rstar 和局部容差 7/800000 不变。

八项种子保留拒绝测试、九项本轮实际证书拒绝控制与此前九项闭分支结构控制通过。
结构测试自身没有几何支付。原可行微小根和 LOCAL 等号可行区域保持保留；
本轮没有新增 LOCAL 叶，也没有把 LOCAL 半径下界解释为空性。

实际发布重放、完整当前衔接审计及独立最终文件复核单独记录，
只有它们也通过后，新部分森林才成为最新完整当前证据链中的候选来源。
组合层不受该细分删除影响：第十轮的实际待查子树为 6,094，
四族分别是 289 / 1,399 / 2,189 / 2,217。两条原候选完整终端仍保留，
87 个历史完整图型和 215 份证明回执继续核对。

实际记录：

- 独立验收：n26-current-candidate-seeded-forest-v4/VERIFIED.json。
- 实际发布重放：n26-current-candidate-seeded-forest-published-replay-v4.json。
- 种子保留：n26-current-candidate-seeded-forest-v4/SEED-RETENTION.json。
- 严格叶账本：n26-current-candidate-seeded-forest-v4/LOWER-LEDGER.json。
- 两个 OPEN 叶：n26-current-candidate-seeded-forest-v4/PENDING-FOREST-LEAVES.json。
- 完整保留根：n26-current-candidate-seeded-forest-v4/PENDING-ANGLES.json。
- 完整当前衔接：n26-current-candidate-seeded-current-audit-v4.json。
- 独立最终复核：n26-current-candidate-seeded-final-digest-recheck-v4.json。

剩余整根、完备四族枚举、任意覆盖必要归约和最终全局联合接受仍未完成。
全局下界、最优性和 n=26 完成标记保持为否。
