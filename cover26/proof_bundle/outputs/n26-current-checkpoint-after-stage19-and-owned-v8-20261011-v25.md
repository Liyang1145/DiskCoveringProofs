# n=26：第十九阶段完成，候选第八版待实际重放

2026-10-11，Asia/Shanghai。目标继续进行：n=26 尚未完成全局最优性闭合，n=27 尚未启动。

第十九阶段已完成原生实现一致性、精确条件重放、终端目录、完整当前链审计和独立最终摘要复核。正式条件前沿由 8,082 推进到 **8,193**。

第十九阶段事件为：展开 3,437；直接力排除 10；角度树排除 15；面积排除 273；组合空分支 1,063；完整终端 2。严格整树排除合计 298，角度树节点 53。逐族守恒均成立：

`8,082 + 4,909 − 3,437 − 298 − 1,063 = 8,193`。

第十九阶段完整当前审计 SHA256：

`9d0f7f7dc318a5db1155c8db2e0cba7ccd5e7a8a43ecc2fcb3b97fe41e7992e7`

独立最终复核重新计算 **186,283** 项摘要，SHA256：

`4395769907a87fb4e7ade1250bb64aef2195768ea141362b4e3b735920f1c2ef`

当前链继续保留 25 个未结候选整根、25 个未结候选角度盒、1794 整根下界、39 个新增精确叶、87 个历史闭合类型和 215 份证明回执。全局目录、任意覆盖必要归约、全局下界和最优性仍未闭合。

候选第八版已完成独立森林验收，但没有新增整根下界支付：4 个根（41、45、48、959）共 870 个 SPLIT、19 个 ENERGY、4 个新增精确叶，855 个 OPEN；未结整根仍为 25，未结角度盒仍为 25。其验收为 `verified=true`，但实际发布重放正在进行；在实际重放及新的当前接入/独立复核完成前，不改变正式候选账本。

记录：

- [第十九阶段当前审计](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-nineteenth-conditional-current-audit-v19-native-v4-with-scope.json)
- [第十九阶段独立复核](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-nineteenth-conditional-final-digest-recheck-v19-native-v4.json)
- [候选第八版验收](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-current-candidate-owned-forest-v8/VERIFIED.json)
- [候选来源身份回归](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-candidate-latest-layer-identity-regression-v6.json)

同根 Rstar 范围、原始 U 前沿 3,922、92 条杆约束、52 坐标框架和局部容差 7/800000 不变。等号可行的 LOCAL 区域未被宣称为空集。
