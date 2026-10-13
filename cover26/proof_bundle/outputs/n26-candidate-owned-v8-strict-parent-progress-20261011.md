# n=26：候选第八版接入重建后的合格父链

2026-10-11 14:20，Asia/Shanghai。本记录写于新的候选当前接入之前。

候选第八版独立验收和实际发布重放均通过，字节 SHA256 一致：

`be3e9e69de30bfa29af94b86764d8f8004752a89d78b000c60f6c079860072c2`

它从已完整复核的候选第七版实际来源延续根 41、45、48，并首次尝试仍未决的根 959。四根共 870 个 SPLIT、19 个 ENERGY、855 个 OPEN；新增四个精确闭叶，没有新整根下界支付，没有新严格空根，仍保留 25 个未结候选整根。855 是本次四根森林的 OPEN 叶数，不替代 25 个原始整根的计数。

原先对旧第十九阶段兼容父链的候选接入已停止，没有生成可采用的当前接受件；输入和旧记录均保留。候选第八版自身的证明时父链没有使用该兼容报告，独立验收和重放仍然有效，不需要重做或改写。

新接入采用完整重建的第十九阶段严格当前父链：

- 审计 `n26-nineteenth-conditional-current-audit-v19-sparse-v2-strict-with-scope.json`，摘要 `83eba3ab63841a5f48f5ffc75df1fee4d7dccd921c042c33a4b4a48d2fec0ecc`。
- 独立复核 `n26-nineteenth-conditional-final-digest-recheck-v19-sparse-v2-strict.json`，摘要 `ba0db24c372b8096df7a7faeeb4cb9cf5a677218e5926211476a12607945bfb9`，全部 186,300 项通过。
- 正式条件前沿 8,193，四族 316 / 1,040 / 3,249 / 3,588。

新的来源身份检查从此父链经第十八阶段追溯到实际候选第七版，并通过十项拒绝测试。相同根数不能代替实际来源身份；所有已接受非 OPEN 节点、闭半边、旧支付、1794 的 LOCAL 下界和等号可行区域都必须保留。

本次接入只增加四个已证明叶及其历史所有权，不删除枚举前沿子树。新的当前接入及独立最终复核都通过后，才可把候选第八版当作下一轮发现的实际来源；届时根数仍为 25。

文件：

- [第八版独立验收](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-current-candidate-owned-forest-v8/VERIFIED.json)
- [第八版实际重放](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-current-candidate-owned-forest-published-replay-v8.json)
- [严格父链身份检查](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-candidate-latest-layer-identity-regression-v7-strict-parent.json)
- [重建后的第十九阶段当前链](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-nineteenth-conditional-current-audit-v19-sparse-v2-strict-with-scope.json)

全局目录、任意覆盖必要归约的最终联合接受、全局下界及最优性仍未闭合，n=26 不标为完成，n=27 不提前启动。
