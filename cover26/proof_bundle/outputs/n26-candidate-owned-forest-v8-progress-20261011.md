# n=26：候选第八版森林延续

2026-10-11，Asia/Shanghai。此项是同根 Rstar 下的候选森林延续，不是全局最优性结论。

第八版从已绑定的候选第七版实际来源继续处理 25 个未结整根中的 41、45、48、959 四根。独立验收和实际发布重放均使用同一封存源、同一父链、同一 92 杆/52 坐标框架及 7/800000 局部容差。

新增森林统计：

- SPLIT 870
- ENERGY 19
- LOCAL 0
- EMPTY 0
- OPEN 855
- 新增精确闭叶 4
- 新整根严格下界支付 0
- 未结整根 25
- 未结闭角盒 25

所有历史非 OPEN 节点、共享边界、旧支付、未尝试整根和 LOCAL 可行性控制均保留。4 个新闭叶是能量下界叶，不是整根支付；因此本版不减少候选整根数量，也不声称全局下界已闭合。

候选第八版验收报告和独立实际发布重放均通过后，才允许将其绑定到第十九阶段完整当前链，并重新计算全量摘要。未完成新的当前接入和最终复核前，本版本保持 exploratory/pending。

核心文件：

- [第八版验收](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-current-candidate-owned-forest-v8/VERIFIED.json)
- [第八版实际重放](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-current-candidate-owned-forest-published-replay-v8.json)
- [第八版来源提案](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/n26-current-candidate-owned-forest-discovery-v8.json)

全局目录、任意覆盖必要归约、全局下界、最优性和 n=27 仍未完成。
