# n=26 九根混合曲率补充覆盖：验收与当前接入流程

2026-10-11，Asia/Shanghai。本记录是新增证明接口的接入说明，
不是已经完成的几何接纳或完整当前接入。正式未结候选整根数不由本记录修改。

完整待验收覆盖包括：

- 整段凸包模式：37、41、45、48、44、40，共 48 个严格能量分块。
- Taylor 线段积分模式：33、36、32，共 37 个严格能量分块。

九个中心盒均使用原始 52 坐标 LOCAL 余量 7/800000，
其中等号可行区域保留，不能宣称严格空集。九根覆盖不替换旧已验收森林、
不重置非 OPEN 节点；重叠补充分块也不计为旧森林中的新唯一叶。
剩余根必须保留第 959 根最新部分森林和全部更早证明链。

新 [统一验收器](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/verify_current_candidate_mixed_curvature_covers.py)
支持两种明确模式，绑定自身执行代码。它完整执行原有 owned 来源门控，
重放真实最新模型、全部旧支付和最新每根森林，再重新计算九根覆盖。
整段模式、积分模式和交叉模式的全部 29 项实际拒绝控制均需运行。
所有九项可行微小候选正控制也必须重新执行。

新验收器不会将数值谱、诊断上下文或仅摘要身份检查当作完整模型来源重放。
固定算术资源仅作为先前诊断和单元算术数据，不被正式验收器读取。

[统一接口保护及算术控制](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-mixed-curvature-cover-own-executor-guard-controls-v1.json)
已经实际运行并通过：

- 29 项算术拒绝控制，包含两种曲率的完整原控制和模式混淆、跨模式重复根。
- 12 项元数据拒绝控制。
- 85 个严格能量分块、九个原始 LOCAL 中心盒的算术重建。
- 九项可行微小候选正控制。
- 新纯积分后端与保留的独立算术测试器结果一致。
- 第 959 根最新部分森林数据原样保留。

这份测试未执行完整最新模型/来源门控，故仍为 `verified=false`、
新增几何支付零、正式整根移除零。测试中的 16 个剩余根是算术账本，
不是正式当前根数。

新 [显式候选身份检查](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/n26_candidate_identity_with_mixed_curvature.py)
及 [回归报告](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-candidate-mixed-curvature-layer-identity-regression-v1.json)
通过 16 项拒绝测试，拒绝新格式冒充旧 owned 来源、遗漏执行器或模式控制、
丢失历史和使用根数相同但过时的来源。旧身份模块没有被修改。

新 [独立最终复核工具](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/recheck_mixed_curvature_candidate_current.py)
及 [账本回归](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/outputs/n26-mixed-curvature-final-accounting-regression-v1.json)
通过 12 项拒绝测试，包括遗漏整根、重复支付、LOCAL 等号区域被错称空集、
遗漏或重置第 959 根历史。此回归也是零支付测试，不替代正式最终复核。

后续实际流程：

1. 候选 owned-v8 的严格父链当前审计和独立最终复核都完成。
2. 用这对完成件、owned-v8 真实验收/重放和两种诊断证书，封存全新混合覆盖包。
3. 真正执行新封存验收器完整主程序：完整来源门控、九根覆盖、29 项控制、
   所有正控制及全部依赖绑定。成功后才执行同一封存主程序的真实发布重放。
4. 以届时最新完成的正式当前链为父链，运行
   [完整当前接入器](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/audit_mixed_curvature_candidate_current.py)；
   它作为独立子进程再次执行整个封存覆盖验收器，不只抽取重放函数。
   保留全球运输前沿、87 个历史类型、215 份回执及所有旧候选证明。
5. 运行独立最终摘要/账本复核。两步均通过才正式采用新的剩余根。

新 [完整来源适配器](C:/Users/Administrator/Documents/Codex/2026-10-09/n-26/work/n26_current_mixed_curvature_candidate_source.py)
识别新模式接入格式，实际再次完整重放原模型、旧支付、新覆盖和剩余历史。
它不修改旧 owned 格式分派器，不将新报告伪装为旧森林验收。

该流程尚待实际几何执行和完整接入。n=26 全局完备目录、任意覆盖归约最终
联合接纳、全局下界和最优性都仍未证明，n=27 未启动。
