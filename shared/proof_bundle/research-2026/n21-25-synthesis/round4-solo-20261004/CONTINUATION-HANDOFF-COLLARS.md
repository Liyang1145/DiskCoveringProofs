# 单独接力：新增证明与真实运行句柄

运行时目标仍 active，最新人类要求是“继续”。禁止子代理。
优先级仍 n25 → n23/n24；三阶无条件全局结论均未完成。
n11 没有启动、编译或修改。不得因本交接文档而暂停或重启活任务。
文件名中的 20261005 延续工作区上海时区的运行目录标识。

## 活句柄：观察原作业，不重复启动

以下 native PID 已通过实际 ps 的命令、参数和运行状态核对：

| 会话 | Linux PID | 当前动作 | 输出/控制目录 |
|---|---:|---|---|
|96878|35578|原12障碍 n25/B14 完整搜索|n25-B14-sparse-collar-search-resume-20261005-v1|
|5476|36899|合并25障碍 n25/B14 完整搜索|n25-B14-union-sparse-collar-search-20261005-v1|
|2693|38328|无障碍 n25/B17 完整搜索|n25-B17-full-collar-search-20261005-v1|
|48071|控制阶段 PID39409，待观察变化|B15 强守卫控制，成功后同一会话自动启动生产|n25-B15-new-sparse-collar-controls-20261005-v1；随后 n25-B15-sparse-collar-search-20261005-v1|
|79193|控制阶段 PID39520，待观察变化|B16 强守卫控制，成功后同一会话自动启动生产|n25-B16-new-sparse-collar-controls-20261005-v1；随后 n25-B16-sparse-collar-search-20261005-v1|

控制阶段 PID 可能已经自然结束并变成其他小例/生产 PID，必须用
write_stdin 和新日志/ps 重新定位；不能把观察超时当退出。
两个控制会话的最后核查分别在完整 N23/B15、N22/B16 baseline，
实际 ps 显示运行、CPU接近100%，不是只有状态文件。
原 B14 最后观察约285百万calls/172092弱图；加强 B14
约143百万calls/103948弱图；B17约179百万calls/3364弱图。
都没有观察到耗尽相位，计数不能当完整类型数或完成率。

生产源码、二进制、原库和原控制五个 SHA 仍全部相符：
12F08344…；A3045DDF…；E59AFBE4…；C0ED3C2B…；B9E280D1…。
实际生产启动前绑定的任何文件都不能热编辑。

## 两项已经真实失败的无守卫搜索

- 会话72810、native38322：B15在2百万弱图内存保护时真实exit1，
  输出 n25-B15-full-collar-search-20261005-v1/NATIVE-TERMINAL.json。
- 会话37918、native38325：B16同样真实exit1，
  输出 n25-B16-full-collar-search-20261005-v1/NATIVE-TERMINAL.json。

均已收取会话结果，没有完整目录、GROUPS或数学完成。
旧内存弱图没有落盘，不能把日志中的1971265等数当证据集合。
新 B15/B16 使用已重新接受的障碍，不是重跑同一个失败作业。

## 新接受成果与严格范围

1. 有界 B14 discovery 的8674个弱图全部严格排除，独立标准库
   重放 pending0。证据 n25-B14-collar-discovery-8674-fresh-exact.json。
   这是发现集，不是完整必要族。
2. 其中首32图的847个面，逐次重证删除后降至142面，归并13个
   新严格障碍。独立重放/导出后，与旧12障碍合并成25障碍库。
   新13图对8674发现图有8490个逐中心/锚杆/面复核的实际注入。
   合并库通过3939映射、105另序存在性对照、8拒绝，
   及10完整小族分割+3失败拒绝后上线 B14。
3. n22的7153个B15旧图不能原树搬到新根：新角约束闭包已负。
   独立角证书 n25-B15-old-pattern-short-path-cycles-20261005-v1.json，
   全7153逐条路径/方向/整数环和重放排除，7伪造拒绝。
   不是7153个完整n25类型。旧 retarget_n22_obstacles 输出0接受、
   7153未直接搬运；不能把其空 GROUPS 的pending0当族闭合。
4. B15有界25百万节点发现33292图；首128全部严格证书+独立重放。
   每次删面重新证明，归并9个严格障碍：
   n25-B15-new-sparse-library-20261005-v1/LIBRARY.json。
5. B16有界2百万节点发现3372图；首64全部严格证书+独立重放。
   归并2个严格障碍：
   n25-B16-new-sparse-library-20261005-v1/LIBRARY.json。
6. 泛化工具导出器 console 仍有旧“B14”文本标签；接受前提是
   JSON的实际B以及 exact.verify(B,...)，上述新库实际分别B15、
   B16。不要依据该 console 标签把它们误记成B14。

## 一个 B16 完整补全族已经闭合

达到构型的外露面只用24个中心，24个面；省略8个纯内部面，
缺一个内部中心，内孔为8边形。弱图不自动包含端点核心。

complete_simple_collar.py 对简单内孔补全，pinched/nonmanifold
明确 UNHANDLED，不排除它们。8个完整冻结小例的全部被处理
fibers与旧全图目录精确相等，另有3拒绝控制。未处理485个小例
collars明确记录，不把它们算排除。源归纳见
SIMPLE-COLLAR-COMPLETION-SOURCE.md。

候选 collar 补全共有91个完整同构型，原接受器独立重放90个
严格排除，唯一待付id90=known attaining。其端点20面核心到
id90的完整中心/循环锚杆/面单射已支付，fresh311883节点整树
报告与当前输入、树、42文件快照全部相符。

最终 n25-B16-single-candidate-collar-closure-20261005-v1.json：
90 strict + 1 exact-r* core，pending0。
只闭合这一个 outer collar 的全部91个简单内孔补全；
绝非整个B16，更非n25全局最优性。映射orientation=1,shift=0。

## 新工具与下一步

- 通用源归约：N25-COLLAR-COVER-INTERFACE.md。
- 发现快照 collar_discovery-linux/schema incomplete-collar-discovery-v1：
  有界预算退出后明确标为 incomplete，不能替代生产目录。
- generic discovery/probe/replay/sparsify/export 工具由
  derive_family_discovery_tools.py 生成，原工具不改。
- family_sparse_gate.py 对新的B15/B16图重新精确接受全部树；
  run_family_sparse_collar.py 仅B15，run_b16_sparse_collar.py 仅B16。
- test_generic_sparse_collar.py 的最后N23控制仍需真实结束；
  test_b16_sparse_collar.py 的N22/N23控制同理。同一工具会话已经
 排好“控制成功才启动生产”，不要旁路重复启动。

下一轮先观察五个活句柄和控制相位。生产成功后检查真实exit、
全部INPUT-BINDINGS和canonical完整目录，再使用旧 probe_groups/
replay_group_stage 支付残余。非零/保护停止不得计完成。
可继续为B17发现严格小图以减少无守卫搜索，但不要重启其活作业。
若出现可实现的弱图，补其内部族；简单内孔可用新枚举器，其他
明确未处理拓扑需另外路线。全部4族和任意覆盖最终合成未完成。

用户面对的简报在 Documents/Codex 当前聊天 outputs/证明推进记录.md。
主要证据保持本原数学目录，不修改历史状态账本或n11。
