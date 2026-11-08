# 2026-11-08 证明资产整合

PR [#4](https://github.com/Liyang1145/DiskCoveringProofs/pull/4) 的全部 35 个变更文件已合入，
源提交固定为 `00b05471dba021a9db34957364a5df0f8b212b8d`，合并提交为
`d2fc6bb9d4dcfc19f81845167f12076fdb91f1c2`。外来证明、源码、原始复算记录和
大证书分片保留原字节，原各阶权威源和限定保留。

| 阶数 | 当前资产与入口 | 本次维护者核验范围 |
|---|---|---|
| 11 | [同版执行器与输入](../external-submissions/2026-11-08-offline-proofs/n11/)补齐了[原文稿](../external-submissions/2026-11-08-sol-review/original/证明.md) | 根与构型、有限不等式、普通链与下界链、两份输入再生成、局部正定性和近构型证书通过。提交者的完整远域双扇通过记录保留；本次未重新计算完整远域。 |
| 12 | [新独立证明与证书](../external-submissions/2026-11-08-offline-proofs/n12/) | 构型与有限界、外来十外围盘完整重放通过：539 测度盒、80 剪枝盒、6395771 外围盒。九外围盘证书 515029 叶的哈希和完整二叉划分通过；全部叶算术未重新计算，提交者内存中断记录保留。 |
| 14 | [原始证明包及审查](../external-submissions/2026-11-08-sol-review/REVIEW.md) | 本次提交引用同字节版本；沿用此前完整 624 个代表及五项拒绝控制的维护者复验。新提交日志单独保留。 |
| 25 | [既有全局源证明入口](../cover25/README.md)与[最终接受件](../cover25/verification/final-acceptance/ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json) | 已接受源归档结论为 r_D(25)=1/(sqrt(6)+sqrt(3))。本次保留权威哈希与原终止句柄限定，未新做全量数学重放。 |

维护者实际输出、命令、工具链和范围见
[SCOPED-REPLAY.json](../external-submissions/2026-11-08-offline-proofs/maintainer/SCOPED-REPLAY.json)，
输入完整性及叶划分见
[INPUTS-VERIFIED.json](../external-submissions/2026-11-08-offline-proofs/maintainer/INPUTS-VERIFIED.json)。
核验在独立构建副本中进行，未覆盖提交者源码或原始日志。两份再生成输入按完整
数值 token 比较，未用平台换行差异改变原证据。MinGW 编译使用任务内 ASCII 临时
目录，断言启用并使用 `-ftrapv`。

外来路线与原证明的精确根等价性、书面任意覆盖归约仍需分别审阅。字节完整性、
有限数学复算和完整全局证明是不同范围；本次没有将其合并为新的全局数学接受。
n=26 原生 16 / 4957 / 344 未决状态保留，持续研究仍暂停。

此前“n=11 缺同版执行器”的初次审查记录作为历史保留；现在源码已经补齐，最新
状态以本页及项目状态索引为准。复算命令见[提交者入口](../external-submissions/2026-11-08-offline-proofs/README.md)。
