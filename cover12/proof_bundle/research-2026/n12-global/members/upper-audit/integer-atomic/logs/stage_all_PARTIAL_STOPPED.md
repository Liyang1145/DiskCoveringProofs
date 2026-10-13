# stage_all_PARTIAL_STOPPED — 说明（避免误读为完整 manifest 重放）

2026-09-26，按 lead 指示**主动停止**（非失败、非超时）。

* 文件：`logs/stage_all_PARTIAL_STOPPED.txt`（17 KB / 120 行 + 2 行表头）
* 运行者：`py -3 -B py/integer_kernel.py stage <stage2200> all`
* 使用的核 hash：**`0115C3F3660382CC…`（冻结版，与 REPORT.md 记录一致）**；输入 stage2200 sha256 前缀 `fd7e2ac05e346bac`
* 完成度：**部分**（120 行样本，非 1021 叶全覆盖）
* 读数：样本内**全部 certified**（0 行 status≠certified），每行标定 `cal(fn=0,ov=0,bad=0)`
* 状态：**不得**引用为"stage2200 全叶整数核重放完成"；该义务由 **finite-reduction** 的全 manifest 复核器承担
  （同一 int 核 + 同一输入由不同成员重复跑**不是**独立数学证据，故本成员不再重跑）。

停止原因（lead 指令）：避免重复同核同输入、避免与主 run3 抢 CPU。核源码与 guards 保持**冻结**，等 finite-reduction 完整 run。