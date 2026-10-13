# n=26 初始推进记录（2026-10-08）

当前选择：在 n=23、24、25 全局源证明验收完成后，优先推进 n=26；n=11 形式化保持暂停，不启动子代理。

## 已核实前提

- n=23：`n23-global-final1/ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json`
  - `verified=true`
  - `global_source_proof_closed=true`
  - `global_optimality_proved=true`
  - SHA256 `6da6c5e1c80ade821bb033ce3b3b547c9ff5fb4a71cac16a531442a867e5da12`
- n=24：`n24-global-final1/ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json`
  - `verified=true`
  - `global_source_proof_closed=true`
  - `global_optimality_proved=true`
  - SHA256 `5bb55c9858a4dc1245249b12fd45cab3c5ed132a238eb6f7e70ddd6f2d0bb777`
- n=25：`n25-global-final5/ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json`
  - `verified=true`
  - `global_source_proof_closed=true`
  - `global_optimality_proved=true`
  - 独立当前内容复核 `555483` 项，差异 `0`
  - 接受子进程实际退出码 `0`
  - `binding_creator_terminal_observed=false`，但绑定报告已由独立全量审计重新核验；此限定已写入接受件
  - SHA256 `30389bfa3132d08954281e743db670fbb3874785e0d90c9876d4f5ddeec31dd1`

## n=26 当前状态

恢复工作区中没有 n=26 的既有证明目录、正式接受件或已运行的 n=26 生产任务。现阶段只建立独立工作区和输入审计，不把 n=25 的数值、角树或全局最优性自动外推到 n=26。

已完成的第一项可验证推进：把 n=25 的精确 Q(√2) 几何构造复制为第 26 个重复圆心，生成
`n26-upper-duplicate-n25-v1/VERIFIED.json`。它严格给出
`r_D(26) ≤ r_D(25) = 1/(√6+√3)` 的上界区间；报告明确保留
`global_optimality_proved=false`，所以这不是 n=26 完成件。

同时把完整剥离内核扩展到 `MAXN=26` 并在 WSL 中编译成功。B=14、15、16、17、18
的 `100000` 节点限额探索均按设计拒绝写出完整目录（`REJECTED NODE LIMIT:
incomplete search`）；这只验证了 n=26 内核的参数边界和 fail-closed 行为，
不计作 n=26 证明或完备枚举。

另做了一个 7 参数数值候选探测。粗采样曾得到约 `0.23590`，但独立
100,000 个边界点加 400 个半径层、每层 1,800 个角点的复核给出
`0.2398727`；局部精修后的复核仍给出 `0.2402294`。因此没有把这个
候选当作 n=26 上界，当前唯一可靠的 n=26 上界仍是重复 n=25 圆心的构造。

首要义务：

1. 从 n=26 自己的精确候选上界开始，确定 `R_26`、有理严格上界和二次域/代数域表示。
2. 独立证明任意严格小覆盖到必要边界族 `(B,I)` 的归约，重新建立完整外露面剥离入口。
3. 为每个必要族生成完整目录、严格源库、下界账本和独立当前内容绑定。
4. 只有四项都闭合且全局接受件通过后，才能宣布 n=26 完成。

已完成的 n=23/24/25 证据归档副本位于 F:；原恢复工作区保留，作为接受件绝对路径和哈希引用的权威源。
