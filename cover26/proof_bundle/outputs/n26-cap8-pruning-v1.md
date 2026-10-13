# n=26 cap8 剪枝实验（2026-10-09）

为处理 `B=18,I=8` 的最小内部预算族，在独立 n=26 剥离内核中加入了
严格三跳闭包和第八杆角帽 `4058615`。三跳闭包已修正为从两跳集合再扩
一跳，避免把四跳关系误当成三跳。

## 运行结果

- 原始三帽内核，B=18，10,000,000 节点：
  - `REJECTED NODE LIMIT: incomplete search`
  - 约 313,561 个 survivors（在 9,000,000 节点时）
- 修正后的 cap8 内核，B=18，10,000,000 节点：
  - `REJECTED NODE LIMIT: incomplete search`
  - 约 2,714 个 survivors（在 9,000,000 节点时）
  - 未写出完整目录
- 修正后的 cap8 内核，B=14，10,000,000 节点：
  - `REJECTED NODE LIMIT: incomplete search`
  - 约 349,666 个 survivors（在 9,000,000 节点时）
  - 未写出完整目录
- `audit` 访问顺序在约 3,000,000 节点、180 秒时仍未闭合，已终止；
  未把它当作结果。

cap8 明显减少了前沿 survivors，但尚未达到零未决叶，因此不能作为
B=18 完整枚举或 n=26 下界证明。

## 绑定状态

第八杆角帽的严格正弦余量已写入：

`n26-boundary-constants-v2/CONSTANTS.json`

该文件仍明确标记 `global_optimality_proved=false`。当前 n=26 仍需
完成五个必要族的完整目录和付款账本。
