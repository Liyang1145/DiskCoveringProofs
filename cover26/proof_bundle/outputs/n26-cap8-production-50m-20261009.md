# n=26 B18 cap8 50M 生产尝试（2026-10-09）

修正后的 n=26 cap8 内核以

`N=26, B=18, scale=10^7, caps=(768677,1587443,2546859,4058615)`

和 `dfs` 模式运行，节点限额为 `50,000,000`。

运行到 `49,000,000` 节点时：

- `survivors=18,126`；
- 进程随后按节点限额退出：
  `REJECTED NODE LIMIT: incomplete search, no complete certificate`；
- 没有写出 `B18.json`。

这次长运行确认 cap8 剪枝虽然有效，但 B18 仍远未达到完整目录。
它不能计作 B18 下界证明，也不能推进 n=26 全局接受。

## 当前内容绑定

- cap8 源文件 SHA-256：
  `61661a090b036ef14729965bf46042af32f39fc4a0d04fb8dc83d59fa9de2d8b`
- Linux 二进制 SHA-256：
  `d9f7f63dc2ce6f8995498c9e610210c313a73723ed363f13b2ede6c950f74fc2`
- 常数件 SHA-256：
  `9ef64a74a6ee55064709d91cf758c512453ca5fd7e70c3cc014c17a1f45a8bae`

状态仍为 `pending`；下一步需要搜索状态压缩、分支分块或新的严格几何付款，
不能只继续增加节点限额。
