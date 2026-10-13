# 冻结输入与联合接受路径复核

本次发现两个证据管理问题，并保持旧文件、旧报告和原manifest不变。
它们是接受链问题，不能通过倒改旧“verified”记录来解决。

## 1. B13冻结检查器曾被后续修改

`N22-B13-CATALOGUE-SNAPSHOT-resume1.json` 绑定
`audit_streamed_hierarchy.py` 的原哈希
`a5e0aab2ba0822beb2af0df2143d5aa53df6ced376d591a3cf8b42ed02426ab3`。

后续为接受合并账本新增了允许缺少重放的分支，导致该路径对应
另一哈希。现在把变体保存为 `audit_streamed_hierarchy_legacy_unpaid.py`，
并将原文件严格恢复到上述已绑定字节内容；没有修改manifest。

`audit_snapshot_files.py` 对完整B13快照的49975个文件重查：
`evidence/n22-B13-snapshot-integrity-resume2.json`，全部通过、零差异。
这只是完整性审计；B13数学闭合仍由原源证明、精确重放和映射证明支付。

## 2. 合并账本不能跳过数学重放

旧变体允许 `--stage GROUPS RECEIPT -` 时计入RECEIPT声称排除的
成员；虽然此前有分批数学重放报告，但该映射审计并未绑定这些
报告，而且字段名仍写“with_replayed_certificates”。故这个路径
不能单独作为最终接受证据。

本轮采用更直接的修复，而不扩大冻结接受器作用域：

1. 对最终B14合并账本逐份、全量执行原 `replay_group_stage.py`；
2. 用恢复的原 `audit_streamed_hierarchy.py` 接受非空联合重放报告；
3. 对达到型的显式映射及4421节点角树又作独立重放；
4. 强化 `close_n22_b14_catalogue.py`，要求上述报告全部内容绑定，
   以及根、同根全盘上界、局部隔离和三次半径关联。

新链现已完成，接受报告是
`evidence/N22-B14-CATALOGUE-CLOSURE-strict-resume2.json`；
旧B14简易闭合报告仍只保留为历史记录。
旧映射审计仍说明映射检查确实曾执行，但不能证明其未绑定的
数学接受链自动完成。B15同样必须使用非空完整联合重放记录。

## 3. 批次计数不是无条件定理

新 `audit_b15_batch_inventory.py` 从原根未决集合出发，严格
检查每个批次的唯一成员、证书字节、重放报告与源哈希。
它不依赖路由链名字或批处理的打印计数。
该检查并不代替重新计算力证书，也不代替全目录的面/锚点
嵌入审计；其报告明确列出两项未在此执行的义务。

所有新报告另存，不倒改旧快照。不声称任何新阶全局证明已经
因此自动完成。n21快照另在作全量字节完整性复核。
