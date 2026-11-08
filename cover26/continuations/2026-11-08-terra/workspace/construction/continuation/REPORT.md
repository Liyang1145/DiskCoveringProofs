# n26 延续审查：本地多提交及 134 杆核心

## 树与对象

`recover_all.py` 在 `GIT_NO_LAZY_FETCH=1` 下只读本地 Git 对象数据库，枚举所有八个本地 commit：047e41a、1790e4a、1d7f3eb、2c43bd4、55b57a2、57f7f6f、6869e8a、91f0ed5。每个 commit 的 `cover26` 树可列出 4746 条路径，但树项存在不代表其 blob 已在缓存。按 Git blob ID 去重后，只有 18 个被这些树引用的 blob 可读；逐一记录 commit、路径、Git blob ID、SHA-256 和精确字节长度于 `all-commits-inventory.json`，原始内容保存在 `recovered/`。所有对象先 `git cat-file -s` 成功并核对字节长度，再写输出；不把缺失对象写成空文件。

`scan_blobs.py` 对所有本地可读 blob（包括没有 `cover26` 路径的对象）计算 SHA-256，结果见 `blob-content-scan.json`。没有对象与原始同根 SYSTEM SHA-256 `e555cb470ef4a3a8c5167f95307e7b0220c8b77a0fe7b435010220450eb44ef7` 或 ROOT-CERTIFICATE SHA-256 `598d65cbc3d839780e3f6b8dbdc3cd36331a391f716eacc1cae83144903b2794` 匹配。候选数值区间出现在 README 和 midarc 独立 final 等记录中，但数值区间不是候选坐标或一套可认证的代数系统。

## 134 杆重建依赖与阻碍

可读的 `n26_current_physical_reuse_source.py` 不是核心模型生成器：它通过缺失的 `n26_latest878_physical_donor_source` 和 `test_checked_root28_full134rod_intersections` 重构实际 root25 原始域，并要求种子中的 `full134rod_supports` 与早期 v4 及 donor 逐项一致。`n26_latest_root25_origin_source.py` 继续依赖缺失的 `probe_root25_v4_balanced_whole_leaf_energy`、种子 `n26-root25-balanced-whole-leaf-successor-v2.json` 和其对应的 independent-controls。`n26_current_origin_append_context_v3.py` 和 `admit_current_missing_origin_refit_parameters_v1.py` 只是检查/增补已有支持证书，并通过进一步缺失的 `n26_origin_branch_correlated_energy`、pilot 和原输入执行验证，不含自足的原始中心坐标与 134 条杆的构造表。

当前可读的 247001 字节 root25 independent-controls 是带原始路径和 SHA 的复核摘要：自身 `verified=false`，并明确 `new_geometric_payments=0`、`global_lower_bound_proved=false`、`global_optimality_proved=false`。它有 1170 个 direct-input 引用，但内容为路径/哈希，不能从哈希重建模型、候选坐标、杆权或区间隔离证明。

本次没有找到能够自足重建候选根、同根覆盖或 134 杆模型的数据，因此不能对原候选宣称已进行精确重放，也不能凭目前文件继续支付几何分支。下一步需恢复上述原 SYSTEM、ROOT-CERTIFICATE、种子和依赖脚本的准确字节；以原始 SHA 校验后，再检查模型定义、变量排列、杆列表、根隔离与同根全覆盖，并将算术域结果和形式几何支付严格区分。完整可执行复核还需解析所有递归输入，不只上述直接引用。
