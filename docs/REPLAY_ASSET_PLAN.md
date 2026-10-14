<!-- SPDX-License-Identifier: MIT -->
# 23–26 的复现缺件审计与补齐方案

2026-10-14 的审计确认：公开仓库没有包含这些阶数的完整冻结依赖。
`restore_large_files.py` 只能还原**已提交**的分片，不能恢复未交付文件。
本页区分数据是否齐全、旧路径能否运行，以及数学义务是否完成。

## 23–25：数据已经迁回本机，公开交付仍缺大部分内容

对原迁回 SQLite 库与 commit
`6869e8ad9a92693e88b891e74ec3e10f703b4146` 的交付清单按原始 SHA256 对照：

| 冻结范围 | 文件数 | 原始字节数 | 公开有相同内容的文件数 | 没有相同公开内容的文件数 |
|---|---:|---:|---:|---:|
| n23 最终冻结角色 | 233,801 | 33,238,593,121 | 191 | 233,610 |
| n24 最终冻结角色 | 230,568 | 2,447,857,236 | 1,731 | 228,837 |
| n25 最终冻结角色 | 555,483 | 29,555,228,713 | 406 | 555,077 |
| 完整迁回并集，含共享文件和迁回元数据 | 1,020,085 | 66,482,183,809 | 2,563 | 1,017,522 |

不同角色会共享文件；各行不能直接相加。相同字节在其他公开路径也算已交付内容，
但还需要显式路径映射。并集未公开的原始字节共 **65,136,631,995**。
这是清单对照，没有在本次审计重新读取全部百万文件，更没有重新证明全局定理。
10 月 8 日保留的全量字节审计记录报告零缺件、零差异；它与本次审计分别标记。
完整机器报告见 [n23–25 审计](../verification/reproducibility/n23-n25-public-content-audit-20261014.json)。

## 已补齐的小型核心数据包

[核心输入 Release](https://github.com/Liyang1145/DiskCoveringProofs/releases/tag/proof-assets-core-20261014)
提供 **55 个文件、61,130,881 原始字节**，包括此前未公开的 **15 个承重输入**。
其中有 n23/n24 的 `core-system.json`、`core-root.json`、候选构型及角度树，
以及 n25 的端点角度树。包中的源代码与证书保留原字节、原来源和原权利范围。

用 Python 3.10+ 下载并按 Git 中固定的索引核对、还原：

```sh
python tools/restore_frozen_assets.py --package-index assets/replay/n23-n25-core/PACKAGES.json --from-url https://github.com/Liyang1145/DiskCoveringProofs/releases/download/proof-assets-core-20261014 --destination build/core-assets
```

也可用 `make restore-core-n23-n25`。下载缓存默认在 `build/frozen-downloads`，
文件还原到 `build/core-assets/assets/<canonical>`。重复运行会核对已有相同文件；
不同内容、缺包、错误哈希、越界 ZIP 路径或重复成员都会失败。
离线使用 `--package-dir <已下载的包目录>` 替代 `--from-url`。

这里的通过标记是**字节还原**。这些原程序支持的核心数学范围为：

| 阶数 | 输入对应的数学步骤 | 保留的局限 |
|---|---|---|
| 23 | 同根隔离、达到构型、局部矩阵与 30,653 节点角树 | 限定的 nonstrict core；完整竞争构型目录另需全量数据 |
| 24 | 同根隔离、达到构型、局部矩阵与 69,215 节点角树 | 同上；旧入口还核对来源整 ZIP |
| 25 | 精确二次域构型、应力纤维、端点局部矩阵与 311,883 节点角树 | 旧角树入口读取历史局部接受件；不能单独称为新鲜全链重放 |

新的一键数学调度入口尚未实现。旧 n23/n24 入口含冻结绝对路径检查；
n25 需要把重新计算的局部结果送入角树检查。核心包让这些数学输入可下载，
不宣称下载之后就完成了全局数学复现。
[PROFILE.json](../assets/replay/n23-n25-core/PROFILE.json) 给出准确文件、哈希、源入口和范围。

## 26：服务器上按冻结清单导出

[n26 审计](../verification/reproducibility/n26-public-content-audit-20261014.json)
已逐项核对算术 controls 的全部 **1,170** 个直接输入：
**132** 项同路径同字节、**3** 项相同字节在别处、**1,035** 项没有交付字节
（1,031 个独立 SHA256）。缺件包括原始系统/根证书、前驱 composition、
joint-refit pilot 和多批 donor/checkpoint。不能用小型 `VERIFIED.json` 代替。

正式 current/final 记录绑定 273,731 个文件。本次没有取得完整 current 正文，
所以**没有完整正式层逐项缺件统计**；报告中的 13 个 midarc 路径只是待确认候选。
现有 n21–25 迁回记录不包含 n26 的完整资产。

在存有冻结 n26 数据的服务器上，先取得仓库的新工具和清单。设 `<n26-root>`
为实际含 `work/`、`outputs/` 的根目录。以下种子清单包含 1,170 个输入引用，
再加 authoritative arithmetic current/controls 自身（重复文件按规范路径合并）：

```sh
python tools/export_frozen_assets.py --ledger verification/reproducibility/n26-arithmetic-export-inputs.jsonl.gz --asset-root "<n26-root>" --audit-only --output "<new-preflight-directory>"
python tools/export_frozen_assets.py --ledger verification/reproducibility/n26-arithmetic-export-inputs.jsonl.gz --asset-root "<n26-root>" --output "<new-bundle-directory>"
```

命令只读取明确列出的文件；先逐文件核对冻结哈希，再在复制时再次核对。
它输出 `SUMMARY.json`、`FILES.jsonl.gz`、`PACKAGES.json` 和分卷 ZIP。
这只是已知直接依赖种子，不保证递归闭包完整。不要修改原 current/controls，
也不要把今天新生成的文件冒充旧哈希所绑定的证书。失败报告会列缺件/哈希差异数量；
应从相应冻结备份找回原始字节。

完整正式层使用原 current 的 `files` 映射：

```sh
python tools/export_frozen_assets.py --ledger "<n26-root>/outputs/n26-mixed-after-six-midarc-supplemental-current-v1.json" --ledger-sha256 ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1 --ledger-field files --root-map verification/reproducibility/n26-root-map.example.json --output "<new-formal-bundle-directory>"
```

先把根映射示例的 `local` 改成该服务器实际目录。两条 `original` 分别处理
Windows 与 WSL 源路径，最长前缀匹配；不会隐式猜测主机路径。
正式 current/final 自身及执行器应另作为版本固定的种子保存，不能只保存其依赖。
缺件、未映射、路径冲突、空清单或超出分卷预算的单文件均不能产出完整包。
默认每卷未压缩预算 512 MiB，可用 `--max-uncompressed-mib` 调整；它是数据完整性检查。

补数据不会自动消除 n26 的 **16** 个正式根、**4,957** 条条件前沿或
**344** 个算术 OPEN 子域；这三种数学计数属于不同范围。n26 全局最优性仍未证明。

## 完整 23–25 数据的发布路线

Git 保存源码、范围说明、索引与下载入口；完整历史冻结数据用版本固定的 Release
或 Zenodo 数据包承载。原迁回已有 **252 个 ZIP、6,155,404,577 压缩字节**，
但它们只覆盖服务器导入的 **898,000** 文件，还必须补本地复制的 **121,463** 文件
和 **622** 个迁回元数据文件。仅上传这些旧 ZIP 会再次得到不完整交付。

完整并集的规范清单已从只读库生成，作为同一 Release 的
`n23-n25-full-closure.jsonl.gz` 提供固定哈希下载；它是百万文件的完整索引，
不是这些文件的实际内容。SHA256 和下载地址见 [PROJECT_STATE.json](../PROJECT_STATE.json)。
全量数据包发布前需要核对全量当前字节、
包覆盖与索引。可重现该清单对照和导出：

```sh
python tools/audit_replay_inventory.py --inventory "<integration-root>/local-inventory.sqlite" --closure-ledger build/full-closure.jsonl.gz --report build/inventory-audit.json
python tools/export_frozen_assets.py --ledger build/full-closure.jsonl.gz --asset-root "<integration-root>/assets" --output "<new-full-bundle-directory>"
```

这一步没有宣布全量数据包已公开。之后才迁移并重放各阶数学入口；旧 `finalize_*`
属于历史验收/字节绑定，不能替代根隔离、区间不等式、树完整性与付款映射重算。

GitHub Release 支持每个 asset 小于 2 GiB、每次 release 至多 1,000 个 asset，
且总量/带宽没有公布上限，见 [GitHub 官方说明](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases)。
Zenodo 默认每个记录 50 GB、100 个文件，可将分卷集合再分组或申请配额，见
[文件限制](https://help.zenodo.org/docs/deposit/manage-files/) 与
[配额说明](https://help.zenodo.org/docs/deposit/manage-quota/)。选择数据托管方式不会改变数学接受状态。
