# 交付范围

2026-10-13，Asia/Shanghai。

本次发布保存现有证明成果，不恢复数学计算、不改变原始接受状态，
也不覆盖原工作区。所有导入文件保留原始字节；大文件使用可逆 gzip
及分片保存，原 SHA256 与分片 SHA256 都进入交付清单。

提交范围：

- 本地 n11、n12、n14 的证明正文、证明代码与所选精确证书；
- n21–25 的共享证明源、最终正文、接受件及其限定；
- n26 的原始证明代码、正式当前/独立最终对、最新算术当前/独立检查对；
- 可明确追踪的来源目录、冻结版本和哈希清单。

初始提交不是整个 100 GB 级历史工作区的镜像。
庞大的逐叶历史记录、编译缓存及重复中间文件不能仅由正文或
`VERIFIED.json` 替代。清单逐项记录已提交文件，并明确标记未提交范围；
本批没有完成所有历史文件的逐项库存清点。
未交付的逐叶依赖意味着相关原始全链命令在普通新克隆中尚不保证可运行。

保存接受件和验证交付哈希，不等于本轮独立重做了数学证明。
本仓库的字节检查器遇到缺件、改字节或错误封装必须失败。

## 2026-10-14: portable mathematical checks

The new `tools/check_math.py` uses only small `math_data/` snapshots. The n12
entry recomputes all 7041 terminals of the k10 branch, while n11 performs
root, configuration geometry and finite stress-field checks. Neither entry
replays every analytic/global obligation; see `REPRODUCIBILITY.md`. These new
entry points need no historical Windows/WSL path mapping or large-file restore.
The original delivery manifest is preserved byte-for-byte in
`manifests/history/FILES-20261013.jsonl.gz`; the live manifest tracks maintained
documentation and new assets. Original proof-bundle bytes are unchanged.

## 2026-10-14: quantified missing frozen inputs

The [23–26 audit](REPLAY_ASSET_PLAN.md) compares the pre-update delivery
manifest with the complete migrated n23–25 inventory and the n26 arithmetic
direct-input ledger. The complete union remains outside Git. A separate
55-file core Release supplements selected bearing inputs and has its own
package index; it is not included in the repository's logical file count.
Its successful restoration is a byte check, not a new mathematical replay.
