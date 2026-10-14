# 来源与区别

结构参考：VonEquinox/DiskCoveringSolve 的 `cover11` 至 `cover20`。
本地阅读参考版本为 `089584973f41e6374ce110f6e5b5ee456df19352`；
本次另以 GitHub API 核对了该仓库当前根目录。
未复制其全部 11–20 证明包，不声称本地 11、12、14 与公开包完全独立。

本地 11、12、14 的机制及来源入口分别为：

- `research-2026/team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md`
- `research-2026/n12-global/lead/GLOBAL-SYNTHESIS.md`
- `research-2026/next-cover-global/lead/FINAL-THEOREM-CHAIN.md`

本地 n21–25 使用 `research-2026/n21-25-synthesis` 中的共享数学源、
完整类型/连续域证书与后续补全接受链。
原文中的过期状态保留为历史，不作为当前结论；各阶 README 指向最终件。

来源路径、SHA256、复制规则和未提交项由 `manifests` 记录。
原始文件中的 Windows / WSL 绝对路径未改写；复现须显式映射。
没有添加新的数学 claim 编号，没有追加外部审查等级。
不替他人来源文件新指定许可证；公开发布或再分发前仍须核对权利。


## Portable public verification layer (2026-10-14)

`math_data/n11/` and `math_data/n12/` are small extracted witness inputs. Their
provenance records pin the archived source paths and SHA256 values. Fresh
checkers recompute inequalities; stored verdicts are never accepting premises.
The new layer is a separate implementation of the scoped arithmetic, not an
independent rederivation of the unrestricted analytic proof.

See `REPRODUCIBILITY.md`, `N11_CHECK_SCOPE.md`, `CONFIGURATIONS.md`, and
`LICENSE_SCOPE.md` for execution scope, exact configuration definitions and
the explicit first-party MIT grant. The original proof archive is not
relicensed. The original byte manifest is retained in `manifests/history/`.
