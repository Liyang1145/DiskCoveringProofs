# HARK_ARCHIVE — DiskCoveringProofs 工作区归档（分支 archive/hark-work）

- 来源：Hark 沙箱中的 n=11 工作目录 `dcp-n11-lean`（约 13 GB，现为 `hark-archive/n11`）、n=26 工作目录 `dcp-n26`（约 2 GB，现为 `hark-archive/n26`）与 `PROGRESS_RUBRIC.md`（现为 `hark-archive/PROGRESS_RUBRIC.md`）
- 归档日期：2026-10-19（Asia/Shanghai）
- 这是一个**孤立分支**（orphan），只含 `hark-archive/` 与本文件，不与 main 共享历史；不打算合并 main。
- 状态快照为 2026-10-19 傍晚的工作区状态；归档时 n=11 / n=26 的看护循环可能仍在跑，之后的新产物不在此分支。

## 目录

| 路径 | 内容 |
|---|---|
| `hark-archive/PROGRESS_RUBRIC.md` | 进度百分比的固定口径（n=11 / n=26） |
| `hark-archive/n11/` | n=11 Lean 形式化工作线：LOOP_RUNBOOK / LOOP_STATE / STATUS、`src/`、`lean/`（不含 .lake）、`lean-core/`、`c450-replay/`、`energy/`（证书 certs/、split/ 节点 JSON、parsed.json、lean-core、lean-wip 草稿、ledger.jsonl）、`class33/`（drive_sec.sh / drive_core.sh / build_core.sh、py/、data/、lean-core/、sector-build 的 2888 个 sector `.lean` 源、ledger.jsonl、日志）、`wip/` 文档与证据、`wip-build/` 的计划与 Mathlib ltar 清单、`ci/` README/ledger/mon.py |
| `hark-archive/n26/` | n=26 算术层：全部 Python 脚本与检查器（verify_certs*.py、certify_box.py、bnb*.py、local/certA.py、certB.py、v3replay/certB_*.py、pilot59.py、assemble.py 等）、STATUS / LOOP_STATE / LOOP_RUNBOOK、`ledger.jsonl`、`tree.txt`、`certs/`、`certs1669/`、`certs_old/`、ROOT25-FOREST-INDEX.json、regress_v3.json、`local/`（FOREST-Q6.json、**missing_closed/ 5432 个缺失叶精确证书**、recheck*.jsonl、leaves/）、`v3replay/`（fleaves/、lleaves/、subtrees/、verA/verB 结果 JSON、open23_*、V3-REPLAY-RESULT.json）、`dl/` 中 <50 MB 的文件（含 midarc.json.gz） |
| `hark-archive/n11/DEDUPED_ON_GITHUB.tsv`、`n26/DEDUPED_ON_GITHUB.tsv` | 本地文件与本仓库 `ci/n11-build` 或 `main` 上**逐字节相同**（git blob sha 一致）的清单——这些没有重复提交，表中给出仓库内已有路径 |
| `*/ARCHIVE_SKIPPED_SUMMARY.txt` | 按类别统计的未搬文件数与体积 |
| `n26/EXCLUDED_BIG_FILES.sha256` | 因体积未搬的大文件的 sha256，重建后用于校验 |

## 刻意没搬的内容及原因

- **编译产物**：`.olean/.ilean/.ir/.c/.private/.server/.a/.so`（n11 class33/sector-build 的 2888 个 .olean 约 844 MB 等）——可由源码重放生成。
- **工具链与缓存**：`.elan/`（约 3.2 GB）、`.lake/`（含 packages_old）、`wip-build/mlib`（Mathlib 缓存约 6 GB）、`wip-build/tc-cold`（冷工具链约 2.3 GB）、`__pycache__`、`*.pkl`（n26 v3replay 遍历/待办缓存 34 个约 351 MB，可由脚本重跑生成）。
- **已在 GitHub 上的内容**：`ci/repo/`（= 分支 `ci/n11-build` 的本地镜像）、`dcp-n26/repo/`（本仓库 main 的稀疏克隆，HEAD c07d79a = tag `proof-assets-core-20261014`，已在远端）、`ci/artifacts/`（CI 下载的结果与日志，可在 Actions 页面重取）、以及 DEDUPED 清单里的逐字节重复文件（含 `wip/lean/N11Formalization` 全部 Lean 源——已在 `ci/n11-build:ci-n11/lean/`；69.9 MB 的 `Ladder49_jt_kkt_z.lean` 也在那里，blob 6dd4447…）。
- **单文件 >50 MB**：`dcp-n26/dl/root25.json`（480 MB）、`root25.json.gz`（217 MB）、`root25-slim.json`（184 MB）、`midarc.json`（54 MB，其 .gz 已搬）、`v3replay/V3-REPLAY-TREE.json`（258 MB）。
- **作废中间件**：`*_abandoned.json`（v3replay 中被放弃的子树/叶尝试）。
- 空的 `.out` 日志、符号链接。

## 如何重建

### n=11
1. Lean 源：`ci/n11-build` 分支的 `ci-n11/lean/` + 本分支 `hark-archive/n11/{energy/lean-wip,class33/lean,class33/lean-core,class33/sector-build,lean-core}`。
2. 工具链：elan + Lean 4（`lean-toolchain` 见各项目；本地用过 v4.35.0 / lean-4.33.1 aarch64 包），`lake exe cache get` 取 Mathlib 缓存。
3. class33 q0m2 sector 回放：`class33/drive_sec.sh`（分块驱动，生成 2888 个 sector .olean）；核心库 `class33/build_core.sh` / `drive_core.sh`。
4. CI：分支 `ci/n11-build`，工作流 `n11-main.yml` / `n11-energy.yml` / `n11-class.yml`（说明见 `hark-archive/n11/ci/README.md`），https://github.com/Liyang1145/DiskCoveringProofs/actions?query=branch%3Aci%2Fn11-build

### n=26
- `V3-REPLAY-TREE.json`：`cd v3replay && python3 assemble.py`。输入为 main 上的 `cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json`（脚本通过 `DCP_MAIN_REPO` 找 main 的检出，默认 `hark-archive/n26/repo`，见下文「在新机器上运行」）+ 本分支的 `subtrees/`、`fleaves/`、`lleaves/`、`open23_assembled.json`。结果 sha256 应为 `beab24c50223608f277d984f0cde2df7c7f7416b35e93c6d94c694c9d8b9aa07`。
- `dl/root25*.json`、`midarc.json`：来自本仓库已发布的冻结数据（Release `proof-assets-*-20261014`，见 main 的 `docs/REPLAY_ASSET_PLAN.md` 与 `tools/restore_frozen_assets.py`）；`midarc.json` 也可由已搬的 `dl/midarc.json.gz` 解压。用 `n26/EXCLUDED_BIG_FILES.sha256` 校验。
- `*.pkl` 缓存：由 `v3replay/certB_walk.py`、`certB_prep.py`、`local/rebuild_lleaf_boxes.py` 等重跑生成。
- 脚本已去掉沙箱绝对路径，统一走环境变量（见下文「在新机器上运行」）。

## 在新机器上运行

脚本已不含 Hark 沙箱绝对路径，克隆到任意位置、从任意 cwd 运行即可。路径根由 `hark-archive/_paths.py`（Python）和 `hark-archive/_paths.sh`（bash，脚本内 `source`）统一解析：每个 Python 脚本顶部有 4 行引导代码，从自身 `__file__` 向上找到 `hark-archive/` 目录并 `from _paths import ...`；每个 `.sh` 顶部 source `_paths.sh`。

| 环境变量 | 用途 | 默认值 |
|---|---|---|
| `DCP_N26_ROOT` | n=26 工作树（原沙箱 dcp-n26） | `<仓库>/hark-archive/n26` |
| `DCP_N11_ROOT` | n=11 工作树（原沙箱 dcp-n11-lean） | `<仓库>/hark-archive/n11` |
| `DCP_MAIN_REPO` | 本仓库 **main** 的检出（v3replay/assemble*.py、replay*.py、propose.py、chk_tight*.py、trycerts.py、local/rebuild_lleaf_boxes.py 读 `cover26/proof_bundle/...`，并 import 其中的 `n26_force` 等模块） | `$DCP_N26_ROOT/repo` |
| `DCP_TMP` | 原来放在 `/tmp`、`/var/tmp` 的编译产物/暂存（`lc/`、`en/`、`c33/`、`wb/`、`stage/`、`ana/`） | Python：`tempfile.gettempdir()`；bash：`${TMPDIR:-/tmp}` |
| `LEAN_TOOLCHAIN` | Lean 工具链前缀（含 `bin/lean`、`lib/lean`） | `${ELAN_HOME:-~/.elan}/toolchains/leanprover--lean4---v4.33.1`；不存在时用 `lean --print-prefix` |
| `LEAN` | lean 可执行文件 | `$LEAN_TOOLCHAIN/bin/lean` |
| `LEANTAR` | leantar（仅 wip-build/fetch_mathlib.py） | PATH 中的 `leantar`，否则 `$LEAN_TOOLCHAIN/bin/leantar` |
| `C450_LEAN_TOOLCHAIN` | 仅 n11/c450-replay/build.sh；原回放用的是 slim core-only Lean v4.35.0 | `$LEAN_TOOLCHAIN` |

路径中不要含空格（部分 shell 脚本保留了原来的不加引号写法）。少数脚本（如 n11/energy/control.py、roundtrip.py）按原设计把结果写到**当前目录**的相对路径，需要时先 `cd` 到脚本所在目录。

**依赖**
- n=26（纯 Python，无 Lean）：Python ≥ 3.10（验证用 3.12.15）；`pip install numpy scipy mpmath python-flint cvxpy`（验证用 numpy 2.5.4、scipy 1.18.1、mpmath 1.4.1、python-flint 0.9.0、cvxpy 1.9.3）。只跑检查器（verify_certs*.py、local/certA.py / certB.py、check_local_slab.py 等）只需 numpy + mpmath；搜索/构造脚本（certify_box.py、bnb*.py）还要 python-flint、cvxpy、scipy。
- n=11：Lean **v4.33.1** + Mathlib **0df444a3**（`elan toolchain install leanprover/lean4:v4.33.1`；Mathlib 用 `lake exe cache get` 取缓存）。core-Lean 回放（class33/、energy/lean-core、c450-replay）不需要 Mathlib；Python 检查脚本（energy/checker.py、control.py、class33/py/*）只需 Python 标准库。
- n11/fetch.sh 依赖 Hark 的 `apicall` 命令，换机器时用 `gh api repos/Liyang1145/DiskCoveringProofs/contents/<path>` 代替。

**两个按哈希钉住的检查器保持原字节不变**：`n26/local/certB.py`（`local/FOREST-Q6.json` 记录 sha256 `f8dc2f98…5be18`）与 `n26/verify_certs_v3_pre_slabforest.py`（`ROOT25-FOREST-INDEX.json` 记录 sha256 `cbb67463…ca6b`）。它们文件里仍是原沙箱根路径字面量；直接运行请用 `python3 hark-archive/run_pinned.py <脚本> [参数]`（先核对 sha256，再在内存里把根路径换成 `$DCP_N26_ROOT` 后执行）；被其它脚本 `import certB` 时由 `_paths.py` 里的 import hook 做同样的内存替换。

**示例**
```bash
git clone --branch archive/hark-work --single-branch https://github.com/Liyang1145/DiskCoveringProofs.git DCP
cd /anywhere
python3 DCP/hark-archive/n26/verify_certs.py DCP/hark-archive/n26/certs/1670.json          # 与 regress_v3.json 中 1670 记录一致
python3 DCP/hark-archive/run_pinned.py DCP/hark-archive/n26/verify_certs_v3_pre_slabforest.py DCP/hark-archive/n26/certs/1681.json
python3 DCP/hark-archive/n26/local/check_local_slab.py                                       # FOREST-Q6 结构检查，PASS
(cd DCP/hark-archive/n11/energy && python3 control.py)                                        # 274/274 正例 + 负例全拒
# main 检出（v3replay 需要）：
git -C DCP worktree add hark-archive/n26/repo origin/main   # 或 export DCP_MAIN_REPO=/path/to/main-checkout
(cd DCP/hark-archive/n26/v3replay && python3 assemble.py)   # 需另取 V3 输入，见上文「如何重建」
# Lean core 回放：
export LEAN_TOOLCHAIN=~/.elan/toolchains/leanprover--lean4---v4.33.1
bash DCP/hark-archive/n11/class33/build_core.sh Class33Core/Defs
```

**保留的绝对路径（历史数据，故意不改）**：日志与输出文件 `n11/c450-replay/logs/bg-driver.log`、`n11/class33/logs/drive_sec.progress`、`n11/energy/logs/split-seg.log`、`n26/run2.err`、`n26/v3replay/bl_1.out`、`n26/v3replay/p.out` 中记录的是当时运行的原始输出；`.json/.jsonl` 账本与证书一律未改（改动会破坏 sha256 与证书绑定）。上面两个钉住的检查器同理。

## 状态快照（2026-10-19）

### n=11 —— 未完成
- main（h450）与 energy 的 CI 为绿。
- class33 q0m2 sector：core-Lean 回放 2888/2888 个 .olean 已在本地生成，**仅为预验证**（未经 CI、未做 axiom 审计）。
- class CI：提交 8de79f7 的 class 运行（run 39107672806）因 runner 关机失败（335 ok、0 真失败），已重跑，**结果待定**。
- axiom 审计：**未做**。rep7 / rep1 sector 回放未完成。
- 因此 n=11 形式化**不能称已完成**。

### n=26 —— 仅算术层，不得称已证
- root25 344/344 盒算术层闭合（343 CLOSED + 1669 CLOSED_WITH_LOCAL_SLAB_FOREST）；v3 重放树 OPEN 0（sha beab24c5…）。
- 缺失叶：certA 5432/5432；certB 约 2.0k/5432（快照时 `local/recheckB_missing.jsonl` 中 1998 个不同叶 okB=true，0 失败；看护循环此前报告约 1887–2080），**双复核未完成**。
- LOCAL-SLAB 接口引理**未写**；ε 扰动精确检查未做。
- 959/1023 盒**不可重建**（不在 v3 树，pinning/SYSTEM.json 未公开）；root28 真实 OPEN 盒未公开。
- 几何付款 0%。**n=26 不得称已证。**
