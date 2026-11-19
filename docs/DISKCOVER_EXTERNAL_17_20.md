<!-- SPDX-License-Identifier: MIT -->
# n=17–20：外部证明与复验交接

[VonEquinox/DiskCoveringSolve](https://github.com/VonEquinox/DiskCoveringSolve/tree/089584973f41e6374ce110f6e5b5ee456df19352) 已发布这四阶的计算机辅助全局最优性证明主张，不只是数值构型。本次只做了只读检查：用 Git 核实上游提交，按固定提交下载四份说明，逐字比较并记录 SHA-256；**没有运行上游检查器，没有独立验证全局证明，也没有将证明包移入本仓库**。

## 可重放入口

在隔离、无凭据的环境中审查固定版本的 Makefile、运行器和 C++ 源码后，再执行下述命令。要求 Python 3.10+（保留断言）、C++17 和 Make；验收路径不依赖第三方 Python 包。下载之后可离线重放。运行前预留磁盘及内存，尤其是 n=20。

```sh
git init DiskCoveringSolve-replay
cd DiskCoveringSolve-replay
git remote add origin https://github.com/VonEquinox/DiskCoveringSolve.git
git fetch --depth=1 origin 089584973f41e6374ce110f6e5b5ee456df19352
git checkout --detach FETCH_HEAD
test "$(git rev-parse HEAD)" = 089584973f41e6374ce110f6e5b5ee456df19352
unset PYTHONOPTIMIZE
make cover17-integrity cover18-integrity cover19-integrity cover20-integrity
# Each report directory must not already exist. Save stdout, stderr, and status separately.
python3 -S -B cover17/run_verification.py --report-dir /tmp/cover17-fresh-reports
python3 -S -B cover18/run_verification.py --report-dir /tmp/cover18-fresh-reports
python3 -S -B cover19/run_verification.py --report-dir /tmp/cover19-fresh-reports
python3 -S -B cover20/run_verification.py --workers 2 --report-dir /tmp/cover20-fresh-reports
```

| n | 上游声称的精确对象与主检查范围 | 要求的成功标记（且进程退出码为 0） |
|---|---|---|
| 17 | 157 变量整数二次系统指定隔离根的平方半径坐标（索引 82）；重建六族中 1,344 个存活轨道，验证非候选与候选分支。 | `COVER17 EXACT MASTER REPLAY PASSED` |
| 18 | 174 变量整数多项式系统的指定隔离根；两套证书独立执行验收，比较七族存活集、验证两根精确同一性。 | `COVER18 REQUESTED REPLAYS AND EXACT LINKAGE PASSED` |
| 19 | `1/sqrt(13)`；两路检查同一精确构型、力学与七族存活集。两路共享部分归约及代码谱系，不等同两次独立外审。 | `COVER19 REQUESTED REPLAYS AND EXACT LINKAGE PASSED` |
| 20 | 198 变量整数二次系统的指定隔离根；先按存储清单还原 197,440,381 字节的分包，再重建八族和验证全部连续分支。不要绕过外层运行器直接运行原始验收程序。 | `COVER20 EXACT MASTER REPLAY AND INPUT RECONSTRUCTION PASSED` |

另在上游固定提交下核对 `cover{17,18,19,20}/INPUT_MANIFEST.json`；n=20 还用 `STORAGE_MANIFEST.json`，并应检查上游提及的独立方程、雅可比和面表核对程序是否在此次实际执行。输入完整性通过并不等于计算重放通过；旧报告同样不能标为本次结果。

## 仍需偿付的数学义务

逐阶把任意圆心的覆盖归约为程序枚举域，核查 Voronoi 退化处理、根面剥离归纳及每项必要条件剪枝，再审计连续参数域完整分割和每片精确判据。表内所谓存活轨道数不是无剪枝总数。核对达到构型确实覆盖整个闭盘（不是只覆盖边界或采样点），并与排除严格较小半径的证书对应到同一半径；n=18、19 两路交叉相符不能代替外部数学复核。验收必须区分字节一致性、重放成功、数学证明审查和证明助手形式化。这里没有声称其中任何未执行步骤已完成。

## 固定提交的入口摘要

以下为原始 README 字节的 SHA-256（不是证明包哈希）：

| 文件 | SHA-256 |
|---|---|
| `cover17/README.md` | `de6f403a6d78741e3ec36b7ffa04d35f7cf23ff003d378bda963ef753b930f20` |
| `cover18/README.md` | `1424f41c9d119eb5f43178a0a8eef68c063c339d904bc7c1793759aad069cf3e` |
| `cover19/README.md` | `1ac70f99407605adbaaee41161c6d52c563a9ec5065b2092859db7993eeb4fa9` |
| `cover20/README.md` | `982071a7b20f0893cea28e56c33fb29f311e2490c371fcac86d5189bd4511bde` |
