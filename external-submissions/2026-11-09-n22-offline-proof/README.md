# n=22 独立证明与离线复证

本批归档提交者独立推导的 [n=22 证明](n22/proof.md)、同版验证源码和复算记录。文稿给出任意圆心的单位闭圆盘覆盖定理。所需公共半径为 \(\sqrt{t_*}\)，其中 \(t_*\) 是 \(29t^3-55t^2+19t-1=0\) 在 \((0.0641,0.0642)\) 内的唯一根。构型由原点、正七边形顶点与边中点、以及七个顶点方向上的内圈圆心组成。正文用凸性分块覆盖整个闭圆盘。

| 证明分支 | 材料 | 提交者复算范围 |
| --- | --- | --- |
| 构型与几何分类 | [正文](n22/proof.md) · [不等式核验](n22/verify.py) | 根区间、面积界和圆周格限制 |
| 13 个圆周格 | [分类和证书](n22/b13.md) · [验证器](n22/verify_b13.py) | 657 个精确有理线性下界 |
| 目标邻接型 | [能量证明](n22/topology.md) · [验证器](n22/verify_topology.py) | 邻接余量及角度能量下界矩阵的精确正定检验 |
| 其余 14 格邻接型 | [分类和证书](n22/b14.md) · [枚举](n22/b14_cases.py) · [验证器](n22/verify_b14.py) | 1,015 个无跨边外圈带和 6,485 个有一条跨边的外圈带，覆盖 231,658 个带标号情形，未闭合数为 0 |

四条命令的实际输出、退出码及覆盖范围见 [本次复算记录](replay/n22.txt)。[原始逐带结果](n22/b14-certification.jsonl)保留原字节。本次新鲜重放以分支和外圈带编号比对结果，所有记录一致。这个 JSONL 是输出记录，验证器从源码重新生成排除证书。

本提交与[项目状态](../../PROJECT_STATE.json)中的原有 n=22 权威证明并列。书面几何归约、与既有权威入口的精确根对照及维护者独立审阅另行记录。本次记录的范围是提交者对这一版材料的复算。

## 文件与复算命令

五个 Python 源文件和原始 JSONL 保留原字节。两份文稿仅调整了复算命令，去掉提交者本机工作目录，并将新鲜复算输出指向新文件名。各文件字节数和 SHA-256 见[交付清单](../../manifests/FILES.jsonl)。

本次使用 Windows x64、Python 3.11.9、NumPy 2.4.6 和 SciPy 1.17.1。两个线性放宽验证器使用本机已有的 NumPy/SciPy 来提出方向和乘子，接受条件由整数和有理数核验。其余两个验证器使用 Python 标准库。

从仓库根目录在 PowerShell 中运行以下命令。每条命令完成后检查退出码。为逐带结果选择一个尚未使用的文件名。

    Set-Location -LiteralPath 'external-submissions/2026-11-09-n22-offline-proof/n22'
    $env:OPENBLAS_NUM_THREADS = '1'
    $env:OMP_NUM_THREADS = '1'
    $env:MKL_NUM_THREADS = '1'
    python -B verify.py
    python -B verify_b13.py
    python -B verify_topology.py
    python -B verify_b14.py --all --workers 4 --nodes 48 --log b14-rerun.jsonl
