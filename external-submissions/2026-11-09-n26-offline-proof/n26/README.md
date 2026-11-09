# 单位闭圆盘的 26 盘覆盖

本目录的构型、程序和证书均在本机独立生成。研究过程未使用网络、浏览器、下载或已有的 26 盘构型与题解。

## 全局最优值

$$
r_{26}=R_* = 0.2347000904004482396167901337766921275604959636549713917859\ldots .
$$

$R_*$ 是 [证明第 6 节](proof.md#6-一个精确的代数覆盖半径) 中方程 $F=F_d=F_h=0$ 的隔离根的第一坐标。同节给出精确达到该半径的 26 个圆心。任意摆法的归约和各分支如何合成全局下界见 [证明第 9 至 10 节](proof.md#10-全局最优性)。

[55 位小数的有理圆心](upper_refined.json) 在有理半径 $0.2347000904004482396167901337766921275604959636549713920$ 下通过完整裁剪 Voronoi 验证。[初次搜索圆心](upper.json) 也在 $U=0.234701$ 下通过，留有显式覆盖余量。

半径至多 $0.235$ 时，实际接触单位圆周的盘数在 14 至 17 之间，计入单点相切。对任意可能更小的覆盖，拓扑复算排除了至多 25 盘的全部摆法，以及 26 盘的 14 弧、15 弧、17 弧和 16 弧的全部带外弦类。16 弧无外弦类归约到同一候选剖分，其最小半径为 $R_*$。详见 [14 弧拓扑证书](topology14.md) 和 [15 至 17 弧的外层枚举](topology_outer.md)。

## 离线复算

本目录是独立的 Python 与 C++ 精确计算证明。`certificates/` 内的 39 个分片保存了完整证书。还原程序依次核对各分片、重组 ZIP 和 45 个证书文件的 SHA-256，再将证书还原到本目录。[分片清单](certificates/manifest.json)

~~~powershell
python restore_certificates.py
python check_global.py
~~~

验算使用 Python 标准库和本机的 `g++`，以 C++17 重建拓扑枚举。原证明各组曾逐组重建并通过检查，环境为 Python 3.11.9 和 g++ 16.2.0。本次归档的实际复算范围见 [执行记录](../replay/n26.txt)。

下面的命令仅复算上界、代数构型和分析部分，使用 Python 标准库即可。

~~~powershell
python check_all.py
~~~

可单独运行下列步骤。

~~~powershell
python verify_upper.py upper.json --radius 234701/1000000
python verify_upper.py upper_refined.json
python verify_eight_constants.py
python verify_radial.py lower_radial.json
python verify_radial.py radial_2265.json
python verify_fan.py
python verify_seam.py
python verify_joint.py lower_2275.json
python verify_joint.py lower_22835.json
python verify_joint.py branch_k14_low4.json
python verify_joint.py branch_k15_22862.json
python verify_joint.py branch_k15_22905.json
python verify_joint.py branch_k16_22846.json
python verify_joint.py lower_22855_split.json
python verify_joint.py lower_22861.json
python verify_joint.py lower_22862_core.json
python verify_joint.py branch_k17_22765.json
python verify_joint.py branch_k17_2287.json
python verify_joint.py lower25_2328.json
python verify_template.py
python verify_local.py
python verify_candidate_seams.py
python verify_candidate_cell.py
~~~

也可以逐组复算拓扑证书。程序重新生成枚举输入，逐项核验证书，并检查各组的开放数。

~~~powershell
python check_belt14.py --remaining belt14_residual.tsv --blocked belt14_residual_chords.tsv
python check_transfer14.py
python check_outer_layers.py --disks 25 --boundary 15
python check_outer_layers.py --disks 25 --boundary 16
python check_outer_layers.py --disks 26 --boundary 15
python check_outer_layers.py --disks 26 --boundary 16 --require-complete
python check_outer_layers.py --disks 26 --boundary 17
~~~

16 弧无弦类的整链复算核验全部填法，并要求候选角差证明的开放叶数为零。

~~~powershell
python check_outer_layers.py --disks 26 --boundary 16 --candidate-shell --halfturn --candidate-partition round4/candidate_halfturn_finish.json --require-complete
~~~

最初搜索可用本机已安装的 NumPy 和 SciPy 复现。以下前 8 个初值包含首次达到给定候选值附近的摆法。第二条命令对搜索发现的接触结构作高精度细化，输出仍须交给精确验证器。

~~~powershell
python search.py --starts 8 --seed 2601 --out reproduced_initial.json
python refine_template.py --out reproduced_refined.json
python verify_upper.py reproduced_refined.json
~~~

数值搜索还分别用种子 2601 与 2662 执行了 300 个初值。各外盘数的最佳数值结果约为 $0.237924,0.236470,0.2347000904004482,0.237215,0.241737$，依次对应 $k=14,\ldots,18$。这些搜索结果只用于寻找构型。任何分支的排除只引用已通过的有理或区间证书。可用 fan_radial_search.py 或 radial_search.py 生成新证书候选，并独立验算。

