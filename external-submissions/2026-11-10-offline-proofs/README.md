# n=25 独立离线证明与复算归档

提交者的离线原稿给出任意摆放圆心的 25 个等半径闭圆盘覆盖单位闭圆盘的精确最优半径
$r_D(25)=1/(\sqrt6+\sqrt3)$。正文包含 25 个圆心的构造、闭圆盘覆盖检查和区间核验下界。
本批是独立归档。仓库原有 n=25 权威入口仍见[项目状态](../../PROJECT_STATE.json)。

| 原稿 | 字节数 | SHA-256 |
| --- | ---: | --- |
| [proof.md](n25/proof.md) | 272,151 | `6f4954aee68f18f25f6162e9d6d40b9739be664957d74eb30b9186c5c202a91a` |
| [verify.py](n25/verify.py) | 189,041 | `5473ad1ec45614ecb40fd80cb1c80735a1a202756e48e239dcc79e34389fd05d` |
| [verify_k7.cpp](n25/verify_k7.cpp) | 281,140 | `c3120096621091142f3288f500b80093beea4218ca476e5c6476288faee12ae1` |

这三份文件保留提交者原字节。对照上游 `509c43f21eae` 的 Git 文件和交付清单，
三份原稿均按新文件归档。离线执行使用 Python 标准库和 C++17 标准库，区间划分由程序生成。

## 本批次实测

在 Windows x64、Python 3.11.9、MSYS2 GCC 16.2.0 下执行，以下命令的退出码均为 `0`。

| 检查 | 实测范围 |
| --- | --- |
| `verify.py` | 完整 Python 验证器，包括有限不等式、组合与局部正定性检查 |
| `high-fourteen-mark-pair` | 十四外围盘配对上界，287,195 个区间盒 |
| `tighter-octagon-fan` | 截断半径核验的单边、三边扇形与四边扇形，分别检查 133、99,509、3,471 个盒 |
| `nine-joint` | 九边形八类共 64 个实际占用排列 |

[复算记录](replay/n25.txt)载有命令、输出、编译诊断和原会话的八边形及九边形前置筛选记录。
本次逐模式全量重放与独立数学复审仍待开展。

## 离线执行

进入 [n25](n25/)，从已有的 Python 和 g++ 环境运行。Windows PowerShell 的本次复算范围如下。
[证明正文第 24 节](n25/proof.md#24-复算与分类闭合)列有完整模式和分类闭合顺序。

```powershell
python -I -B .\verify.py
g++ -std=c++17 -O3 -ffp-contract=off -fno-fast-math -pthread .\verify_k7.cpp -o .\verify_k7.exe
.\verify_k7.exe high-fourteen-mark-pair
.\verify_k7.exe tighter-octagon-fan
.\verify_k7.exe nine-joint
```
