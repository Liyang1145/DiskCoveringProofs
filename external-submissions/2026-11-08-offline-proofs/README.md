# n=11、12、14 离线复证材料

本批材料由提交者提供，与仓库既有源证明分别归档。各阶原权威入口见 [项目状态](../../PROJECT_STATE.json)。以下复算针对这里列出的执行器和证书。书面几何归约、不同精确根定义之间的同根关系及外部审阅各有独立的验证范围。

| 阶数 | 入库材料 | 本次复算范围 |
| --- | --- | --- |
| 11 | [既有文稿](../2026-11-08-sol-review/original/证明.md) 的同版 [源码和再生成输入](n11/) | 根与构型、一般位置归约中的有限不等式、链递推、局部正定性及双扇全域算术均复算通过。全域为 4475 个排除叶和 28 个近点叶。 [输出](replay/n11.txt) |
| 12 | [证明正文](n12/证明.md)、[全局下界](n12/全局下界.md) 和 [源码与证书](n12/) | 已复算构型、十一外围盘常数、十外围盘全域（539 个测度盒、80 个剪枝盒）及九盘切平面。九外围盘全量重放在本机出现内存不足时中断，附当前运行记录。 [构型与常数](replay/n12_verify.txt) · [十盘](replay/n12_ten.txt) · [九盘](replay/n12_nine.txt) |
| 14 | [上游已有证明包](../2026-11-08-sol-review/extracted/N=14/)及本次复算记录 | 核验了完整构型、局部证书、几何分类常数和 624 个面表代表，退出码为 0。[输出](replay/n14.txt) |

## 来源和文件范围

- n=11 文稿与既有审查所用的文件逐字节一致，SHA-256 为 `0e49e197f8246bcfa0a9224f48b6da79333666569104ab9081244ddd221f444a`。这次补入七个同版源文件，以及从源码重新生成的 `chain_windows.txt` 和 `fan_constants.txt`。
- n=12 的 C++ 区间库由附带源码构建。九外围盘证书解压后有 515,029 条记录，未压缩 JSONL 的 SHA-256 为 `6349cc5e4b9f201c022ee3e9ade844d8f6f66c28992ec8f21e6349dc180d315f`。`explore.py` 和 `ten_search.py` 记录探索过程。严格复算使用 Python 标准库和本机编译的区间库。
- n=14 的文稿、执行器与正式证书共 12 个文件，逐字节匹配 [既有审查](../2026-11-08-sol-review/REVIEW.md) 所用版本。仓库已有一份相同证明包，本次添加新复算记录。探索日志和生成阶段的中间力证书可由原工作区单独保存。
- 各入库文件的字节数和 SHA-256 见 [交付清单](../../manifests/FILES.jsonl)。原文件保留其来源和许可范围。复算输出另存，临时目录以相对路径显示。

## 离线复算

本次使用 Windows x64、Python 3.11.9 和 MSYS2 GCC 16.2.0，Python 与 C++ 断言均启用。各命令在对应阶数目录中运行，并检查退出码。

### n=11

进入 [n11](n11/)，按[原文第 7 节](../2026-11-08-sol-review/original/证明.md#7-离线复算)运行。第 7 节的命令能从源码重生成两个输入文件。C++ 需要支持 128 位整数的 g++。本次最后一条命令使用了 6 个线程。

### n=12

进入 [n12](n12/)。先按分片文件名顺序重组原压缩档。以下命令校验完整 SHA-256 后写入文件。九外围盘全量重放的运行时间取决于核心数和负载。

```powershell
@'
from hashlib import sha256
from pathlib import Path

base = Path(".")
parts = sorted(base.glob("nine_certificate.jsonl.gz.part????"))
data = b"".join(part.read_bytes() for part in parts)
expected = "baa3df55282d91445774e5682f9263d726c76acaa7f9b9f685a5d31ca25e83fc"
if sha256(data).hexdigest() != expected:
    raise SystemExit("Missing or corrupt nine-boundary certificate parts")
with (base / "nine_certificate.jsonl.gz").open("xb") as output:
    output.write(data)
'@ | python -I -B -
```

如果本目录已有 SHA-256 相同的原压缩档，可直接开始复算。

```powershell
python -I -B verify.py
g++ -std=c++20 -O3 -shared -static -ftrapv -o ten_intervals.dll ten_intervals.cpp
python -B -S ten_driver.py replay --file ten_certificate.jsonl
python -B -S nine_driver.py replay --file nine_certificate.jsonl.gz --jobs 12
```

### n=14

进入 [n=14 的上游归档目录](../2026-11-08-sol-review/extracted/N=14/)，运行 `python -B -S verify.py`。
