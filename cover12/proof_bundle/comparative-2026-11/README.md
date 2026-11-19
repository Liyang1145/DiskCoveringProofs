# 十二盘覆盖的独立作答

以下是同一道数学题的本地独立作答原稿。各目录附有该结论用到的证书及验证源代码。

| 来源 | 原稿结论 | 重放入口 |
|---|---|---|
| [订阅 · Sol](subscription-sol/proof.md) | 全局最优 | 目录内 `python -B verify.py` |
| [中转站 · Sol](bear-sol/proof.md) | 全局最优 | 目录内 `python -B replay.py`，需要 NumPy |
| [中转站 · Astra](bear-astra/proof.md) | 全局最优 | 原稿末节列出 Python 命令和 C++ 转角核的构建命令 |
| [订阅 · Astra](subscription-astra-partial/proof.md) | **全局最优性未证明**。给出严格全局下界、覆盖构造和局部最优性 | 原稿列出的 `verify_local.py`、`verify_class.py`、`verify_upper.py`、`verify_lower.py`、`verify_box.py` |

各路线的本次执行范围见[复验记录](../../../docs/PROOF-ASSET-INTEGRATION-20261119.md)。主独立证明及全局验证入口见[独立证明包](../independent-2026-11/proof.md)。
