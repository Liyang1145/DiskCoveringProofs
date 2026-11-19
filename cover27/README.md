# 二十七个等圆盘覆盖单位圆盘

当前经过复验的范围为
$$
0.224645\le r_D(27)\le \rho_{27},\qquad
\rho_{27}\approx 0.23079558957419143670819.
$$
\(\rho_{27}\) 由有理盒中的 18 元多项式系统定义。同一个根给出覆盖整个闭单位盘的 27 个圆心，并在半宽为 \(10^{-6}\) 的 53 坐标规范盒内达到严格局部最优。全局最优性仍待证明。

## 数学材料

| 阶段 | 内容 |
|---|---|
| [基线证明与证书](proof_bundle/research-2026-11/baseline/proof.md) | 精确构造、局部证明、初始全局下界和 28 阶的严格界 |
| [后续下界](proof_bundle/research-2026-11/followup/proof.md) | 边界拥有者分类，无条件下界提高至 0.224640 |
| [径向范围与核心搜索](proof_bundle/research-2026-11/core-search/proof.md) | 核心覆盖、边界拥有者范数范围与对应搜索 |
| [边界对偶图](proof_bundle/research-2026-11/boundary-graph/proof.md) | 十四拥有者分支的度数限制 |
| [核心环带](proof_bundle/research-2026-11/core-cycle/proof.md) | 边界和核心环的图枚举与面积排除 |
| [核心剖分与最新下界](proof_bundle/research-2026-11/core-fills/proof.md) | 49,805 种核心剖分、十三盘辅助下界与无条件下界 0.224645 |

## 重放

以下命令从仓库根目录运行。基线的两个 Python 程序使用 SymPy 1.14。剖分和面积检验使用 Python 3 和 Node.js，重放十三盘辅助搜索还需要 `g++` 支持 C++20。Python 应保留断言。

```sh
python -B cover27/proof_bundle/research-2026-11/baseline/verify_cover27.py cover27/proof_bundle/research-2026-11/baseline/exact-27
python -B cover27/proof_bundle/research-2026-11/baseline/verify_local27.py cover27/proof_bundle/research-2026-11/baseline/exact-27
python -B cover27/proof_bundle/research-2026-11/core-fills/verify_bundle.py --global-lower
python -B cover27/proof_bundle/research-2026-11/core-fills/verify_bundle.py --only-aux13 --jobs 4
```

构型、分支条件、剩余范围和本次验证见[复验记录](../docs/PROOF-ASSET-INTEGRATION-20261119.md)。继续工作时需在 \(U=0.230796\) 下处理 14 至 18 名边界拥有者各分支的余域，或证明任何候选竞争配置可送入同根局部盒。
