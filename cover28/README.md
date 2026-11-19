# 二十八个等圆盘覆盖单位圆盘

本包复验了两侧严格界证书，得到
$$
0.220001\le r_D(28)\le 0.225724991191.
$$
上界构造包含 28 个有理圆心，其覆盖范围是整个闭单位盘。全局最优性仍待证明。[数学证明](../cover27/proof_bundle/research-2026-11/baseline/proof.md) · [有理圆心和半径](../cover27/proof_bundle/research-2026-11/baseline/cover-28-rational.json)

从仓库根目录复算，使用 Node.js 与 Python 3，保留 Python 断言。

```sh
node cover27/proof_bundle/research-2026-11/baseline/area27.js 28
python -B cover27/proof_bundle/research-2026-11/baseline/verify_rational_cover.py cover27/proof_bundle/research-2026-11/baseline/cover-28-rational.json
```

下界来自五种边界拥有者数量的面积排除。上界用有理数和整数平方根外包验证 Voronoi 候选极值。下一步可从两端缩小这个区间。
