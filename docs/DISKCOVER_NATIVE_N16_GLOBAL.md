<!-- SPDX-License-Identifier: MIT -->
# n=16：全局最优性与精确重放

最小覆盖半径是 [已认证的 140 维代数根所对应的半径](DISKCOVER_NATIVE_N16.md)
$r_* = \sqrt{t_*}$，约为 $0.308219801898618$。这里是任意圆心的
计算机辅助全局证明，不是 Lean 形式化。圆心允许重合、在目标盘外，
或没有对称性。

1. [精确达到性](DISKCOVER_NATIVE_N16.md)：重新生成 140 个方程并
   验证收缩，找到同一个唯一隔离根；以精确接触和有理区间核对的
   三角链、圆弓覆盖整个闭单位圆盘。
2. [原生任意圆心归约与普查](DISKCOVER_NATIVE_N16_CENSUS.md)：
   反设一个半径 $r<r_*$ 的覆盖，选 $r<\rho<r_*$。在 $\rho$
   的严格余量内径向归一化、扰动，得到简单裁剪 Voronoi 对偶。
   用更松的有理测试半径 $U$ 只会扩大必要条件的角域。
   正长度边界拥有者数只能是 11 或 12，完整根面剥离给 93 和
   71 个规范轨道；两种遍历逐面相同。每个来自覆盖的见证杆短于 $r_*$。
3. [非候选连续域](DISKCOVER_NATIVE_N16_FORCE.md)：新生成并重新
   精确复验 93 个 11 拥有者轨道和 70 个 12 拥有者轨道，每个力树
   排除整个相应角域。以原生面表绑定证书并检查没有遗漏。
4. 唯一剩余的是 12 拥有者候选图。将任意该图的实现按图同构重标，
   反向时反射，并旋转**原始候选锚点** $q_0$ 到 $(1,0)$。
   自行重建同一全图的 78 个杆，验证与原生面表一一对应。
   重放固定版本的候选角盒、整数向量与半平面乘子作为
   **待核验数据**，不运行外部验证器、不采信其验收报告。
   5173 次严格内部分裂覆盖全部根角域；5052 个终端盒的有理力
   不等式排除半径小于 $r_*$；122 个终端盒则由独立核验的
   [锚点隔离定理](DISKCOVER_NATIVE_N16_ANCHOR_ISOLATION.md)排除。
   后者以原始 $q_0$ 为基准，验证整个角盒的平方位移和不超过
   $1/100$，并非只测角盒中心。重复、循环、孤立或未决节点均拒绝。

由 2 每个严格反例必属于这 164 个轨道之一，3 和 4 一一排除；
与 1 的同根上界合起来即得 $r_D(16)=r_*$。

## 一键重放证明（不改求解器接口）

```sh
base=https://raw.githubusercontent.com/VonEquinox/DiskCoveringSolve/089584973f41e6374ce110f6e5b5ee456df19352/cover16/proof_bundle/core
curl --fail --location "$base/root16.json" -o root16.json
curl --fail --location "$base/candidate16_tree.json.gz" -o candidate16_tree.json.gz
python verification/n16/replay_global.py root16.json candidate16_tree.json.gz
```

固定根 SHA-256：
`a89dfe7e356a670176622e0726a0e7d27f14136e5e1d79326f9afedac285ab9e`；
候选输入树 SHA-256：
`3fa2a55f460b35678ad92f977e2c0bae52c0b1e8ad6fc27957835d87f362fb31`。
根/树数据由参考作者提供；拓扑普查、163 张非候选图的完整证书、
矩阵正定性及全部终端检查均由本仓库重新完成。接受路径只需要
Python 标准库和 C++17 编译器，数值优化器不参与接受。
