<!-- SPDX-License-Identifier: MIT -->
# n=13：候选图的精确锚点隔离

此证书排除同一候选杆图、锚点向量欧氏距离至多 $1/8$
的全部严格较小半径实现；不要求圆心和三角面见证点接近
候选，也不自动排除该图的其它角盒。

在[已经复验的 119 维代数根](DISKCOVER_NATIVE_N13.md)处，
使用相同顺序的 47 条正权杆、9 条单位圆约束及 62 个自由几何
坐标。记 $A$ 为这些约束对几何坐标的 Jacobian，$M$ 为
加权棒图 Laplacian 加锚点乘子对角块，$P$ 为 18 个自由
锚点坐标上的投影。令 $\nu=49/2500$，
$W=\operatorname{diag}(w_e^2,\nu^2)$。
按[参考论文](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover13/docs/cover13_proof_zh.md)
的矩阵形式，独立构造并验证
$$ M+148 A^T W A-(19/10000)P\succ0. $$

将根盒中点舍入到分母 $10^{15}$，并认证整个根盒距离
舍入坐标不超过 $\varepsilon=2\cdot10^{-15}$。实际杆权在
$(0,1/10)$、圆乘子在 $(-\nu,0)$，舍入几何 Jacobian
Frobenius 范数小于 9。每条杆行上至多四项、每项误差至多
$4\varepsilon$；每条单位圆约束的至多两项各误差至多
$2\varepsilon$。因此取 $\delta_A=236\varepsilon$、
$\delta_M=(2\Delta+1)\varepsilon$（$\Delta$ 为杆图最大度）、
$\delta_W=\varepsilon/4$ 安全。算子范数扰动小于
$$\delta_M+148[(18+\delta_A)\delta_A/100+
               \delta_W(9+\delta_A)^2]<10^{-9}.$$
将舍入矩阵减去 $10^{-9}I$ 后做全整数无分数 Bareiss
消元，62 个顺序主子式全正。这里不使用外部矩阵因子，也不使用
浮点特征值。

与 [n=16 的驻定展开](DISKCOVER_NATIVE_N16_ANCHOR_ISOLATION.md)
完全相同：若另一实现杆长至多候选半径，写位移为 $d$、
$a^2=d^T P d$，则由负乘子与非负杆余量有
$d^TMd\le0$ 和 $d^T A^T W A d\le2\nu^2a^4$。
对 $a\le1/8$，上面正定矩阵的二次型不超过
$296\nu^2a^4-(19/10000)a^2\le0$，故只可能 $d=0$，
不能实现严格较小半径。

```sh
python verification/n13/anchor_isolation.py
```

候选与规范图的重标、以及完整角盒是否落在这个邻域，必须由连续域
分支核对器各自验证，不能用本页替代。
