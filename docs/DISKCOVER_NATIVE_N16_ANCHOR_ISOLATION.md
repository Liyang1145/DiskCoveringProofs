<!-- SPDX-License-Identifier: MIT -->
# n=16：候选拓扑的锚点邻域排除

本项只排除候选图中一整块锚点邻域。不假设其圆心或三角见证点
接近候选。尚需排除同一图的邻域外角盒和其它拓扑图。

用[本仓库的代数存在性复验](DISKCOVER_NATIVE_N16.md)所得的固定根
以及该图的 54 条精确接触杆。固定 $q_0=(1,0)$ 后，令 $y_*$ 为
其余 74 个几何坐标，$w_e$ 为杆权，$\mu_i$ 为 11 个圆约束的乘子。
令 $A$ 为 54 个固定半径杆平方约束与 11 个单位圆条件的几何
Jacobian，$M$ 为加权杆图 Laplacian 加上锚点乘子对角块，
$P$ 投影到 22 个自由锚点坐标。取
$\nu=11/1000$，$W=\operatorname{diag}(w_e^2,\nu^2)$。
[上游书面证明](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover16/docs/r16_proof_zh.md)
提供此条件的提示；本仓库从锁定根数据构造矩阵并重新证明正定，
不直接取用上游矩阵证书或运行其程序。

核验器证明 $0<w_e<1/10$、$-\nu<\mu_i<0$，以及
$$M+200 A^T W A-(57/100000)P\succ0.$$
具体地，将几何坐标与乘子舍入到分母 $Q=10^{15}$，
并核对整根盒距舍入值小于 $\varepsilon=2/Q$。
舍入后的几何 Jacobian 的 Frobenius 范数小于 10。
每条杆行最多四个非零项，每项变化至多 $4\varepsilon$；
圆约束行最多两个非零项，每项变化至多 $2\varepsilon$。
于是 $\delta_A=400\varepsilon$ 是 $A$ 的算子范数误差上界。
若杆图最大度为 $\Delta$，逐行绝对值和给
$\delta_M=(2\Delta+1)\varepsilon$；平方杆权给
$\delta_W=\varepsilon/4$，且 $W$ 和舍入值算子范数均低于 $1/100$。
展开并三角估计，所述矩阵的总扰动小于
$$\delta_M+200[(20+\delta_A)\delta_A/100+
               \delta_W(10+\delta_A)^2]<10^{-8}.$$
对舍入矩阵减去 $10^{-8}I$，乘以 $Q^4$ 变成整数矩阵。
独立 Bareiss 消元逐个核对 74 个主顺序子式均严格为正，
因此由 Sylvester 判据得到精确根处的正定性。

现在令 $d=y-y_*$ 为同一杆图的任意实现与候选的差，
$\alpha^2=d^T P d$。假设所有杆长至多候选半径 $r_*$ 且锚点均
在单位圆上。记 $s_e=r_*^2-\ell_e^2\ge0$，
$v_e=|d_u-d_v|^2\ge0$，$u_i=|d_{q_i}|^2\ge0$。
精确二次展开给 $(Ad)_e=-v_e-s_e$、$(Ad)_i=-u_i$。
把已证明的根驻定方程与 $d$ 作内积，得
$$\sum_e w_e(v_e+s_e)=\sum_i(-\mu_i)u_i\le\nu\alpha^2.$$
由非负项的平方和不超过和的平方，
$d^TA^TWAd\le2\nu^2\alpha^4$，同时
$d^TMd=-\sum_e w_e s_e\le0$。若 $d\ne0$ 且
$\alpha\le1/10$，则正定矩阵在 $d$ 上的二次型应为正，
但上界 $400\nu^2\alpha^4-(57/100000)\alpha^2$ 不大于零。
故 $d=0$。特别地，这整个锚点邻域不可能实现严格更小的半径。

```sh
python verification/n16/anchor_isolation.py path/to/root16.json
```

本次输出 54 条正杆、74 个正主顺序子式。因为此证明依赖指定
候选子图的标签，应用到规范图时必须先验证保留的见证杆与锚点
循环的重标对应关系。
