# two-hub/AVERAGE-TRICK.md — 单圆容量比的下界恒等式（解析，全域）

**陈述（proved, 解析, 全称）**：设 $W:S^1\to[0,\infty)$ 可积，$h\in[0,\pi]$。则存在半角 $h$ 的弧 $A$（即弧长 $2h$）使
$$\int_A W\ \ge\ \frac{2h}{2\pi}\int_{S^1}W .$$

**证明**：对弧心位置 $\varphi$ 积分并交换次序。固定 $\theta$，使 $\theta\in A(\varphi)$ 的 $\varphi$ 构成测度恰为 $2h$ 的集合（$A(\varphi)=[\varphi-h,\varphi+h]$）。于是
$$\frac1{2\pi}\int_0^{2\pi}\Big(\int_{A(\varphi)}W\Big)d\varphi=\frac{2h}{2\pi}\int_0^{2\pi}W(\theta)\,d\theta .$$
平均给出下界，故最大值 $\ge$ 平均值。$\square$

## 推论（对承重结论的影响）

1. **均匀权在单圆上已最优**：任何非负权、任何"每条环盘弧单独受限"的论证，若只用一条圆上的弧，则单盘捕获份额的**下确界就是弧长比** $2h/2\pi$；角度整形（cos 多项式、峰谷布置）**不能**把该比降到 $2h/2\pi$ 以下。因此 n11 型结果不可能仅靠"单圆 + 非负权的峰谷"获得，必须使用**两圆之间的耦合**（同一环盘在两圆上的弧心由几何相互锁定）。

2. 对 n12 k10 的数值含义（$r=U=0.361102963744508672616920293904$）：
   - 外圆 $\partial D$：可行弧半角上确界 $\asin U=0.369795\ldots$，弧长比 $2\asin U/(2\pi)=0.11773$；
   - 于是任何权下，**必有一个可行环盘位置**捕获外圆权的 $\ge 11.773\%$；
   - 而"每盘预算"是需求的 $1/10=10\%$。差额只能由 hub 项的**耦合**填补（大外弧 $\Rightarrow$ 环心远离 hub $\Rightarrow$ hub 弧缩小/消失），这正是 n11 机制的本质。

3. 因此"联合 hub exposed-boundary + outer-circle 容量"的可行形式必须是：
   对**同一**环盘位置 $(\rho,\varphi)$ 同时计外圆弧与两 hub 弧，并令
   $$\sup_{\rho,\varphi}\Big[\int_{A_0}W_0+\int_{E_1\cap A_1}W_1+\int_{E_2\cap A_2}W_2\Big]<\frac1{10}\Big[\int_{\partial D}W_0+\int_{E_1}W_1+\int_{E_2}W_2\Big],$$
   其中 $A_j$ 由 $(\rho,\varphi)$ 与 hub 几何唯一决定。**单圆上的角度整形无益；增益只能来自 $A_0$ 与 $A_1,A_2$ 的锁定关系。**

写域：本节只作解析记录，不改 lead/shared 任何文件。
