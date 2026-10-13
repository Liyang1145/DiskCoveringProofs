# 复核：`lead/NINE-BOUNDARY-OWNERSHIP.md` + `lead/NINE-RING-NO-CHORDS.md`（k9 分支）

复核者：finite-reduction（本成员）。方式：逐步独立重推（不复用原文推理步骤），必要时用**组合/见证点**替代叙述；常量链用精确有理算术检查。
**结论：通过（未发现反例或数学错误）**；两处叙述我用更紧的论证替换（端点循环序、非邻不重叠），**未发现割线遗漏**（§5 说明为什么）。仅写法建议两条（§7），非纠错。
被复核文件：`lead/NINE-BOUNDARY-OWNERSHIP.md`、`lead/NINE-RING-NO-CHORDS.md`；依赖文件 `lead/INNER-ROOT-REDUCTION.md`、`lead/FOUNDATIONS.md`（只读）。

---

## 1 范围与前提（复核对象的口径）

- k9 分支：半径 $r$ 的覆盖、**恰好 9 个边界活动盘**，$0<r\le U=0.361102963744508672616920293904$（$U$ 为登记精确有理阈值）；其余 3 盘非活动（$\|h\|<1-r$）。
- "same-arc inner-root replacement"：每个边界活动盘换成同弧的内根盘。**我独立核对了 `INNER-ROOT-REDUCTION.md` 的关键不等式**（这是本条链的 WLOG 依据）：设外根 $t=\rho_+$、内根 $\rho_-$，$a=x\cdot u$，$m=\cos\alpha=(\rho_++\rho_-)/2$。
  - 若 $a\le m$：$\|x-\rho_-u\|^2-\|x-\rho_+u\|^2=2(\rho_+-\rho_-)(a-m)\le0$ ✓（内根更近）；
  - 若 $a\ge m$：$\|x-\rho_-u\|^2\le1-2\rho_-m+\rho_-^2=1-\rho_+\rho_-=r^2$ ✓（用 $\rho_++\rho_-=2m$、$\rho_+\rho_-=1-r^2$）。
  故 $D\cap B(\rho_+u,r)\subseteq D\cap B(\rho_-u,r)$ ✓：替换**保持覆盖**；弧与活动/非活动状态不变；新范数 $\in[1-r,\sqrt{1-r^2}]$（$\rho_-\le\sqrt{1-r^2}$ 由 $\rho_-\le\rho_+$；$\rho_-\ge(1-r^2)/(1+r)=1-r$ 由 $\rho_+\le1+r$）✓。故下文对"代表构型"的结论是覆盖存在性的 WLOG 结论 ✓。

## 2 逐步核对（k9 弧几何与最近心归属）

| # | 断言 | 复核 |
|---|---|---|
| V1 | 每弧角长 $\le2\asin r<\pi/4$ | ✓：ACTIVITY 弧半宽 $\alpha=\arccos\frac{1+t^2-r^2}{2t}\le\arccos\sqrt{1-r^2}=\asin r$（AM-GM）；$r\le U<4/11<3/8<\sqrt{2-\sqrt2}/2=\sin(\pi/8)$ ⟹ $\asin r<\pi/8$（$\asin$ 单调）⟹ 弧长 $<{\pi}/{4}$ ✓（常量链 §4 精确核对） |
| V2 | 8 条弧不能覆盖 $S^1$，故 9 条都 essential | ✓：$8\cdot2\asin r<8\cdot\pi/4=2\pi$（**严格**：$\asin r<\pi/8$）⟹ 总测度 $<2\pi$ ⟹ 不能覆盖；若某弧含于其余八弧之并则删去它仍覆盖 ⟹ 矛盾 ⟹ essential ✓（同时也排除重复弧：相同弧互相包含） |
| V3 | 中点循环序严格 | ✓：中点相同 ⟹ 短弧含于长弧（或两弧相同）⟹ 冗余 ⟹ 与 essential 矛盾 ✓ |
| V4 | 左/右端点循环序 = 中点循环序 | ✓ **我给出更紧证明**（§3.A）：任取一对，取割点使两弧落入同一提升；若左端点序与中点序相反，则短弧真含于长弧 ⟹ 与 essential 矛盾；右端点同理。原文只对"重叠邻域"陈述；**我的版本对所有弧对成立**（中点距离 $>\pi/8$ 的对不可能反转，因反转需 $\lvert L_i-L_j\rvert>2\delta>\pi/4\ge\lvert L_i-L_j\rvert$）✓ |
| V5 | 至多两弧共点（含共端点） | ✓ **更紧证明**（§3.B）：三弧共用 $p$ ⟹ 提升到 $p=0$ 后三弧都在 $(-\pi/4,\pi/4)$，按左端点排序，essential（无包含）给同序右端点，中间弧含于两端弧之并 ⟹ 冗余 ⟹ 矛盾 ✓ |
| V6 | 只有循环相邻弧重叠 | ✓ **更紧证明**（§3.C）：三弧中点 $ \alpha_i<\alpha_k<\alpha_j$、$A_i\cap A_j\ne\varnothing$ ⟹ $A_k\subseteq A_i\cup A_j$ ⟹ $A_k$ 的**排他片**（essential 保证非空）被覆盖 ⟹ 矛盾。重叠 ⟹ 中点间距 $< (L_i+L_j)/2<\pi/4$，提升无歧义 ✓ |
| V7 | 同半径内根对：任一实际弧内**至多一个 tie** | ✓：两内根心范数 $\le s=\sqrt{1-r^2}$，故中点 $\lvert m\rvert<s$（严格凸 + 互异），中垂线 $L$ 到原点距离 $d\le\lvert m\rvert<s$；$L\cap S^1$ 两点**短向**分离 $2\arccos d>2\arccos s=2\asin r$ ⟹ 长 $\le2\asin r$ 的弧至多含一个 tie 点 ✓（双根 $\alpha=\asin r$ 情形仍 $d<s$ ✓）。这条是"换手至多一次"的唯一依据 ✓ |
| V8 | 最近归属：每弧含排他开片；只可能相邻弧竞争；归属集是含排他片的闭弧；恰 9 段归属弧 + 9 个二点 switch；$S^1$ 上无三点 tie | ✓：非活动盘在 $S^1$ 上距离 $>r$（闭性 + 紧性）；非邻活动弧与 $A_i$ 不交（V6）⟹ 在 $A_i$ 上距离 $>r$；仅左右邻可竞争 ⟹ 平方距离差在 $A_i$ 内至多一个零点（V7）⟹ 不能"挖中洞再回来"，从排他片向两侧各延到一个 switch ⟹ 归属集为闭弧 ✓；三点 tie 会在 $S^1$ 上给出三弧共点 ⟹ 与 V5 矛盾 ✓ |
| V9 | 非邻环盘**作为闭盘**不相交 ⟹ 无三环共点、最近/Delaunay 公共点边只能是相邻标签、无全环三角形 | ✓：见 §3.D 的论证与测度矛盾（下）＋三环共点必含非邻对（9 个标签的任意三元组都含非相邻对；$\{i,i+1,i+2\}$ 含 $(i,i+2)$）⟹ 与非邻不相交矛盾 ✓；Delaunay 边 = 两盘（半径 $r$）有公共点 ✓；三环 Voronoi/Delaunay 顶点 = 三盘（半径 $r$）共点 ⟹ 同上矛盾 ✓ |
| V10 | 结论经内根替换仍成立 | ✓：替换保弧、保覆盖（§1），故对任何 $r\le U$ 的覆盖都存在满足上述九弧结构的代表构型 ⟹ 结论用于代表即用于存在性 ✓ |

## 3 我给出的四个组合论证（替代/收紧原文叙述）

**A（端点序 = 中点序）。** 取任一弧对 $(i,j)$，选割点使两弧都落在同一提升（两弧长 $<\pi$，其并测度 $<2\pi$，割点存在）。写 $A_k=[\alpha_k-b_k,\ \alpha_k+b_k]$（$2b_k=$ 弧长）。若中点序与左端点序相反：$\alpha_i<\alpha_j$ 且 $\alpha_i-b_i>\alpha_j-b_j$，则 $b_j-b_i>2(\alpha_j-\alpha_i)>0$，并且 $\alpha_i+b_i\le\alpha_j+b_j$（因 $b_j-b_i>-2(\alpha_j-\alpha_i)$）；于是 $A_i\subsetneq A_j$：与 essential 矛盾 ✓。右端点序同法 ✓。

**B（三弧不共点）。** 设 $A_1,A_2,A_3\ni p$；提升到 $p=0$：每弧含 $0$、长 $<\pi/4$ ⟹ $A_k=[l_k,r_k]\subseteq(-\pi/4,\pi/4)$，$l_k\le0\le r_k$。按左端点排序 $l_1\le l_2\le l_3$；essential（无包含、无重复）⟹ 右端点同序 $r_1\le r_2\le r_3$（否则 $A_2\subseteq A_1$ 或 $A_3\subseteq A_2$）。于是 $[l_2,0]\subseteq A_1$（$l_2\ge l_1$、$0\le r_1$）与 $[0,r_2]\subseteq A_3$（$l_3\le0$、$r_2\le r_3$）给出 $A_2\subseteq A_1\cup A_3$ ⟹ $A_2$ 冗余 ⟹ 矛盾 ✓。共端点情形含在内 ✓。

**C（非邻不重叠 + 见证点版）。** 设循环序中 $i,j$ 之间有弧（非邻），且 $A_i\cap A_j\ne\varnothing$；提升后 $\alpha_i<\alpha_j$，取中间某弧 $A_k$（$\alpha_i<\alpha_k<\alpha_j$）。
- 子命题 (a) $\alpha_k-b_k\ge\alpha_i-b_i$：否则 $b_k>b_i+(\alpha_k-\alpha_i)>b_i$ 且 $\alpha_k+b_k>\alpha_i+b_i$ ⟹ $A_i\subsetneq A_k$ ✗；
- 子命题 (b) $\alpha_k+b_k\le\alpha_j+b_j$：否则 $b_j<b_k-(\alpha_j-\alpha_k)<b_k$ 且 $\alpha_j-b_j>\alpha_k-b_k$ ⟹ $A_k\subsetneq A_j$ ✗；
- 由 $A_i\cap A_j\ne\varnothing$ 得 $\alpha_i+b_i\ge\alpha_j-b_j$，故 $A_i\cup A_j=[\alpha_i-b_i,\ \alpha_j+b_j]$（区间）$\supseteq[\alpha_k-b_k,\alpha_k+b_k]=A_k$ ✓。
**见证点收尾**：essential 给 $A_k$ 内一点 $q$ 不被其余八弧覆盖（排他点）；但 $q\in A_k\subseteq A_i\cup A_j$ ⟹ $q$ 被 $A_i$ 或 $A_j$ 覆盖 ⟹ 矛盾 ✓。（两版都成立；见证点版更短，但依赖上面的包含。）

**D（$J$ 内的弧 $\ge3$，且都在 $J$ 内）。** 设非邻盘 $i,j$ 有公共点 $p$（$\lvert p\rvert\ge1-2r>0$，因心范数 $\ge1-r$）。对 $x\in A_i$：$\lvert x-p\rvert\le\lvert x-c_i\rvert+\lvert c_i-p\rvert\le2r$ ⟹ $A_i\subseteq J:=S^1\cap B(p,2r)$（$A_j$ 同）✓。$J$ 是闭弧，半宽 $\alpha_J=\arccos\frac{1+\lvert p\rvert^2-4r^2}{2\lvert p\rvert}\le\asin(2r)$（AM-GM；$4r^2<1$）⟹ $\lvert J\rvert\le2\asin(2r)<\pi$ ✓ 且 $J\ne S^1$（否则需 $1+\lvert p\rvert\le2r<1$ ✗）✓。在 $J$ 的提升中写 $A_i=[l_i,r_i]$、$A_j=[l_j,r_j]$（不妨 $l_i<l_j$）：由 A，凡中点介于 $\alpha_i,\alpha_j$ 的弧，其左端点在 $(l_i,l_j)$、右端点在 $(r_i,r_j)$ ⟹ 该弧 $\subseteq[l_i,r_j]\subseteq J$（$J$ 是区间）✓。非邻 ⟹ **两个方向各 $\ge1$ 个中点** ⟹ 短方向（即 $J$ 内方向）至少含 $A_i,A_j$ 与 $\ge1$ 条中间弧：**$\ge3$ 条整弧在 $J$ 内** ✓。
测度：$2\pi=\lvert S^1\rvert\le\sum_k\lvert A_k\rvert\le\lvert J\rvert+6\cdot2\asin r\le2\asin(2r)+12\asin r$ ⟹ $\pi\le\asin(2r)+6\asin r$；对 $r\le U$ 为假（§4）⟹ 矛盾 ⟹ 非邻盘不相交（含相切）✓。

## 4 常量链（精确有理/整数算术，`evidence/no-chords-constants.txt`，14/14 通过）

| 项 | 精确核对 |
|---|---|
| $U<4/11$ | $11\cdot22568935234031792038557518369<4\cdot62500000000000000000000000000$ ✓ |
| $4/11<3/8<\sin(\pi/8)$ | $32<33$；$(23/16)^2=529/256>2=512/256$（$\sin(\pi/8)=\sqrt{2-\sqrt2}/2$）✓ |
| $2U<8/11$ | ✓ |
| $\sin(41/50)\ge41/50-(41/50)^3/6=546079/750000>8/11$ | $6006869>6000000$ ✓（Taylor 前两项，$[0,1]$ 上交错级数） |
| $\sin(373/1000)\ge2186104883/6000000000>4/11$ | ✓ |
| 单调性 | $\asin$ 在 $[0,1]$ 递增，$41/50,373/1000\in(0,1)$ ⟹ $\asin(2r)<41/50$、$\asin r<373/1000$（$r\le U$）✓ |
| 和 | $41/50+6\cdot373/1000=1529/500=3.058$ ✓ |
| $\pi>3.058$ | $\pi>12\sin(\pi/12)=3(\sqrt6-\sqrt2)$（内接正十二边形）且 $3(\sqrt6-\sqrt2)>1529/500$（$\iff4\sqrt3<15662159/2250000\iff3<2.4529\ldots$）✓ |

结论：$\asin(2r)+6\asin r<3.058<\pi$ 对一切 $r\le U$ 成立 ✓。

## 5 割线遗漏专项检查（结论：未发现）

- 全链只有两处出现"直线/割线"几何：
  1. **中垂线 $L$（V7 的 tie 引理）**：$L$ 是 $S^1$ 的割线，两点分离必须用**短向** $2\arccos d$；原文写 "smaller angular separation" ✓ 正确。若误用长向 $2\pi-2\arccos d$，结论会反向失效——我把这一点显式记为承重点，未发现原文有该错误。
  2. **$J=S^1\cap B(p,2r)$ 的弧端点**（§3.D）：只用弧长与端点序，不涉及直线段。
- 其余步骤（essential/端点序/共点/不重叠/归属/测度）**全部是 $S^1$ 上的弧测度与组合**，不存在把"相邻中心之间的弦长"当作 $S^1$ 弧长使用的地方；原文末尾也明确区分："本结论只排除公共覆盖点/最近心边，不排除任意直线段" ✓。
- 因此"两个完整弧在长度 $<\pi$ 的 $J$ 内 ⟹ 其间的完整弧都在 $J$"这一环**没有遗漏**：它的充分依据是 §3.A 的端点序一致性（对**所有**弧对成立，包含不重叠的远对）＋ $J$ 在提升中是区间。

## 6 范围与限制（诚实声明）

- 结论**条件于**：k9 分支（恰 9 个活动盘）、$0<r\le U$、内根替换后的代表构型；**未**涉及 k10/k11，**未**证明 hub 邻接或嵌入的直线对偶三角化（原文亦如此声明 ✓）。
- 本复核是**逐步人工重推**，不是形式化验证；常量链用了独立的精确有理检查脚本（同作者实现）。
- 本复核**不**声称"环盘之间没有弦"这类更强的几何陈述；只确认原文所声明的范围。

## 7 写法建议（非纠错）

1. `NINE-BOUNDARY-OWNERSHIP.md` 第 12 行的"最终序步"可替换为 §3.A/§3.C 的行内证明（原文自己标注需要独立组合检查；现已有）。
2. `NINE-RING-NO-CHORDS.md` 第 5 行对端点序的说明只覆盖"重叠邻域"；建议改为"任取一对（含不重叠远对）：若反转则短弧真含于长弧"，以消除读者对远对的疑问（远对的分离 $>\pi/8$ 使反转不可能，已在 §2.V4 说明）。
