# CENTRAL-CRESCENT-STRESS —— 中央两 faces 的 exact crescent 结构：quartic 不可消，真正可用的凸对象是**固定圆盘**（cutting-plane），在候选处精确活跃

> 路由 r20-alternative/cline2；只写本目录；无子派生；输入 = `n11/upper/certified_object.json` 的**精确有理**圆心（1e17 标度）
> 与 `lead/R20-CENTRAL-SPAN-NECESSITY.md`、`lead/R20-CHAIN-HUB-CONVEXIFICATION.md`(C879)、
> `lead/R20-CHAIN-VARIANCE-LOCALIZATION.md`、`lead/HUB-DISTANCE-QUADRATIC-DUAL.md`(C890)。
> 本件**不**沿用 span 过滤（该过滤在候选处 slack = +3.63e-3，已知不 sharp，见 `CENTRAL-SPAN-DUAL.md` §6），
> **不**做任何 remotebox 排除，**不**宣称全局下界。全部新读数是**诊断**（60 位 mpmath，输入有理，输出非证书）。
> 已登记：**C894**（proved-exact，crescent 对称差 + 等半径根轴保号 + 单盘精确化）、
> **C895**（proved-exact，quartic hub coupling 不可被加权消去）、**C896**（numeric，候选处读数与精确性余量）。
>
> 证据/复现：`central_crescent_stress.py` → `central_crescent_stress.json`
> （`py -3 -B -X utf8 research-2026/team-current/r20-alternative/central_crescent_stress.py`）。
> 其中 [S] 段为 sympy **符号**恒等式与不可消性，[C] 段为候选读数（`residual = 0` 处即符号验证通过）。

---

## §0 结论速览（三条）

1. **quartic hub coupling 不能被加权消去**（§2，符号精确）：两 faces 的约束多项式
   `F_{c_i}(a,b)` 的 deg-4 分量是 `-|a|^4 |b-c_i|^2`（对 a）与 `-|b|^4 |a-c_i|^2`（对 b）；
   正（乃至任意实数）加权 `λ0 F_{c0}+λ4 F_{c4}` 的 deg-4 分量 = `-|a|^4(λ0|b-c0|^2+λ4|b-c4|^2)`，
   恒消失 ⟺ `λ0=λ4=0`（`c0≠c4`）；混合 (2,2) 分量同样秩 2、不可消。二次约束（hub 范数、链 pins、局域化盘）
   无 deg-4 分量 ⇒ **无法用它们把 quartic 抵消**。故"正加权 → 二次（凸）stress"这条路**按其字面形式不存在**，
   本件明确记为 **unresolved（器械不存在，不是数学命题被否证）**。
2. **真正可用的 orientation-preserving 凸对象是"固定圆盘"**（§3）：crescent 恰是过 `(A,C)` 的两个等半径 r-盘的
   **对称差**；等半径 ⇒ 根轴 = 弦线 `AC` ⇒ 落在 q-半平面的点若在 `B(q,r)` 内则必在 `B(q',r)` 内，于是
   单盘松弛的**超额部分恰是半 lens** `L ⊆ B(q',r)`。因此只要局域化球与**远端盘** `B(q',r)` 不相交，
   `ρ(A,b,C) ≤ r` 在该球上**精确等价**于 `b ∈ B(q,r)`——一个圆盘（cutting plane），不是二次 stress。
3. **候选处该圆盘精确活跃（tight）**（§5）：`|q_i-hB|-r = -3.9e-16 / -5.5e-16`（`ρ(hA,hB,c_0/4) = r` 到 1e-17）；
   局域化球与远端盘的精确性余量 = `+0.15416 > 0`。即：两 faces 的 exact crescent 约束在候选处被
   **两个固定圆盘**（中心为环数据函数）精确替代，且都 active。二次 stress 的缺失因此不是障碍：
   该结构把 quartic/lens 非凸性**按定向精确线性化**掉了。

---

## §1 exact normal form：中央 circumradius 约束在 hubs+ring endpoints 上的多项式

对象：hubs `a,b`，环端点 `c`；`d=|a-b|`，`L_c := det(b-a, c-a)`，`φ_c := ⟨c-a, c-b⟩ = |c-m|^2 - d^2/4`，
`m=(a+b)/2`，`k^2 = r^2 - d^2/4`，`w_c = ⟨c-m,n⟩`（`n ⊥ (b-a)` 单位），`s_c=|c-m|^2`。

**（1.1）多项式形式。** 对非退化三角形
```
F_c(a,b) := 4 r^2 det(b-a,c-a)^2 - |a-b|^2 |c-a|^2 |c-b|^2 ,      F_c >= 0  <=>  rho(a,b,c) <= r .
```
**（1.2）等价正规形**（脚本残差 = 0，符号验证）：
```
F_c = 4 k^2 L_c^2 - d^2 φ_c^2 = d^2 [ 4 k^2 w_c^2 - (s_c - d^2/4)^2 ] = - d^2 g_+(c) g_-(c) ,
   g_±(c) = |c - (m ± k n)|^2 - r^2 .
```
最后一条即 `lead` Lemma 2 / 本件 Lemma 1 的乘积恒等式：`ρ ≤ r ⟺ g_+ g_- ≤ 0 ⟺ c ∈ (B(p_+,r) ∪ B(p_-,r)) \ int(B(p_+,r) ∩ B(p_-,r))`
（"closed symmetric difference"）。**角度形**（用 `ρ = |ab| / (2 sin∠acb)`）：
`ρ(a,b,c) ≤ r ⟺ ∠acb ∈ [α, π-α]`，`α = arcsin(d/2r)`——crescent 的两个边界弧就是"过 A、C 的半径 r 圆"。
对称性说明：`ρ` 三顶点对称，故上式把 `a`、`b`、`c` 任一换成被固定点都同样成立（§3 用到 `A,C` 固定、`b` 变动）。

**（1.3）bidegree 表**（把 `F_c` 看成 (a,b) 的二元多项式；脚本 `S3a`）：
```
support = {(4,0),(4,1),(4,2), (3,0),(3,1),(3,2),(3,3), (2,0)..(2,4), (1,1)..(1,4), (0,2),(0,3),(0,4)}
```
即**每个 hub 变量上至多 4 次**、总次数 6（`d^2 |c-a|^2 |c-b|^2` 项），且
```
deg_a=4 分量 = -|a|^4 |b-c|^2 ,        deg_b=4 分量 = -|b|^4 |a-c|^2 .        (S3b/S3c)
```
（Lagrange 恒等式：`det(a,b-c)^2 + (a·(b-c))^2 = |a|^2|b-c|^2`，来自 `4r^2L^2` 与 `-d^2φ^2` 的 deg-4 部分之和。）
**这就是"quartic hub coupling"的精确定位**：它既在 (4,·)、(·,4) 里（含 `|b-c|^2` 的跨 hub 耦合），也在 (2,2) 混合项里。

## §2 正加权是否消去 quartic hub coupling：**不能**（符号判定）

设 `W := λ0 F_{c0} + λ4 F_{c4}`（`λ0,λ4 ∈ R`），`c0 ≠ c4`。由 §1.3 线性性：
```
deg_a=4 分量 (W) = -|a|^4 ( λ0 |b-c0|^2 + λ4 |b-c4|^2 ) .                    (S4b)
```
`|b-c_i|^2 = |b|^2 - 2 b·c_i + |c_i|^2`，故"该分量恒消失"是**关于 b 的三个恒等式**：
`λ0+λ4=0`、`λ0 c0 + λ4 c4 = 0`（向量）、`λ0|c0|^2 + λ4|c4|^2 = 0`；由第一条 `λ4=-λ0`，第二条给 `λ0(c0-c4)=0`
⇒ `λ0=λ4=0`。脚本 `S4d` 直接解线性系统：**唯一解 `{l0:0, l4:0}`**。b 侧同理（`S4c`）。
混合 (2,2) 分量：脚本 `S5` 在有理数据点求该线性系统的秩 = **2**（且在符号系统上求解同样只有零解）⇒ 连混合耦合也不能消。

**推论（本件对"quadratic stress"问题的正式回答）**
> 不存在任何乘子（正、负、甚至允许与二次约束混用）把两个中央约束的 quartic hub coupling 消成一个二次式：
> 二次约束（`|h| ≤ 1-r`、C879 链盘 `|h-p_i| ≤ r`、variance 局域化盘 `|h-b| ≤ ε`）**没有 deg-4 分量**，
> 而 deg-4 分量本身已由上述恒等式锁定为"两项同号相加"。因此按字面意义的 `正加权 → quadratic stress`
> **unresolved（器械不存在）**。若要二次对象，只能（i）允许 quartic 乘子（本件未探索），或（ii）改变表示——
> 这正是 §3。

## §3 替代结构：crescent 的定向精确圆盘化（保 orientation 的 convex 对象）

固定两个不同点 `A, C` 与 `0 < |AC| < 2r`；令 `q, q'` 为满足 `|q-A|=|q-C|=r` 的两个圆心（关于直线 `AC` 镜像）。

**引理 1（对称差）** 对非退化 `(A,b,C)`：`ρ(A,b,C) ≤ r ⟺ b ∈ (B(q,r) ∪ B(q',r)) \ int(B(q,r) ∩ B(q',r))`。
证明：§1.2 的乘积恒等式（`A,C,b` 三顶点对称）给出 `ρ ≤ r ⟺ g_q(b) g_{q'}(b) ≤ 0`，即 `b ∉ (两个都在外) ∪ (两个都在内)`。∎

**引理 2（等半径 ⇒ 根轴 = 弦线；**方向已修正**：原版写反，lead 已据此 retract C894）**
两盘半径相等，根轴 = `qq'` 的垂直平分线；而 `A,C ∈ ∂B(q,r) ∩ ∂B(q',r)`
（两者到 `q,q'` 距离均为 `r`）⇒ 根轴 = 直线 `AC`。于是 q-侧半平面 `H_q` 上**逐点**有 `g_q ≤ g_{q'}`，故
`B(q',r) ∩ H_q ⊆ B(q,r)`（**远端半盘落在近端盘内**；这才是正确方向）。∎
⚠ 反向蕴含**不成立**：`g_q ≤ 0` 且在 q-侧 ⇏ `g_{q'} ≤ 0`。反例（lead 给出，已写入 `central_crescent_stress.py` 的 [L2]）：
`r=1, A=(-3/5,0), C=(3/5,0), q=(0,4/5), q'=(0,-4/5), p=q`：`g_q=-1` 但 `g_{q'}=39/25>0`。

**推论（单盘化的超额恰好是半 lens；此处两条都是对的）** 记 `L := B(q,r) ∩ B(q',r) ∩ H_q`。由引理 1 + 引理 2：
```
(1) crescent ∩ H_q  ⊆  B(q,r) ∩ H_q ;                       % crescent ⊆ B_q ∪ B_{q'}
(2) (B(q,r) ∩ H_q) \ {crescent}  =  B(q,r) ∩ int(B(q',r)) ∩ H_q  ⊆  B(q',r) .
```
即单盘对象相对 crescent 的**超额恰好是半 lens `L`**，而 `L ⊆ B(q',r)`（远端盘）。再补一条几何定位：由平行四边形律，
`b ∈ B(q,r) ∩ B(q',r)` ⇒ `|b - mid(AC)| ≤ |AC|/2`（lens 落在弦 `AC` 的 Thales 盘内），故超额区是**紧致局部化**的。
**于是"避开远端盘"就足够**（这正是 §5/`CENTRAL-HELLY-SCREEN.md` 检验的那一条）。

**注（`H_q` 条件可去掉：更干净的等价形式，仅需"避开远端盘"）** 设 `R` 为任意集合且 `R ∩ B(q',r) = ∅`。由引理 1，
`{crescent} = (B(q,r) ∪ B(q',r)) \ int(B(q,r) ∩ B(q',r))`；`R` 上第二项为空，且 `int(lens) ⊆ int(B(q',r)) ⊆ B(q',r)`
也在 `R` 上为空 ⇒ `{crescent} ∩ R = B(q,r) ∩ R`。**故只需局域化球与远端盘不相交**（本件 §5 检验的正是这一条，
且 C894 里多写的 `H_q` 假设是冗余的，加着也无害）。

**这就是"保留 orientation 的 convex 外松弛 / cutting plane"**：定向（落在哪个半平面 = 哪支圆盘）一旦由局域化固定，
约束就退化为**一个固定圆盘**；"exact candidate 处 tight"因此是可检验的两条：圆盘活跃 + 超额区被局域化球排除。

## §4 局域 hub localization 接口（C879 + variance identity；全部 ring-only）

链 pins `p_i` = 相邻环 r-圆的**内部**交点（`R20-CHAIN-HUB-CONVEXIFICATION` 的 `p_in`）。q0 图（`lead/q0_graphs.json[2]`）：
hubs `9,10`；hub 9 的 fan = `[9,0,1],[9,1,2],[9,2,3],[9,3,4]` ⇒ 链 pins `{0,1,2,3}`；
hub 10 的 fan = `[10,4,5]..[10,8,0]` ⇒ 链 pins `{4,5,6,7,8}`；中央 faces = `[9,10,0],[9,10,4]`。
对任意凸权 `λ`（`Σλ=1, λ≥0`）：`Σλ_i|h-p_i|^2 = V + |h-b|^2`，`V = Σ_{i<j}λ_iλ_j|p_i-p_j|^2` ⇒
**`|h-b| ≤ ε := sqrt(r^2 - V)` 是任何合法 hub 的必满足条件**（C879 链盘的前提），且 `V ≤ r^2` 本身是环的必要条件。

| hub | 权 | `ε` | 备注 |
|---|---|---|---|
| 10 (A) | pins `{4,6,8}`：(.**459978**, **.080045**, **.459978**)（重心权，全正） | `V_A - r^2 = -1.9e-16` ⇒ `ε_A = 1.4e-8` | 三 pin 同时 `|hA-p_i| = r`（到 2e-16）⇒ 精确候选处 `ε_A = 0`（**条件性**，见 §6） |
| 9 (B) | pins `{0,3}`：**(1/2, 1/2)**（有理！） | `ε_B = 0.0330620707 = sqrt(r^2 - \|p_0p_3\|^2/4)` | `b_B = (p_0+p_3)/2`，纯环数据；**无**对称/饱和假设 |

关键读数：hub B **不在**其链 pins 的凸包内（四个三点子集的重心权都有负分量；pins 绕 hB 的角度跨 190°>180°），
所以 hub B **没有** `ε=0` 的凸权局域化（与"四切触"是两件事——四切触只是 `|hB-p_j| = r ∀j∈{0,1,2,3}`，
它给出 `V=r^2` **仅对含负分量的重心权**，不是合法局域化）。合法的 `ε_B = 0.03306` 来自仅用两个链 pin 的有理权。

## §5 候选处的读数（60 位，诊断；输入为 exact rational 圆心 + 保存的 r）

```
中央 faces:  rho(hA,hB,c_0) - r* = -1.03e-18 ,   rho(hA,hB,c_4) - r* = -3.95e-17      (r* = C249 上界对象)
链 pin 距离 - r:  hubA {4,6,8} = -2.8e-16, -2.4e-16, -2.3e-16 ；{5,7} = -2.84e-3（slack）
                 hubB {0,1,2,3} = -2.9e-16, -5.0e-16, -4.1e-16, -2.6e-16（四个切触）
固定圆盘（过 (hA, c_i) 的半径 r 圆，取 hB 所在支）:
   |q_i - hB| - r  = -3.88e-16 (i=0) ,  -5.50e-16 (i=4)      →  两盘在候选处都 active（tight）
   远端盘余量 |q'_i - hB| - r = +0.163048                     →  两支分离，定向不病态
   b_B 到远端盘余量 - eps_B  = +0.154159 > 0                  →  局域化球 B(b_B, eps_B) 与超额区不相交
                                                              ⇒  §3 推论在候选处**精确成立**（无额外损失）
|AC| = 0.7361319697 (两 face 同值)；hB 到弦线距离 0.3985 > Thales 半径 0.3681
hubA 局域化驱动圆盘中心的位移（|dA| = eps_A = 1.4e-8）：|dq| ≈ 2.39e-8
```
解释：(i) 两 faces 的 circumradius 恰为 `r*`（到 1e-17）⇒ crescent 约束 active；
(ii) §3 的单盘化在该处**精确等价**（超额区被局域化球排除，余量 0.154 ≫ 0）；
(iii) 于是两 faces 等价于 hub B 必须同时落在两个**由环数据确定的固定圆盘**内（圆盘中心对 hA 的依赖只有 `~2.4e-8` 量级，
即 hub A 的 pinning 精度），与 C879 链盘族 `K_B = B(0,1-r) ∩ ∩_{j∈{0,1,2,3}} B(p_j,r)` 一起构成**凸**可行性系统。

## §6 级别、边界与未决（诚实清单）

**已证（解析 + 符号验证）**
1. §1.2 三条恒等式（`F_c = 4k^2L^2 - d^2φ^2 = -d^2 g_+g_-`）与角度形：脚本残差 = 0（精确符号）。
2. §2 不可消定理：deg-4 分量 = `-|a|^4(λ0|b-c0|^2+λ4|b-c4|^2)`（b 侧对称），唯一零解 `λ=0`；
   混合 (2,2) 秩 2。证明在正文（三行恒等式 + 秩）。**这否掉的是"正加权→quadratic stress"这一器械，不是某个数学命题。**
3. §3 引理 1/2 + 推论（对称差表示、等半径根轴保号、超额 ⊆ 远端盘、lens ⊆ Thales 盘）。
4. §4 局域化不等式本身（variance 恒等式 + 非负权 + C879 链盘⇒`|h-b| ≤ sqrt(r^2-V)`）：解析。

**numeric only（60 位诊断，非证书）**：§5 全部读数（r 用保存浮点 / C249 有理对象；pins 含 `sqrt`）。
特别地"超额区余量 +0.154 > eps_B"与"两固定盘 active 到 4e-16"都是**数值**（→ C896）。
**unresolved（明确未决）**
* (U1) **该凸化（两固定盘 + K_B + K_A）作为 r 的函数的可行性阈值是否恰为 `r*`**（即它是否 sharp、能否闭合 q0(6,7)）。
  这是本结构给出的**最小可判定义务**：固定环数据，对
  `{h_B ∈ B(q_0(b_A), r + L eps_A) ∩ B(q_4(b_A), r + L eps_A) ∩ K_B }`（凸，2 维）做精确阈值/区间证书，
  与真局部阈值比较。本件未做该阈值计算（避免制造新的一轮数值扫描）。
* (U2) **`ε_A = 0`（hub A 三切触）不得预设**：§4 表里 `ε_A = 1.4e-8` 只是保存对象（1e-17 舍入）的读数；
  精确最优处是否 `V_A = r^2` 属饱和型假设，必须由全局论证导出（或改用 `ε_A > 0` 的加厚圆盘版本，
  代价是圆盘半径放大 `~2.4e-8`）。**本件不把它当输入。**
* (U3) §3 推论对活动环（ring 自由）的**全域**版本：本件只给了"给定环数据 + 局域化"的精确化；
  ring 自由时 `q_i, b_B, eps_B, K_B` 都随环变化，"余量 +0.154" 需要区间化才能成为全域证书。
* (U4) 本件**未**探索带 quartic 乘子（例如把 `F_{c_i}` 自身或其组合作为乘子乘上局部化二次约束）的对偶，
  也未探索 SOS/Positivstellensatz 形式；§2 只否证了"线性加权消 quartic"。

## §7 与在册结论的关系

* **支持/复用**：`lead/R20-CENTRAL-SPAN-NECESSITY.md` 的乘积恒等式与 `D ≤ 2r+2k`（本件 §1.2 给出同一恒等式的符号验证 + 角度形）；
  `lead/R20-CHAIN-HUB-CONVEXIFICATION.md`（链盘凸集，用作 `K_A,K_B`）；`lead/R20-CHAIN-VARIANCE-LOCALIZATION.md`（variance 局域化，
  本件把它用于 `(1/2,1/2)` 的**两个链 pin** 上，得到 `ε_B = 0.03306`——比在册读数 `0.1714171`（均匀 4 权）小 5 倍，且权重是精确有理数）。
  `lead/HUB-DISTANCE-QUADRATIC-DUAL.md`(C890)：本件 §2 说明该二次对偶族**不可能**从两个中央约束的加权中获得更强形式（quartic 不可消），
  与该件"coarse filter、非 sharp"的自述一致。
* **不沿用**：span 过滤本身（候选 slack +3.63e-3，不 sharp）；不做远端盒排除。
* **与在册"中央两 faces 未处理"的关系（修正性）**：`lead/R20-CENTRAL-SPAN-NECESSITY.md` 结尾写
  "triangle orientation and two precise crescents remain"。本件把这"两个 precise crescents"在
  **定向 + 局域化**下精确化为**两个固定圆盘**，并给出候选处的活跃性与余量读数 ⇒ 该条未决项由
  "两个 quartic crescent"收窄为"一个 2 维凸可行性阈值（U1）+ 一个饱和度问题（U2）"。

## §8 复现

```powershell
py -3 -B -X utf8 research-2026/team-current/r20-alternative/central_crescent_stress.py   # 写出 central_crescent_stress.json
```
[S] 段：sympy 恒等式/分量/解（`S2a_identity_F_equals_minus_d2_gp_gm_residual = 0`，
`S4d_solutions_of_deg_a4_vanishing = [{l0: 0, l4: 0}]`，`S5c_rank_of_mixed_22_system_at_rational_data = 2`）；
[C] 段：60 位读数（`hubA_eps(barycentric) = 1.38e-8`，`hubB_best_convex_localisation.eps = 0.0330620707`，
`dist(b_B, distal disk) - eps_B (exactness margin) = 0.154159`，`|q-hB|-r = -3.88e-16/-5.50e-16`）。
