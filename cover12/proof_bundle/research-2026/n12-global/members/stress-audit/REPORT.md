# stress-audit — 独立复核 lead 的 conditional sharp-stress 接口

scope: 仅本 36 边网络（9 anchors + 9 ring sites + 3 hubs + 6 witnesses）的 conditional theorem 及其支撑装置；
不是 n12 全局定理，不含 k10/k11、其它网络、拓扑接口（nine-topology）与 13-face coverage（candidate）。
作者目录：`research-2026/n12-global/members/stress-audit/`（未改动 shared/lead/claims/n11）。
日期：2026-09-26。所有证据在 `logs/`、`evidence/`；claims 见 C971–C977。

## 0. 结论一句话

**未发现 lead 侧承重装置的具体数学错误。** 三条主义务（七轨道权重的自由节点/锚点平衡与 T、cos 界+M 的 mixed-direction 证书、graph/分类/归一化一致性）
均以**独立表示与独立实现**复核通过；新扩展（root-T Banach 证书、full-simplex 网络证书族）亦独立复算通过。
我自己在审计中发现并修正了 3 个**我方代码**错误（见 §4），它们是本轮唯一的错误来源。

**最终口径（按 lead 的澄清）**：根存在（Krawczyk 证书，我已独立复算）+ 图给定 ⇒ 本报告给出的是**固定图的无条件 lower bound**
（作为关于 9 anchor 角向向量的解析命题：全域 gap 单纯形上 E(θ)>r²、V_G(θ)>r，其中 Krawczyk/区间引用都是无条件有限算术证书）。
**尚缺的不是这个 lower bound，而是 cover→graph 类接口（9 个边界切换弧如何产生该图与 gap∈(0,L] 域）以及 upper coverage / 全局最优。**

## 1. 义务一：cos 界与 Hessian 主导项（C973, C972, C977）

- 合法性：9 anchor 相邻角差 Δ_i∈(0,L], Σ=2π，L=2asinU，U=0.361102963744508672616920293904（精确有理）。
- **4L<π 的精确有理链**：4L<π ⟺ U<sin(π/8) ⟺ √2 < 2−4U²。实测 2−4U²=1.4784185983>0 且 (2−4U²)²−2=0.1857215518>0（全部 Fraction 精确）。
- **9L>2π**：U=0.36110296374450867 > 22/63=0.3492063492 > π/9 > sin(π/9)（π<22/7），故宽度单形非空且 D=9L−2π>0。
- **cos(dL)=T_d(1−2U²) 精确有理**：d=1..4 → 0.739209299149864, 0.092860775899267, −0.601922201007845, −0.982753752598772；
  与 `evidence/stress-interval.json` 的 `exact_cosine_constants` **逐位相同**（Chebyshev 递推 `2c·x_{d−1}−x_{d−2}`）。
- 于是对 label 距 d≤4：较短弧长 s≤dL<π，且 cos(θ_i−θ_j)=cos(s)≥cos(dL)（cos 在 [0,π] 单调下降）。
  ⇒ 对 q_ij≥0，zᵀH(θ)z = Σ 2q_ij cos(θ_i−θ_j)(z_i−z_j)² ≥ Σ 2q_ij cos(d_ij L)(z_i−z_j)² = zᵀMz，**全域成立**。
- **mixed direction 结论**：M·1=0 恒等（构造即行和为零）。我不用 leading minor 而是用 `{e_0−e_k}_{k=1..8}`（张成 1⊥）的 Gram 矩阵：
  8 个 LDL pivot 下界 ≥1.21608e−02（±1e−30 box）；同 box 上 lead 式 leading 8×8 主次式下界 ≥1.14301e−02。
  二者各自独立给出：对 interval family 的每个成员 M 与每个 z∈1⊥, z≠0 有 zᵀMz>0；再配 M·1=0，得对每个 z≠0 且 z_0=0 有 zᵀMz>0
  （若 z=c·1+w, w⊥1 则 zᵀMz=wᵀMw>0；若 w=0 则 z_0=0 ⟹ z=0）。**这正是“固定旋转的 anchor 切空间”，覆盖全部 mixed 方向**，无按块/按对角推断。
- box 中心的**精确有理**（无区间）计算复现了记录谱：0, 2.366154692e−03(×2), 3.445751907e−02(×2), 6.032405391e−02, 7.061441684e−02, 8.333489422e−02(×2)。
- 内点性/guard 在 box 上认证：0<2β<L ⟺ w²(1−U²)<3U²b²；0<2α<L ⟺ A²<12U²S²(A>0)；b>w(β<π/6)、r<U、
  S−b<0、2a−t+r>0、1−t²−r²>0、2t−2r−a>0、全权重>0。

## 2. 义务二：装置同一性与独立区间核（C975, C972）

- **对象同一**：按 `k%3==1→z`、`i%3==2→x`、其余→y（anchor-site 边）与 `face<3: hub→q/ring→p`、`HHR: hub→u/ring→j`（witness 边）重建后，
  36 个归一化权重与 `candidate-stress-probe.json` 零空间压力**最大相对偏差 3.207e−15**（float LU 噪声），Σ=1。
- lead 记录的 18 个 Dirichlet pivot、7 个权重区间、normalization=85.65756301037007、4 个余弦常数、min Schur 电导 6.684002e−05
  与我的自写核**逐位一致（相对偏差 0）**。`root-t-stress-certificate.json` 同样一致。
- **独立实现差异**（非 replay）：自写 exact-Fraction 端点区间、外向十进网格舍入（10^−30/45/60 三档）、
  消元顺序 sites→hubs→witnesses（lead 为 witnesses→sites→hubs）、反转顺序亦通过、mixed 证书用 1⊥ 的 Gram 基而非 leading minor。
- 与 lead 实现的差异：lead 的 `I` 原语与我的一样做外向网格舍入，但网格/顺序不同；我实测三档网格 10^−30/45/60 与反转消元顺序下结论不变，说明符号结论不依赖具体舍入路径。
- **primitive 覆盖性论证核对**：区间 `+ − × ÷`（除法带严格符号断言）、无主元置换消元、Schur、LDL 都是包含性单调的，
  故 pivot 区间 lo>0 对 interval family 的每个成员的前导主次式成立；`q_ij` 区间 lo≥0 对每个成员的非负性成立；
  M 的每个 entry 是 q 的单调函数，故区间 M ⊇ {M(q)}；Gram/LDL 的线性/多项式组合同样被包含 ⇒ 证书覆盖**全部** mixed 方向而非抽样。

## 3. 义务三：七轨道权重、T 与 F,G,H,T 分支（C971, C979）

- 18 个自由节点平衡逐条归约到**其真正前提**（sympy 精确范式 + dps=40 数值双查）：
  - HRR witness `2p(b−d)+q(a−d)≡0`、hub `qr+u(t−r−2a)≡0`、HHR witness `au−2u(t−r)+jr≡0`：纯定义恒等；
  - low site `2z(cosα−t)−jr≡0` ⟺ G（cosα=(1+t²−r²)/(2t)）；
  - high site 切向 `(y−x−d)(S−b)/b + H/12 ≡0`、径向 `(x+y)(b−S)+db−S + bH/12 ≡0` ⟺ H（且 d=2b−1）。
- 9 个 anchor 的切向残差：轨道型 {18,21,24} → −(2ywS−ztA)/(2√3S)，{19,22,25} → +(2ywS−ztA)/(2√3S)，{20,23,26} → 0（hub 轴反射抵消，两权重同为 x）。
  ⇒ 角向平衡 ⟺ yv=z t sinα。
- **T 与角向标量的精确关系**：T·K = 2ywS−ztA，K=−2(1−b)/((S−b)(2a−t+r)(1−t²−r²))；
  故（除子非零）T=0 ⟺ yv=z t sinα。数值：记录根处 y·v−z·t·sinα≈1.5e−60。
- **分支结构（新增结构事实；线性性只是数值观察）**：T ∉ ⟨F,G,H⟩（grevlex 归约余式非零，精确）；
  沿 F=G=H 分支的有限数值扫描给出 **numeric slope observation**：T(s)/s≈3.8348 在 s≲1e−8 稳定，s≥1e−6 起出现高阶偏差
  （1e−4 时 3.83568，1e−3 时 3.84350），**因此这不是精确线性**，只是零点位置的一阶估计（≈−T(0)/c₁，距记录根 ~7e−63）；
  远点 s=0.5/1.0 时 T=0.3014/0.3934≠0。**“T 在 ±1e−30 box 内有唯一零点”的承重依据是 lead 的 Krawczyk 证书本身，不是这个斜率。**
- **lead 新 root-T 证书独立复核**：用我自己的区间核 + 其 Y：‖I−YJ(box)‖∞≤4.087416e−28<1（lead 记 4.0874e−28），Krawczyk 像严格含于 box。
  ⇒ {F=G=H=T=0} 在该 box 内存在唯一根；同 box 的 stress 不等式通过（min Dirichlet pivot 2.9077e−02、min q 6.6840e−05、min M 次式 pivot 1.1430e−02）。
  **这把“conditional 假设里根是否存在”补上了**（lead 的 `evidence/root-t-certificate.json`、`root-t-stress-certificate.json` 已被独立确认）。

## 4. 错误审计（本轮唯一发现的错误都在我的审计代码里）

1. **我方消元双扣**：我第一版消元对每个无序对更新两次（内层扫全 remain 而非上三角），导致 pivot 变负。
   lead 的 `stress_interval.py` / `network_interval_certificate.py` 用 `for jx in range(ix,len(remain))`，**正确**。
   影响：仅我方脚本；修正后我方 pivot 与 lead 记录逐位一致（step5/6）。
2. **我方把 D 写成 9L−π**（应为 9L−2π），导致 E/linear/norm 全错；修正后与 lead 记录逐位一致（step7 输出）。
3. **我方 max‖d‖² 多乘一个 D²**（`D*D*Σ(D·(…))²` 应为 `Σ(D·(…))²`）；修正后 max_norm2=0.64078583572567687886 与 lead 一致。
   （附：step7 早期“L 不在括号内/E 不匹配”的两次报警均系我方 double 精度比较与上述错误，非 lead 缺陷。）

## 5. 扩展复核：13-face [2,3,4] 网络的 Taylor+κ 证书（C976）

- 独立重建 57 边/25 自由节点：原序与反序 Dirichlet 消元全正（min pivot 2.6326e−06 / 3.0000e−06），q≥0（min 8.1378e−05），M·1=0，
  M+κI(κ=1/50) 全 9×9 LDL 正（min pivot 3.7700e−03）。
- **M 本身有两个负特征值**（λmin=−1.9383e−02）：κ 位移**必要**；位移后 λmin=6.1715e−04>0，**够用**。lead 的“M 允许 negative + 9×9 LDL”处理正确。
- 数值逐位复现：E(θ_ref)=0.1370958166906964609461811、linear_min=−4.1207750207823423449e−09、
  max‖d‖²=0.64078583572567687886、lower=0.1306879542126646713752797、margin=lower−U²=**2.926037875967e−04>0**。
- 逻辑核对：Taylor 余项 ≥−(κ/2)‖d‖²（H⪰M⪰−κI）；线性项在单形顶点取 min；凸的 ‖d‖² 在顶点取 max；
  sin/cos 用 **Lagrange 余项 + 导数界**（sin 截断到 79 次 ⇒ 余项 ≤|x|⁸⁰/80!；cos 截断到 78 次 ⇒ ≤|x|⁷⁹/79!，
  因输入是区间、不是交错级数场景，故不能用交错级数估计）——这是对任意 x 都成立的 generic bound；
  我以 dps=80 逐点的“enclosure 含真值、宽 4.2e−44”只是**一致性检查**，不是该界本身的证明依据；
  Machin π 与 L 的 sin 夹逼（sin(lo/2)<U<sin(hi/2)）我同样独立复算成立。
- scope 提醒：该证书排除的是**该网络**在 U 以下的可行性；它是否覆盖真实覆盖族取决于拓扑接口（nine-topology），且它**不**涉及 sharp r≈U−2.9e−17 的那个网络。

### 5b. full-simplex 网络证书族（60 份 `network-certified-*.json`，C981）

- 我用自己的重建+消元+特征值流程扫过 `evidence/network-certified-*.json` 全部 **60** 份（117/126/135/144/225/234、M1、M2-*、P2-*、P3-*、P4-*、T2-*、T3-*）。
  每一份都通过：57（或 45/51）边的自由节点 Dirichlet pivot 在**原顺序与反转顺序**均为正；q_ij≥0；M·1=0（精确 0）；
  M+κI 的 9×9 精确 LDL 全正；且 **λ_min(M)+κ>0**（κ 是每网络各自的，0.006–0.05；例如 135 的 λ_min(M)=−2.3644e−2 需 κ≥0.0236，其 JSON 用 0.05）。
  E(θ_ref)、linear_min、max‖d‖²、lower 与各自记录逐位一致（≤3.1e−29，受我用 mpmath 的 L/D 精度限制）。
- 最小 margin（lower−U²）= **2.926037875967e−04**，出现在 234，与 lead 的“最小 margin .0002926”一致；全部 margin>0。
- 注意计数口径：我扫的是 `evidence/network-certified-*.json` 全部 **60** 个文件（lead 口径的“55”可能是按不同重复/拓扑去重的计数；数量差异不影响每条证书各自的复核结论）。
  `evidence/network-certified-333.json` **不存在**（333 只有 `network-minimax-333.json` 提案），所以“333 拓扑”本身没有 full-simplex 证书。

### 5c. 桥接对象同一性（`lead/ROOT-AND-NETWORK-BRIDGE.md`，C981）

- 333 图的 13 face = 9 boundary(i,i+1,label_i; label=9,9,9,10,10,10,11,11,11) + 3 block(3,9,10),(6,10,11),(0,11,9) + 1 central(9,10,11)，与 `network-minimax-333.json` 的 faces 逐项一致。
- 以 ring 重标号 σ(i)=i−2 (mod 9)、hubs 固定后：333 的 faces 中恰有 6 个映到 stress_interval 的 6 个 active faces
  （333 侧：(1,2,9),(4,5,10),(7,8,11) 三个 HRR 与 (3,9,10),(6,10,11),(0,11,9) 三个 HHR），
  被删的 7 个 = 其余 6 个 boundary face + central HHH(9,10,11)；两者 anchor-site 边规则同为 (18+i,i),(18+i,(i+1)%9)。
  ⇒ 桥接的身份断言（“删除 7 face 留 6 active 正好是 stress_interval 图”）成立（组合层面）。
- 该 6-face 子图是 13-face 图的**子网络**，故 V_6face ≤ V_13face；“max edge>U” 的 full-simplex 证书只对 13-face 网络成立，
  不能与 sharp 结论（V_6face≈r<U）混用——两者对象不同，这是我们此前人工核对过的接口要点。

## 6. 与 lead 文档的一致性 / 未覆盖项

- 与 `lead/EXACT-CANDIDATE-STRESS.md`、`GLOBAL-STRESS-CONVEXITY.md`、`ANCHOR-NETWORK-INTERFACE.md` 的每个承重步骤一致（含 T 的替换性质、
  “不是断言 J=T”、M1=0+次式、以及 `D3-EXACT-CHART.md` 的 F,G,H 几何）。
- 未覆盖（不在我 scope）：cover→graph 类接口（9 个边界切换弧 ⇒ 该图与 gap∈(0,L] 域）、13-face/upper coverage、k10/k11、其它 block 网络的分类、r_D(12) 的全局判定。
- 严格性口径：**固定图（本 36 边网络）的无条件 lower bound 已到位**（Krawczyk 根存在 + 区间矩阵不等式 + 精确恒等式，全部为无条件有限证书）；
  条件性只存在于“真实 12 盘覆盖 ⇒ 该图可行放置”这一步。因此本报告不构成 n12 全局最优定理，也不改变 STATUS 的 gap 列表。

## 7. 复现

```
$env:PYTHONIOENCODING='utf-8'
py -3 -B research-2026/n12-global/members/stress-audit/py/step1_chart_T.py     # T 在记录根 ~2.7e-66
py -3 -B research-2026/n12-global/members/stress-audit/py/step2_geometry.py    # 几何/36 边/18 节点/9 锚点残差 ~1e-60
py -3 -B research-2026/n12-global/members/stress-audit/py/step3c_symbolic_nf.py # 精确恒等式（sympy 范式 + 两点复核）
py -3 -B research-2026/n12-global/members/stress-audit/py/step4_Tbranch.py     # T∉<F,G,H>；slope observation（非精确线性），零点一阶估计 ~7e-63
py -3 -B research-2026/n12-global/members/stress-audit/py/step5_kernel.py      # 我方区间核：权重/pivot/q/Gram(mixed)
py -3 -B research-2026/n12-global/members/stress-audit/py/step6_compare.py     # 与 probe / stress-interval.json 的一致性
py -3 -B research-2026/n12-global/members/stress-audit/py/step7_check234.py    # 234 网络 Taylor+κ 复核
py -3 -B research-2026/n12-global/members/stress-audit/py/step8_Lcheck.py      # L=2asinU 括号有效性
py -3 -B research-2026/n12-global/members/stress-audit/py/step9_roott_check.py # 我自己的 Krawczyk 复核
py -3 -B research-2026/n12-global/members/stress-audit/py/step10_domain.py     # 域/内点性/guard
py -3 -B research-2026/n12-global/members/stress-audit/py/step13_network_sweep.py # 60 份 full-simplex 证书族
py -3 -B research-2026/n12-global/members/stress-audit/py/step14_bridge.py       # 333↔6-face 桥接身份
```
