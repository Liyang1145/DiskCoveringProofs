# 数值校准（**不是证明**；仅作反证式检查与器械校准）

按 Lead 口径：数值只校准、不扩量；证明见 [`PROOF-finite-reduction.md`](PROOF-finite-reduction.md)。

## 0 三个独立器械与它们的严格性等级

| 器械 | 定义 | 严格性 |
|---|---|---|
| `R_cand` | 取候选集 $K(C)$ 中点（$K_d$ 施加 $\|x\|\le1$ 过滤）的最大 $f_C$ | **下界**（候选点都在 $D$ 内，$R_{\rm cand}\le R(C)$ 恒真；浮点误差 $O(10^{-16})$） |
| `R_ref` | 密格点 $\max f_C$ + 从格点前 24 名出发的投影 pattern search（步长收缩到 $10^{-14}$） | **下界**（格点值 $\le R$；优化只提升读数）——器械独立于候选列表 |
| `sandwich` | 格点 $2001^2$ + $2\times10^6$ 均匀随机点；给出上界 $\max_{\rm grid}f+\frac{h\sqrt2}{2}+10^{-12}$（$h=0.002$，$f_C$ 是 $1$-Lipschitz，格点覆盖半径 $h\sqrt2/2$） | 上界是**sound**的（浮点舍入除外，宽度 $\approx7.07\times10^{-4}$） |

**判读规则**：
- $\max_{\text{格点}}f_C-R_{\rm cand}>0$（超过浮点噪声）$\Rightarrow$ **硬反例**（不依赖任何优化器，因为格点值是真 $R$ 的下界）。
- `R_ref` $<R_{\rm cand}$ 只说明**参考器械没找到峰**（器械失败），不说明定理有问题。
- "无正违例"只是校准证据，**不能**替代证明（浮点/采样不能确证连续统）。

## 1 battery：223 例（`evidence/battery.json`，SHA256 前缀 `5C7BD5FAE2371883`）

配置族：全零/单中心/重合中心、环形（正 $m$ 边形 $m=3..12$，$\rho\in\{0.2..1.0\}$，含/不含原点）、重复（6 点各双份）、共线（x 轴 12 点、y 轴 6 点含原点、共线三点+随机）、外心落界三元组、近平行切（$\varepsilon=10^{-2}..10^{-9}$）、随机（圆盘/圆周/混合，$n=1..12$）、近退化扰动（$10^{-3}$、$10^{-6}$）、C182 只读构型。

| 读数 | 值 |
|---|---|
| 例数 | 223 |
| $\max(R_{\rm ref}-R_{\rm cand})$（正方向） | $4.44\times10^{-16}$（例 `single-0.99-diag`，纯浮点噪声） |
| 正违例数（阈值 $10^{-9}$ / $10^{-7}$） | $0$ / $0$ |
| $\min(R_{\rm ref}-R_{\rm cand})$（负方向=参考器械失败） | $-2.49\times10^{-7}$（6 例近平移正三角形，峰极平坦，器械未收敛） |
| $\max(\text{格点值}-R_{\rm cand})$ | $\mathbf{0.0}$（$223$ 例中**从未**出现"格点值 $>R_{\rm cand}$"） |
| 未过滤 (d) 读数 $>R_{\rm cand}$ 的例数 | $55$（例：`collinear-3+random` 未过滤 $76.441$，$R_{\rm cand}=1.000$） |

$55$ 例直接支持 PROOF §3.5：$|x|\le1$ 过滤是**等价性**所必需（不加过滤则判据只剩充分方向）。

## 2 sandwich：28 例关键退化（`evidence/sandwich-check.json`，SHA256 前缀 `90D09ECA74136FC9`）

含全零、单中心、对、重复、共线、外心落界、近平行切 $\varepsilon=10^{-9}$、环+原点、四类不可省性见证、C182 与两个随机例。

| 读数 | 值 |
|---|---|
| 例数 / 采样点总数 | $28$ / $5.6\times10^7$ |
| $\max(\text{格点值}-R_{\rm cand})$ | $\mathbf{0.0}$ |
| $\max(\text{随机点值}-R_{\rm cand})$ | $-6.77\times10^{-8}$（负=无违例） |
| 上界宽度 $\max(h\sqrt2/2+10^{-12})$ | $7.07\times10^{-4}$ |

样例（12 位）：`all-zero-n12`/`single-origin`/`pair-origin-0.9`/`collinear-3+random` 均 $R_{\rm cand}=1.000000000000$、`cc-on-bd-triple` $=1.500000000000$、`ess-c-two-centers` $=1.118033988749895$、`ess-d-regular12-on-circle` $=1.000000000000$。

## 2b 接口校准：多项式接口 vs 几何候选判据（两种表示，`evidence/qe-interface-check.json`）

`py/qe_interface_check.py` 把 `QE-interface.md` §1 的 $A\wedge\bigwedge B_i\wedge\bigwedge C_{ij}\wedge\bigwedge D_{ijk}$（多项式、无定义域量词、含全部退化 guard）实现为布尔函数，与"几何候选判据" $R_{\rm cand}\le r$（直接取候选**点**）逐 $r$ 比较——这是同一命题的两种独立表示。

| 读数 | 值 |
|---|---|
| 构型数 / 决定性探针数（$\lvert r-R_{\rm cand}\rvert>10^{-9}$） | $29$ / $305$ |
| 不一致数 | $\mathbf{0}$ |
| 浮点边界带跳过（$r=R_{\rm cand}$ 等号情形，浮点舍入决定符号） | $14$（其中已判读的 `iface` 全为 True，与"取等即覆盖"一致） |
| 覆盖的退化族 | 全零、单中心、重复、共线、外心落界、近平行切 $10^{-9}$、环+原点、四类不可省性见证、C182 |

**附带发现（已修）**：接口的 $(b)$ 项（反径点）必须是**析取** $\bigvee_j$（"被某个中心覆盖"），不是合取 $\bigwedge_j$。自检例：$C=\{(0,0),(0.9,0)\}$、$r=1=R$——合取写法会误判为不覆盖。该错在 v1 接口稿中出现、由本次检查发现并修正（`QE-interface.md` §1/§5）。

## 2c 精确检查器（`py/exact_checker.py`，全 `fractions.Fraction`，**无浮点、无区间**）

实现 `QE-interface.md` §3.3 的完全无量版本：$A\wedge\bigwedge B_i\wedge\bigwedge C_{ij}\wedge\bigwedge D_{ijk}$，其中
$B/C$ 的根式统一为 $a+b\sqrt s\le0$ 的精确符号-平方分支判别，$D$ 用 $x=v/(2\Delta)$ 代入（guard $|v|^2\le4\Delta^2$，覆盖 $|v-2\Delta c_m|^2\le4\Delta^2\rho$）。

| 读数 | 值 |
|---|---|
| **已知答案对照**（`calib-*`，$11$ 行） | $\{(0,0)\}$（$r=1$ 真 / $0.9999$ 假）；$\{(0,0),(1/2,0)\}$（同）；$\{(\pm1/2,0)\}$（$\rho=5/4$ 真、$\rho=31/25$ 假）；$12$ 个原点中心（$r=1$ 真 / $0.9$ 假）；单中心 $(0.6,0.8)$（$r=2$ 真、$1.99$ 假、$2.01$ 真） |
| 对照不一致数 | $\mathbf{0}$ |
| **域不变式自检**（`selftest_domain`，$8$ 项） | 空 $C$、$r<0$、$\rho<0$、中心 $\|c\|^2>1$（两种入口）**必 `raise AssertionError`**；中心取到边界 $\|c\|^2=1$、重复中心、$r=0$ 且中心在原点 必须**不**报错 |
| **越域语义（已加固）** | $4N-H^2\le0$ 分支**不再 `continue` 计真**，改 `raise AssertionError`（合法域内由 L2' 排除）；`main` 对 C182 段不再"warn 后成功"：任何异常或对照不一致都写 `status=error` 并**非零 exit**（成功时打印 `[OK]`） |
| C182 侧条件 | $12$ 个 17 位十进中心均满足 $\|c_i\|^2\le1$（精确判定） |
| C182 在登记阈值 $U$ 处 | 判据 **真**（$U=22568935234031792038557518369/62500000000000000000000000000$）；该行标为 **instance，非独立对照** |
| C182 精确二分（**已冻结，不再加深**） | $R\in(lo,hi]$：$lo=0.36110296374450867151750799166621$，$hi=0.36110296374450867373795404091652$，宽 $2.22\times10^{-18}$；$U-lo\approx1.10\times10^{-18}$，$hi-U\approx1.12\times10^{-18}$，$U$ 在包围内 |

**判读（严格限定）**：在"主定理成立 + 本实现正确"前提下，$U$ 处判据为真即 $R(C182\text{ 构型})\le U$：这是**精确有理**覆盖证书，与旧 D1 盒细分是不同方法；$lo$ 处判据为假即 $R>lo$。**不改 C182 claim、不是重认证、不证明全局最优**；本实现为同作者实现，非独立复核。

## 3 C182 只读诊断（**诊断读数，不是重认证**）

| 量 | 读数 |
|---|---|
| $n$ / 不同位置数 | $12$ / $12$ |
| $R_{\rm cand}$（float） | $0.3611029637445088$ |
| 登记阈值（C182 精确有理字面） | $0.361102963744508672616920293904$ |
| 两者差 | $\approx1.3\times10^{-16}$ |
| 最大点类型 | $K_c$（中垂线∩圆），对 $(3,9)$，位置 $(0.0928795150133,\,0.9956773552165)$，$\vert\arg\min\vert=2$ |
| 格点值 | $0.36094574936413093$（$\text{violation}=-1.57\times10^{-4}$，$h/\sqrt2\approx7\times10^{-4}$ 量级内） |
| 未过滤 (d) 读数 | $1546.60$（近共线三元组外心远离 $D$） |

**不得误读**：该表只说明"用本判据读该构型得到与登记上界一致的数"，不构成对 C182 的重新认证、不改变任何旧 claim、不证明全局最优。

## 4 复现

```powershell
cd research-2026/n12-global/members/finite-reduction
py -3 -B py/run_battery.py evidence          # 223 例 -> evidence/battery.json + battery-stdout.txt
py -3 -B py/sandwich_check.py evidence/sandwich-check.json
py -3 -B py/qe_interface_check.py evidence/qe-interface-check.json
```

证据哈希（SHA256 前 16 位）：`battery.json 5C7BD5FAE2371883`、`battery-stdout.txt 73800E76ACAF4A5F`、`sandwich-check.json 90D09ECA74136FC9`、`sandwich-stdout.txt 5A6A7EB4742D9D2C`、`qe-interface-check.json F0673E465B9FCA32`。

## 5 器械边界（诚实记录）

- 无独立子代理可用（本环境 `subagent` 路由失败：两次 `Error: no adapter registered for provider "tokenrhythm2"`，另一次 `SubagentDepthError: subagent depth 2 exceeds maxDepth 1`），故**没有**第三方独立实现的数值核查；本目录内的独立审阅只有 Lead 对 PROOF 的人工审计（指出 6 处，v2 已修正）。因此上述"无违例"是**同作者双器械**证据，不应读作独立复核。
- `sandwich` 上界只有 $\approx7\times10^{-4}$ 宽（受 $1$-Lipschitz 格点覆盖半径限制），**不足以**认证等号；认证级等号需要穷尽分支定界（旧 D1 形态），本目录未做（不属于本任务的判据证明）。
- 6 例负 gap 记录在 `battery.json`（`gap` 字段），作为器械失败样本保留。

`py -3 -B py/exact_checker.py evidence/exact-checker.json`   # 精确有理检查器（§2c）
