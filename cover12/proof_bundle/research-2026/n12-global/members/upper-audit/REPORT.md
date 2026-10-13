# UPPER-AUDIT · n=12 源诊断与 D3 字面身份核对报告

成员 `upper-audit`，2026-09-26。写域：`research-2026/n12-global/members/upper-audit/**`（唯一写入处）。
**未修改**共享 `STATUS.md`/`DEAD.md`/`.mathlab` claims；**未覆盖**任何旧构型、证书、输出或日志。
本报告只对 **C182 单构型上界链的接口**负责：追溯 `cover_n_uncovered=36` 与 REPORT `0/328` 的口径差异、
核对 D3 的 Number 转换是否与原 `centers_dec17` 有理对象同一、并做有限重放与独立算术复核。
**不含**全局最优性、下界或 n=12 完成声明。

---

## 0. 结论速览（先给可判定命题与等级）

| # | 命题 | 等级 / 作用域 | 证据 |
|---|---|---|---|
| F1 | 历史字段 `cover_n_uncovered=36` 的语义 = **不加域过滤**时，364 个候选盒里 `min_i dist_box_lo(B,c_i) > claim` 的盒数；7 档（n=12…18）逐值重算与记录一致（36/44/60/72/84/114/142），`cover_examples` 前 5 项名称+20 位值逐字节一致 | [已复现·精确] 单个配置族 n=12…18 的历史记录 | `logs/cover_forensics.txt` |
| F2 | 这 36 个"未覆盖"候选**全部**是与单位闭盘 D 不相交的 `circ*`（三元组外心）盒；D 内/D 上无任何未覆盖候选 | [已复现·精确] 同一对象 | `logs/offender_profile.txt`（3 行计数 + 36 行清单） |
| F3 | REPORT §3 的 `0 / 328 检查盒` = **同一诊断加域过滤**：328 = 与 D 相交的候选盒数，0 = 其中未覆盖数；7 档 checked（328/406/492/602/724/849/986）= `总候选数 − 与 D 不相交的盒数`，逐档对齐 | [已复现·精确] 同上 | `logs/cover_forensics.txt`、`logs/threshold_sweep.txt` |
| F4 | `364−36=328` **只在 n=12 这一行成立**，是巧合而非恒等：n=13 记录值 44，而 `455−44=411≠406` | [已核对·精确] 反例一行 | `logs/cover_forensics.txt` |
| F5 | 差异根因 = **域过滤被半应用**（旧字段不计域过滤、报告列计域过滤），不是对象、阈值或候选族差异：对象同为 `cfg/cert_n12_othern.json:centers_dec17`，阈值同为记录 claim，候选族同为 364=12+2·C(12,2)+C(12,3) | [证据推断]（数值语义已复现；中间代码版本不可恢复，无 git 历史） | `out/cert_all.json`（同文件内 flat 36 + nested `cover{328,0}`）、mtimes、`logs/cover_forensics.txt` |
| F6 | D3 的 Number 管道与 `centers_dec17` **逐坐标同一**：24/24 坐标 `toFixed(17)` 整数 == 直接读 JSON 字面整数，差 0；引擎自报 `literal diffs=14` 是 `toFixed(17)` 对比**同一 double 的最短往返字面**，与身份无关 | [已核对·精确] 该配置 24 坐标 | `logs/d3_ints_audit.txt`、`logs/c182-d3-official.txt` |
| F7 | D3 as-run 区间与"引擎直接跑原始字面整数"（`encloseScaledInts`）区间**字符串完全相同** = [0.361102963744508672616920293903, …904]；`cross_consistent=true`、`valid=true`、`filter_safe_halfdiag=true`、候选 430、argmax=bisect-circle | [已复现·精确] 单构型 | `logs/d3_ints_audit.txt`、`logs/c182-d3-official.txt` |
| F8 | D1/D2 重放（显式 C182 阈值）与历史记录逐项一致：`bb_ok=true`、8057 盒、depth 101；D2 区间 [..903,..904]、argmax `bis5,10#0` | [已复现·精确] 单构型 | `logs/c182-d1-d2-replay.txt` |
| F9 | 独立算术复核（本成员自写、平方比较免 sqrt）：328 个与 D 相交的候选盒 `min_i max_corner|x−c_i|² ≤ claim²` 失败 **0** ⇒（前提=候选族完备引理）`R_D(S12) ≤ claim`；我自算区间 [..903,..904]，argmax 同 | [已核对·精确，条件于候选引理] 单构型 | `logs/independent_cover.txt` |
| F10 | 精确余量：D 外 36 个外心 `|p|²−1 ≥ 0.0151`（无贴边侥幸）；D 内 328 盒覆盖不等式最小余量 ≈ **4.5e-31**（平方单位，盒 `bis5,10#0`）⇒ 半径 ≈ 6.2e-31，与历史区间宽 6.236e-31 同量级 | [已核对·精确] 单构型 | `logs/margins.txt` |

**禁止读法**（本次核对的结果不能支持的说法）：
1. 不得把 36 读成"D 内有 36 处漏覆盖"——36 项全在 D 外（`|p|²−1 ≥ 0.0151`），对覆盖问题无影响。
2. 不得把 REPORT §3.2 的 `0/328` 当覆盖率证书——它是**必要**条件的正对照（见 §4），REPORT 自己也标了"不是证明"。
3. 不得由本次单构型上界推出 r_D(12) 的最优性、唯一性或下界。
4. 不得把 Pegg 值当"精确最优刻画"（lead 2026-09-26 已收窄为代数数值对照；与本报告的 C182 上界部分无关）。

---

## 1. 被核对对象与证据哈希（只读，未改动）

| 角色 | 路径 | SHA256 前缀 |
|---|---|---|
| 认证对象（17 位十进制字面，精确有理） | `research-2026/session2/n1314/cfg/cert_n12_othern.json` | `922CD6216EEC0210FDB26E4F08029113…` |
| 历史输出（含 `cover_n_uncovered=36`） | `research-2026/session2/n1314/out/cert_n12_othern.json` | `A92606F6B05CBC0B5D9C3628407E5A7E…` |
| 批量历史输出（flat 36 + nested `cover{328,0}`） | `research-2026/session2/n1314/out/cert_all.json` | `0E6F6C7A94A7C81F5FB1D12B215A54C8…` |
| 覆盖诊断当前实现（含域过滤） | `research-2026/session2/n1314/py/cert_batch.py` | `F63555E37668D5E0B47492444B2F7765…` |
| D3 引擎（团队既有件，只读引用） | `n11/upper/enclose17.mjs` | `BDD20E942CED1CB7D08E8BB8E5F3DB9A…` |
| D2 候选族 + 精确区间工具 | `research-2026/session2/n1314/py/cert_cand.py`、`py/certlib.py` | `FDA934BD272D4875…`、`D51B5B8770BEA5F3…` |
| D1 分支定界 | `research-2026/session2/n1314/py/cert_bb.py` | `55D465CC2C279CEF…` |

记录阈值（本文所有"claim"）：`claim = 22568935234031792038557518369/62500000000000000000000000000`
`= 0.361102963744508672616920293904`（与 `out/cert_n12_othern.json:claim` 同值）。

---

## 2. `36` 的精确语义（F1/F2/F4）

`cert_batch.candidate_coverage` 当前源码的判据是 `min_i dist_box_lo(B, c_i) > r`，
`dist_box_lo` = 盒到点的**距离下界**（定向 `sqrt_lo`，`SCALE_BITS=96`）。两种计数只在**是否先剔除与 D
不相交的盒**上不同。逐档重算（不写旧文件）：

| tag | 候选总数（记录 `cover_n_cand`） | 与 D 不相交 O | 无域过滤未覆盖 `U_all` | **域过滤后未覆盖** `U_in` | 记录 `cover_n_uncovered` | 记录 = `U_all`? |
|---|---|---|---|---|---|---|
| n12_othern | 364 | 36 | 36 | **0** | 36 | ✔ |
| n13_v1 | 455 | 49 | 44 | **0** | 44 | ✔ |
| n14_v1 | 560 | 68 | 60 | **0** | 60 | ✔ |
| n15_v1 | 680 | 78 | 72 | **0** | 72 | ✔ |
| n16_v1 | 816 | 92 | 84 | **0** | 84 | ✔ |
| n17_v1 | 969 | 120 | 114 | **0** | 114 | ✔ |
| n18_v1 | 1140 | 154 | 142 | **0** | 142 | ✔ |

- 7/7 档 `记录 cover_n_uncovered = U_all`（**无域过滤**），且 `cover_examples` 与 `U_all` 前 5 项
  （名称 + `fstr(d,20,'down')` 值）逐字节相同；免 sqrt 的精确平方变体给出同样的 36/0/36，
  说明识别不依赖 `sqrt_lo` 取整。
- n=12 的 36 项全是 `circ*`，值域 0.364921945… … 1546.601281752…（近共线三元组的远外心，
  坐标量级 ~1.5e3），36/36 与 D 不相交。故 `U_in=0`：**D 内/D 上没有未覆盖候选**。
- 反例行：n=13 的 `U_all=44 ≠ O=49`，而 REPORT 的 checked=406=455−49。故
  `364−36=328` 是 n=12 行的巧合（该行恰好 `U_all=O=36`），**不能**当作"36 就是域外过滤解释"的恒等式。

---

## 3. `0/328` 的精确语义与两文件的口径并存（F3/F5）

- `328` = `364 − 36` = 与 D 相交的候选盒数；同一算式对 n=13…18 给 406/492/602/724/849/986，
  与 REPORT §3 表逐档一致 ⇒ **REPORT 的 checked 列 = 当前（带域过滤）实现的 `n_checked`**。
- `0` = 这批盒里未覆盖数（当前实现 `n_uncovered`）。REPORT 行写作 `0 / 328 检查盒`，
  **同一对象、同一阈值、同一候选族**，只是对 `uncovered` 与 `checked` 都加了域过滤。
- 判别力（同源复现 `n1314 STATUS.md §4` 的读数）：`claim−1e-9` 时域过滤未覆盖数
  n=13/14/17 = **19/29/25**（STATUS 原文）✔；`claim−1e-6` = **19/36/25** ✔；n=12 为 30/30。
  即该诊断在阈值下调 ~1e-9 时立刻出现失败 ⇒ 它在 claim 处给的是**有判别力的必要条件**。
- 并存证据：`out/cert_all.json` 的 n=12 记录**同一个 JSON 对象**里同时有
  `"cover_n_uncovered": 36`（flat，无域过滤，附大值 examples）与
  `"cover": {"n_cand":364,"n_checked":328,"n_uncovered":0,"examples":[]}`（nested，带域过滤）。
  mtimes（本机、2026-09-20）：`out/cert_n12_othern.json` 14:50:39 → `out/cert_n18_v1.json`+`cert_session_log.txt`
  14:53:19 → `py/cert_batch.py` **14:53:39（在产出之后被编辑）** → `__pycache__/cert_batch.cpython-314.pyc`
  **14:53:56（编辑后首次被导入）** → `out/cert_all.json` 14:54:02 → `REPORT.md` 15:33:20。
  `.git` 不存在（`Test-Path .git` = False），中间版本无法从版本库恢复。
  即：per-tag 记录 = 旧（无过滤）计数器；`cert_all.json` 的 nested `cover` 与 REPORT §3 / STATUS §4
  = 编辑后（带过滤）计数器——两个计数的全部 7 档数值均已由我在本报告中独立复现（§2 表、§3 判别力）。

**口径结论**：两个数字不是互相矛盾的两个"事实"，而是**同一诊断在两种域过滤约定下的两个计数器**
（旧 flat 字段 = 无过滤；报告列 = 有过滤）。因此 36 **不构成**对 C182 上界的反例或撤回理由；
真正承重的覆盖不等式证书是 D1 与 D2 的 `hi`（§5），不是这条正对照。

---

## 4. 文档级缺陷（应记入 DEAD 的"实现/诊断语义"，不是数学判死）

1. `candidate_coverage` docstring 写"`dist_box_lo ≤ dist(x,·)` ⇒ 盒内每点都在某盘内"——
   方向不成立：`min_i dist_box_lo(B,c_i) ≤ r` 只说明**存在**点与**存在**盘近，不控制盒内其它点；
   要覆盖整盒需要上界 `dist_box_hi`。正确可用的蕴含只有**必要条件**：
   `R ≤ r` ⇒ 每个与 D 相交的候选盒满足 `min_i dist_box_lo(B,c_i) ≤ r`。
   （REPORT §3.2 已自标"**不是证明**"，故本条是措辞/接口缺陷，不是假证书。）
2. 字段名 `cover_n_uncovered` 未标注域范围；把它读成"D 内漏覆盖数"是误读。REPORT 的 `检查盒` 列
   才是带域过滤的版本，两列必须成对引用。

---

## 5. D3 字面身份与有限重放（F6/F7/F8/F9/F10）

### 5.1 坐标级同一性（直接比对，不依赖引擎自诊断）

`js/scale/enc17.mjs` 做 `Number(p[0])`，`encloseHigh` 内部 `certifiedInts` 用 `toFixed(17)` 作为
**认证对象**。`js/d3_ints_audit.mjs` 把三方对齐：JSON 字面整数 / `toFixed(17)` 整数 / 最短往返字面整数：

- **24/24 坐标：`toFixed(17)` 整数 == 直接读 JSON 字面得到的整数，差 0** ⇒ D3 认证的就是
  `cfg/cert_n12_othern.json:centers_dec17` 这个精确有理对象，**无需任何转移界**。
- 引擎自报 `literal vs certified coordinate diffs = {"differing_coordinates":14,"total":24}`：
  这 14 处是 `toFixed(17)` 与**同一 double 的最短往返字面**（如字面 `0.77932142321915399`
  的最短表示为 `0.779321423219154`，二者同一 double，`toFixed(17)` 复原原字面）。它**不是**
  与 JSON 字符串的差异；START 要求的"逐项直接比较"结果就是 0 差异。
- 反向证据：用同一引擎直接对原始字面整数跑 `encloseScaledInts`（绕开 Number），得到区间字符串
  与 as-run 完全相同，`cross_consistent=true`。

### 5.2 重放读数

| 装置 | 读数 | 与历史记录 |
|---|---|---|
| D1 `bb_upper`（显式 claim） | `ok=true`，8057 盒，`maxdepth=101`（nprune_out 1421 / nprune_ub 4622 / ntight 2939，cpu 7.4 s） | 与 `bb_boxes=8057`、`bb_depth=101` 一致 |
| D2 `cert_cand.enclose` | `R ∈ [0.361102963744508672616920293903, …904]`，argmax `bis5,10#0` | 与 `d2_lo/d2_hi/d2_argmax` 一致 |
| D3 `encloseHigh`（官方驱动） | [..903, …904]，430 候选/394 included，`filter_safe_halfdiag=true` | 同上 |
| 本成员独立装置（自写 sqrt、精确平方比较） | 328 个与 D 相交盒失败 **0**；`hi ≤ claim`；`lo ≥ hist d2_lo`；argmax `bis5,10#0` | 独立支持同一条上界 |
| float64 网格对照（**非证书**） | 4001² 网格 max = 0.3610364332096850 ≤ claim | 仅作下方向控制 |

### 5.3 承重链条与本次独立复核的边界

`R_D(S12) ≤ claim` 的完整链条是两段：

1. **候选族完备引理**（纸面数学，本次我复核其分支与排除，见 §6）：
   最大化点 x\* 必属于 {三元组外心} ∪ {中垂线∩∂D} ∪ {对径点}，且 x\* ∈ D 故其盒与 D 相交；
2. **精确不等式**（本成员计算，条件于 1）：对每个与 D 相交的候选盒 B，`min_i max_{x∈B}|x−c_i| ≤ claim`
   ⇔ `min_i (四角 |x−c_i|² 的最大值) ≤ claim²`——纯有理比较，**不用 sqrt**，0 失败。
   由此 `R ≤ min_i max_{x∈B*}|x−c_i| ≤ claim`（B\* = 含 x\* 的盒）。

这次复核**没有**独立证明引理 1 的数学内容（那是纸面论证）；也没有给出 r_D(12) 的下界、
没有排除其它 11 个或更少中心数的构型、没有触及最优性。等级 = 单构型上界（与 C182 的作用域相同）。

---

## 6. 候选族完备引理的复核（纸面，供独立复核者挑错）

设 `f(x)=min_i|x−c_i|`，D 紧、f 连续 ⇒ 最大化点 x\* 存在。按 x\* 位置与活跃集 `A={i:|x*−c_i|=f(x*)}` 分类：

- **|x\*|<1（内点）**：若存在方向 v 使 `⟨v, x*−c_i⟩>0` 对所有 i∈A 成立，则沿 v 微动时
  所有活跃距离严格增大；非活跃距离有正余量、小扰动下仍非活跃 ⇒ f 增大，与最大性矛盾。
  两活跃点的方向集合交为空 ⇔ `x*−c_i` 与 `x*−c_j` 反向 ⇔ x\* 是 c_i c_j 中点，此时沿垂线移动
  使两者距离都增大（`|x*+tn−c_i|² = (|c_ic_j|/2)² + t²`），同样矛盾。故内点活跃数 ≥3
  **互异**中心且三者等距 ⇒ x\* 是三元组外心（精确有理点，已枚举）。
  （三中心共线时不可能三点等距；若含重合心，则互异三元组仍被枚举到。）
- **|x\*|=1 且 |A|≥2**：x\* 在中垂线上且 |x\*|=1 ⇒ 是中垂线∩∂D 的两交点之一（已枚举，两交点都列）。
- **|x\*|=1 且 |A|={i}**：沿 ∂D 的局部最大要求 `d/dθ|x−c_i|=0` ⇒ x\* = −c_i/|c_i|（已枚举）。
  需 `c_i ≠ 0`；S12 的 12 个中心全不为 0（最小模长 = `|c_2| > 0.278241660874427933074758036213`，
  见 `logs/center_moduli.txt`），故本对象无退化缺口。
  另注：若某中心恰在原点，对径点未定义——这是"引理一般形式"的边界条件，与 S12 无关；
  D3 源码 `if (ra.lo > 0n)` 亦显式跳过该情形。

D2 的候选族与上述三类完全一致（D3 额外含 midpoint，只会放松 `hi`，不影响正确性）。
**注意**：本节的排除论证是纸面推理，未经形式化；建议由独立成员用不同表述（KKT/Clarke 或
沿边界一维化）复核，尤其是"内点两活跃点不可能"与"边界单活跃点必为对径点"两步。

---

## 7. 交付文件与复现命令（全部在本成员写域内）

| 文件 | 内容 |
|---|---|
| `py/cover_forensics.py` → `logs/cover_forensics.txt` | 7 档两计数器逐值重算、examples 比对、checked 列对齐 |
| `py/threshold_sweep.py` → `logs/threshold_sweep.txt` | 调用**原** `cert_batch.candidate_coverage`，claim/claim−1e-9/claim−1e-6 |
| `py/offender_profile.py` → `logs/offender_profile.txt` | 36 项清单、类型直方图、域内/域外归类 |
| `py/margins.py` → `logs/margins.txt` | `|p|²−1`（域外余量）与覆盖不等式精确余量 |
| `py/independent_cover.py` → `logs/independent_cover.txt` | 自写候选族 + 免 sqrt 精确平方判定 + 网格对照 |
| `js/d3_ints_audit.mjs` → `logs/d3_ints_audit.txt` | 24 坐标三方整数比对 + 两对象区间比较 |
| `logs/c182-d1-d2-replay.txt` | `certify_cfg.py` 显式阈值重放（D1+D2） |
| `logs/c182-d3-official.txt` | 官方 `node js/scale/enc17.mjs ../../cfg/cert_n12_othern.json` 原样输出 |

```powershell
# 从工作区根执行；所有输出重定向到本成员 logs/（不写旧文件）
py -3 -B research-2026/n12-global/members/upper-audit/py/cover_forensics.py   > research-2026/n12-global/members/upper-audit/logs/cover_forensics.txt 2>&1
py -3 -B research-2026/n12-global/members/upper-audit/py/threshold_sweep.py   > research-2026/n12-global/members/upper-audit/logs/threshold_sweep.txt 2>&1
py -3 -B research-2026/n12-global/members/upper-audit/py/independent_cover.py > research-2026/n12-global/members/upper-audit/logs/independent_cover.txt 2>&1
py -3 -B research-2026/n12-global/members/upper-audit/py/offender_profile.py  > research-2026/n12-global/members/upper-audit/logs/offender_profile.txt 2>&1
py -3 -B research-2026/n12-global/members/upper-audit/py/margins.py           > research-2026/n12-global/members/upper-audit/logs/margins.txt 2>&1
node research-2026/n12-global/members/upper-audit/js/d3_ints_audit.mjs        > research-2026/n12-global/members/upper-audit/logs/d3_ints_audit.txt 2>&1
py -3 -B research-2026/session2/n1314/py/certify_cfg.py research-2026/session2/n1314/cfg/cert_n12_othern.json --key centers_dec17 --nd 17 --claim 0.361102963744508672616920293904 > research-2026/n12-global/members/upper-audit/logs/c182-d1-d2-replay.txt 2>&1
node research-2026/session2/n1314/js/scale/enc17.mjs ../../cfg/cert_n12_othern.json > research-2026/n12-global/members/upper-audit/logs/c182-d3-official.txt 2>&1
```

---

## 8. 本次未做 / 未决（不要读成已完成）

- **未**登记或修改 claim；本报告结论如需进台账，应由 lead 决定并注明本成员为来源、独立复核状态。
- **未**独立证明候选族引理（§6 只是复核性推导）；建议另派成员用不同表示复核。
- **未**做任何下界、全局排除或最优性工作；`r_D(12)` 的全局目标仍是 gap。
- Pegg 对照的来源力度由 lead 2026-09-26 收窄（Q2651575 正文为近似关系 `r(12)≈1/2.769≈1/(x+1)`，
  `x³−2x−2=0`，非精确最优刻画）；这与 C182 单构型上界部分无关。
