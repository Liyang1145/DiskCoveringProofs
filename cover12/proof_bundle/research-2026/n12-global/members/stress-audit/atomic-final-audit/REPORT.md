# atomic-final-audit — 独立表示审计：k10 冻结整数原子核 + 控制叶 4398 @ 2^28

范围：只做 Lead 指定的关键核独立数学/表示审计，**不是** 6723 叶全队列重放。
写域仅 `members/stress-audit/atomic-final-audit/`；未改 `lead/**`、冻结核、shared、n11。

被审对象（哈希实测，2026-09-27）：
* `members/upper-audit/integer-atomic/py/integer_kernel.py` SHA256 `0115c3f3660382cc5bcc53c1faf287ff…`（冻结）
* `members/upper-audit/integer-atomic/py/integer_kernel_n.py` SHA256 `a89a2cee8dcbcf4dd7585b6878a6ad48…`
* 快照 `evidence/hubline-domain-stage11825.json` SHA256 `26fefd6a842b9ca9…`（与 obligation B 记录一致）
* 向量集 `evidence/atomic-unit-vectors-2048.json` SHA256 `acc14b2c954c9174…`（= escalated 记录的 `units_sha256`）
* 数学依据 `lead/ATOMIC-DUAL-PROOF.md` SHA256 `3c31fad500471c01…`

独立性声明：我的所有结论来自 (i) 源码逐行推导，(ii) 自写 **exact-Fraction 表示**的原子矩形/距离/严格性探针
（`py/fraction_control_4398.py`、`py/integrity_probes.py`），**没有** import 被审 `bound` 来构造任何我的量；
被审 `bound/certify` 只被**调用做输出对照**（Lead 要求的“与整数 bound 的输出对照”）与重放记录。
`integer_kernel_n.py` 的 `bound/certify` 是**继承**冻结类的（其自身 docstring 已声明），因此对这两个方法的
结论全部是源码推理 + 小样本独立重算，不是第二套实现的一致通过。

## 0. 结论

1. **未发现影响 certified 的可靠性缺陷**；7 条核内判据的方向逐条成立（§1），8 个 annulus 严格性探针、1500 组
   (atom, box) 对照、4 个负/完整性探针全部通过（§3）。
2. 控制叶 4398 @ 2^28：我的精确重建给出 **atoms=4778、demand=325879733812**，与记录**逐位一致**；
   阈值、端点上限（2^28）、以及记录中的 **2^26 capture=32608767913** 被我独立重算复现（§3.4）。
3. 三项发现（按性质分类，均不影响本叶 certified 的数学结论）：**F1 provenance**（快照记录叶计数与冻结核重跑不一致）、
   **F2 字段**（`depth` 在 2^28 不可信）、**F3 参数绑定**（`screen` 必须是 True 才是证书级；空权集会抛错而非假证明）。详见 §4。
4. 未覆盖：接口前提 P-a…P-d（§2，属其他成员 scope）、float 核 `hubline_atoms_fast.py` 的 PAD 界、全队列重放。

## 1. 核内判据：方向与前提逐条（源码行号）

记号：`S=2^Sexpt`，整数单位 = 1/S；`H=[(sl,sh),(xl,xh),(yl,yh)]`；向量 `v=(c,s_v)`，`c²+s_v²=1` 精确有理。

| # | 判据 | 行 | 方向/含义（我的推导） |
|---|---|---|---|
| D1 | 原子矩形含真实原子 | ik:95–103, ikn:154–161 | hub1 坐标 `x−s+Uc` 对 `x` 单增、对 `s` 单减 ⇒ 值域恰为 `[xl−sh+Uc, xh−sl+Uc]`；`y+Us_v` over `y∈[yl,yh]` ⇒ `[yl+Us_v, yh+Us_v]`。hub2 同理 `[xl+sl+Uc, xh+sh+Uc]`。边界原子取点。⇒ 任意三元组、任意 `v` 的真实原子都在矩形内。 |
| D2 | 外舍入 ⇒ 距离只会变小 | ik:102–103 | `floor(rx0·S) ≤ rx0·S ≤ rx1·S ≤ ceil(rx1·S)` ⇒ 整数矩形 ⊇ 精确矩形 ⇒ `d2_int ≤ S²·d²_exact`（**over-count 方向**成立；1500 组对照 0 反例）。 |
| D3 | capture 判据 `d2_int ≤ U2_ceil=⌈U²S²⌉` | ik:69,135 | 无假阴性：真实 `d²≤U²` ⇒ `d2_int ≤ S²d² ≤ U²S² ≤ U2_ceil` ⇒ 必计入（1500 组 0 反例）。上界性：计入只是“可能可达”⇒ 求和是真实 capture 的**上界**（外扩最多每坐标 1 单位）。 |
| D4a | annulus 内拒 `high < inner_floor` | ik:70,126 | `high=farx²+fary²` **恰好** = `S²·max_box(x²+y²)`（坐标独立）；`inner_floor=⌊(1−U)²S²⌋ ≤ (1−U)²S²` ⇒ 丢弃 ⇒ 盒内 `|c|<1−U`（非激活）⇒ 无合法中心。严格性：`max|c|=1−U` 时 `high ≥ inner_floor` ⇒ **保留**（探针 touch-inner-exactly ✓）。 |
| D4b | annulus 外拒 `low > outer_ceil` | ik:71,126 | `low` **恰好** = `S²·min_box(x²+y²)`；`outer_ceil=⌈(1−U²)S²⌉ ≥ (1−U²)S²` ⇒ 丢弃 ⇒ `min|c|²>1−U²` ⇒ 无合法中心。保留侧只增大搜索域（sound）。 |
| D5 | 权重 `round(v·1e9)`、丢零 | ik:87–94 | 密度用精确双角递推 + 有理 `(c,s_v)`（`assert v≥0`）；`Fraction.__round__` 精确（半偶），`|w−v·10⁹|≤1/2`；丢 `w=0` 不改 T 也不改 capture 和（0 权贡献 0）。控制叶 0 违规、0 零权。 |
| D6 | 叶判据 `10·val < total` **严格** | ik:150 | 任一放置的捕获 ≤ `10·max_val < total` ⇒ 必有原子（权≥1）未被十环捕获 ⇒ 矛盾成立；等号不足（P3 负对照：capture=total 时永不 certified）。 |
| D7 | int64 范围 | ik:112–113,134 | `|原子端点|≤2S`（构造后 assert；实测 max=2^28 @2^28，与记录一致）；环端点 `|·|≤S`；`|dx|≤3S`（原子 2S + 环 S，代码按 4S 保守）；`d²≤18S² < 32S²=2^61 < 2^63`（S=2^28），阈值 `⌈U²S²⌉/⌊(1−U)²S²⌋/⌈(1−U²)S²⌉` 分别 9.396e15/2.941e16/6.266e16 ≪ 2^63；`total<2^60`、`10·total<2^63` assert；列表→int64 越界会**抛错**而非回绕。 |
| D8 | 失败诚实性 | ik:143–156 | 预算→`budget`（P1 ✓）；宽度 ≤16 → `unresolved`（永不 `certified`）✓；全零权 → 构造抛 `ValueError`（P2：响亮失败，不给证书）✓。 |

DFS 全域论证（我自己的表述）：根盒 `[−S,S]² = [−1,1]²`；合法（归一化）环心在 annulus
`[1−U, √(1−U²)] ⊂ [−1,1]²`（`1−U=0.6389>0`，`√(1−U²)=0.9325<1`）；整数二分是精确铺砌（偶数中点 assert ⇒ 格点不变量）；
每个被丢弃盒由 D4a/D4b 保证不含合法中心 ⇒ 任一合法放置的十个中心都落在某个“保留盒”内 ⇒
`10·max_val < total` ⇒ 有原子未被覆盖。**结论只依赖 D4a/D4b 的单盒方向性 + 精确铺砌**，与遍历顺序/栈序无关。

## 2. 外部前提（kernel-external；我未重证，只核对它们被引用处）

* **P-a 归一化**：每个激活环心可移到 annulus `[1−U,√(1−U²)]` 且保持“保留原子仍被十环覆盖”。依据
  `lead/INNER-ROOT-REDUCTION.md`（`GLOBAL-INTERFACE-AUDIT.md` §1 引用“D-intersection inclusion and equality of the actual S1 arcs”）。
  **注意承重的是 D∩ 包含/并集覆盖那条**（hub 原子是内点，仅弧相等不够）——建议在接口文档里把这条写成显式引用。
* **P-b 原子必要性**：边界原子（两 hub 都够不到 S¹，因 `|h_j|+U<1`）；hub 原子经扰动 + 有限并闭性
  （`ATOMIC-DUAL-PROOF.md` §witness measure；筛选恒等式 `dist²−U²=4s(s∓Uc)` 精确）；交界原子用 `v=n1+n2` 的显式扰动。
* **P-c s=U 面无法 k10 三元组**（`ATOMIC-DUAL-PROOF.md` §8、`members/structure/atomic-interface/AUDIT.md` Q1）⇒ 盒含 s=U 只是保守超集。
* **P-d 核心/原子分工**：两个非激活 hub 负责核心，十环负责原子；核心侧由 producer 的 (i)(ii)(iii) 删除测试负责（非本核）。

## 3. 控制叶 4398（stage11825 原子序 4398，atomN=2048）

1. **精确重建**（Fraction，无缩放）：atoms=4778（boundary 2048 + hub1 1365 + hub2 1365；筛选各丢 683），
   demand=325879733812 — 与记录 `atoms/total_integer_demand` **逐位一致**。
2. **阈值**：2^26 → `587248451585182 / 1838321733031375 / 3916351175785315`；
   2^28 → `9395975225362900 / 29413147728502004 / 62661618812565037`（= ⌈U²S²⌉/⌊(1−U)²S²⌋/⌈(1−U²)S²⌉ 精确）。
3. **端点上限**：我的 max |原子端点| = 268435456 = 2^28（2^28 尺度），cap 2S=536870912；与记录 `max_endpoint_units=268435456` 一致。
4. **独立重算一个记录数字**：记录 2^26 未决盒 `(4512816,4512832,−43155728,−43155712)` 的 capture = **32608767913**；
   我用自写整数算术得到同一值，`bound()` 也返回该值 ✓（存储数字被独立复现）。
5. **annulus 严格性探针（8 个，全部 OK）**：`inside-hole`(丢)、`x-in-hole y-outside-outer`(丢)、`straddle-inner`(留)、
   `straddle-outer`(留)、`strictly-outside-outer`(丢)、`strictly-inside-hole`(丢)、**`touch-inner-exactly`(留，验证非严格侧)**、
   `outside-outer-094`(丢)；我的独立精确判据与 kernel 判定逐项一致。
6. **1500 组 (atom, box) 对照**：假阴性 0；over-count 0（超出文档化 6/S shell 的 0）。
7. **重跑对照**：冻结核 `certify()` @2^28 给出 `boxes=13783, leaves=6757, outside=135, max_capture=32587905919,
   gap=674622, atoms=4778, scale=2^28, max_d2_seen=268165183489113677(=3.72S²≤18S²)`，与 `escalated-scale28-evidence.json`
   的 `scale_28_result` **逐位一致** ✓。
8. **负/完整性探针**：P1 预算截断→`budget{boxes:11,pending:7}`；P2 全零权→构造抛错（无假证明）；
   P3 `10·val ≥ total`（含等号）→`unresolved{boxes:81}`，**永不 certified**；P4 见 4。

## 4. 发现（不影响本叶数学结论，但影响 manifest/replay 口径）

* **F1 provenance（具体、可复现）**：快照内该叶 `result` = `{boxes:13781, leaves:6756, outside:135, max_capture:32587905919,
  demand:325879733812, gap:674622, atoms:4778}`，**缺 `scale` 字段**；而冻结核在 2^28 上重跑 = `13783/6757`（其余数字一致）。
  两个文件（`evidence/atomic-unit-vectors-2048.json` 与 member 的 `canonical-unit-vectors-2048.json`）我逐元素比对**相同**
  （仅字节格式不同 ⇒ hash 不同是预期的），H/权重也按 demand/atoms 对齐，故差异来自**产生记录时的代码版本**（旧版字典无 scale/max_d2 字段）。
  **影响**：该叶的**存储计数**只能作诊断，不能作证据；接受必须建立在“源绑定重放”上（`escalated-scale28-evidence.json` 即是，
  我的重跑独立确认其证书数字）。建议 manifest 校验对“recorded boxes/leaves”与重放不一致的叶**明确标注**（gap/capture 一致不算绑定）。
* **F2 字段（复核确认 upper-audit 的发现）**：`certify(max_depth=23)` 的 `max_depth` 只被回显；停止靠 `w ≤ 16`。
  2^26 下真实分裂深度 = 23（与字段巧合一致），**2^28 下应为 25**，而字段仍写 23 ⇒ `unresolved` 记录的 `depth` 不可信（不影响 certified）。
* **F3 参数绑定**：`integer_kernel_n.IntAtomsN(..., screen=False)` 会保留可能落在另一 hub 内部的原子 ⇒ 那些原子**不必**由十环覆盖 ⇒
  “`10M<T` ⇒ 有原子未覆盖”的推理失效 ⇒ **该配置下 certified 可能是假排除**。冻结类恒为 `screen=True`（无开关），
  saved 证书走默认 True；但每叶证据未记录该开关。建议：校验器显式绑定 `screen=True`（或等价地绑定原子集哈希），并在文档里标明该参数是**证书级参数**。
  附：全零权向量在构造期抛 `ValueError`（空数组 max）——响亮失败，可接受。

## 5. 复现

```
$env:PYTHONIOENCODING='utf-8'
py -3 -B research-2026/n12-global/members/stress-audit/atomic-final-audit/py/fraction_control_4398.py
py -3 -B research-2026/n12-global/members/stress-audit/atomic-final-audit/py/integrity_probes.py
```
日志 `logs/`，证据 `evidence/fraction-control-4398.json`、`evidence/integrity-probes.json`。
