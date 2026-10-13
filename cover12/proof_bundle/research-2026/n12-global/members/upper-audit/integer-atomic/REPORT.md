# INTEGER-ATOMIC · 纯 int64 距离核（去除 IEEE 前提的独立重放核）

成员 `upper-audit`（子目录 `integer-atomic/`），2026-09-26。写域 `members/upper-audit/integer-atomic/**`。
**未改** `lead/**`、未覆盖 evidence（只读）。

**版本/hash（引用必带）**
* 核源码 `py/integer_kernel.py` SHA256 `0115C3F3660382CC5BCC53C1FAF287FF624CA2F2C649A02035B7494759C0FC50`
* guard 自检 `py/guard_selftest.py` SHA256 `D89F9F49720A02D637153F0268F2B9D85F63CC98973769EB87D466484C70D687`
* canonical units `evidence/atomic-unit-vectors-2048.json` SHA256 前缀 `acc14b2c954c9174…`
* 输入 stage `evidence/hubline-domain-stage2200.json` SHA256 前缀 `fd7e2ac05e346bac…`

---

## 0. 结论（可判定）

| 对象 | 整数核结果 | 与 float 核记录 |
|---|---|---|
| 原 positive 盒 `s∈[199/1000,201/1000], x∈[0,1/1000], y∈[23/2000,27/2000]` | **certified**：boxes 11875 / leaves 5818 / outside 120 / max 32575800681 / total 325759278632 / gap 1271822 | 逐字段相同 |
| stage2200 最紧 3 盒（relgap 1.85e-11、8.56e-10、1.86e-9） | **certified ×3**：25425/12609/104/gap 6；7843/3780/142/gap 278；9265/4438/195/gap 605 | 逐字段相同 |
| stage2200 最紧 8 盒（追加 5 个） | **certified 8/8**，无一 unresolved/budget | — |
| 类 API guard（18 条负控制 + 正控制） | **18/18 fire，0 miss；正控制 PASS** | `logs/guard_selftest.txt` |

**判读**：在 S = 2^26、深度 ≤ 23 的设定下，纯整数（int64）距离判据能**独立**复现全部被检盒的证明状态，
包括相对间隙仅 **6/3.24e11 ≈ 1.9e-11** 的 #946；整数核与 float 核的盒数/叶数/最大权/间隙**完全一致**
（一致性只是观察，结论依据是整数算术本身的 out-of-range 方向与下限保证，见 §2）。
⇒ 这些证书**不再依赖 IEEE 浮点陈述**；可作为 manifest 级独立重放核（按盒逐个 `status`）。

---

## 1. 设计（严格按 lead 规格）

* **尺度**：`S = 2^26`；atom 精确有理坐标 rectangle 由 `records + H` **重建**（不用 float X 数组），
  下端 `floor(·S)`、上端 `ceil(·S)` 取整（outward）；`assert max|endpoint| ≤ 2S` ✓（实测 = `S`，只用了一半余量）。
* **ring 盒**：dyadic，DFS 深度 ≤ 23；端点以 1/S 为单位是**精确整数**（`(a+b)` 偶性断言 ✓），
  最小盒宽 ≥ 16 单位（= 16/2^26 ≈ 2.4e-7）。
* **距离**：`dx = max(Ax0−Bx1, Bx0−Ax1, 0)`（同 y），`d2 = dx²+dy²` 用 `np.int64`；
  `|diff| ≤ 4S`、`d2 ≤ 32S² = 2^57`（**实测 max_d2 ≤ 1.68e16 ≈ 0.117·32S²**，距 2^63 约 550× 余量）。
* **阈值（精确有理→整数，方向关键）**：`U2_ceil = ceil(U²S²)`（计 capture 当且仅当 `d2 ≤ U2_ceil`）；
  annulus `inner_floor = floor((1−U)²S²)`、`outer_ceil = ceil((1−U²)S²)`，
  丢弃条件 `high < inner_floor` 或 `low > outer_ceil`（严格、保守方向）。
* **权重/筛选**：权重仍为 `round(W(θ)·1e9)` 的正整数；曝光筛选在**精确有理**里做
  （j=1: `U·c ≤ s_lo`；j=2: `U·c ≥ −s_lo`）；单位向量只从 `evidence/atomic-unit-vectors-2048.json` 读取（无 `tan`）。
* **整数和**：capture 用 int64 求和（`≤ total < 2^60` 断言 ✓；`10·total < 2^63` 断言 ✓），
  接受判据 `10·val < total` 在 Python 整数里比较（无溢出）。
* **前提进类 API（本次补强）**：`IntAtoms.__init__` 断言 `20≤Sexpt≤28`（int）、`len(H)==3`、每维 `(lo,hi)` 有序、
  `H[0][0] ≥ 0`、`len(weights)==3`、每 row 为序列、row 长奇数且 ≥5、三 row 等长；
  `bound` 断言 `-S ≤ bx0 ≤ bx1 ≤ S`（y 同）。⇒ 独立复核器直接调用 class 即继承全部前提，
  不依赖 CLI 侧检查（`py/guard_selftest.py` 用 18 条负控制逐条证明 guard 会触发）。

## 2. 为什么它是证明（两个方向）

* **无假阳性（outside ⇒ 真距离 > U）**：整数 atom 矩形是精确矩形的 outward 扩张 ⇒ `dx,d2 ≤ 真 d²·S²`；
  故 `d2 > U2_ceil ≥ U²S²` ⇒ 真 `d² > U²` ✓。ANNULUS 同理：ring 盒端点在 1/S 网格上**精确**，
  `low/S², high/S²` 就是真 min/max 半径²，配合 floor/ceil 阈值 ⇒ 丢弃只在"证明不交 annulus"时发生 ✓。
* **无假阴性（真距离 ≤ U ⇒ 必被计入）**：真 `d² ≤ U²` ⇒ `d2 ≤ U²S² ≤ U2_ceil` ✓。
* 唯一 slack 是 atom 矩形的 outward 扩张（≤ 1 单位/坐标 ⇒ 平方距离最多降 ~6/S ≈ 9e-8）；
  实测在 4 类盒 × 10,000 随机 (盒, atom) 样本上 **outward-rounded overcounts = 0**，
  **false negatives = 0**，**shell violations = 0**。

## 3. 自检（每次运行都跑）

`py/integer_kernel.py` 内建：`max|endpoint| ≤ 2S`、ring 端点/中点精确性、`d2 ≤ 32S²`、
`total < 2^60`、`10·total < 2^63`；外加 Fraction 标定（随机 dyadic 盒 depth ≤ 23 × 随机 atom，双向）
——本次所有运行均为 `fn=0, ov=0, bad=0`。另：随机盒按**索引构造**（`bx0 = -S + k·w`），
避免负数取模把 depth-0 盒映出域（旧写法在 depth=0 时把 `-S` 映到 `-2S`；新 guard 恰好抓到该助手 bug，与核无关）。

## 4. 复现

```powershell
cd research-2026/n12-global/members/upper-audit/integer-atomic
py -3 -B py/guard_selftest.py                                            # 18 guard 负控制 + 正控制
py -3 -B py/integer_kernel.py positive                                   # 原 positive 盒
py -3 -B py/integer_kernel.py stage3                                     # stage2200 最紧 3 盒
py -3 -B py/integer_kernel.py stage ../../../evidence/hubline-domain-stage2200.json 8   # 最紧 8 盒
py -3 -B py/integer_kernel.py stage <manifest.json> all                  # 全 manifest 逐盒重放（按盒 status）
py -3 -B py/integer_kernel.py hub <idx>                                  # 指定 stage2200 叶
```
证据日志：`logs/guard_selftest.txt`、`logs/positive.txt`、`logs/stage3.txt`、`logs/stage_tightest8.txt`
（每行含 atoms/total/status/boxes/max/gap + 标定计数 + max_d2_seen）。约 0.75 s / hub 盒，可用于 manifest 批跑。

## 5. 边界 / 未做

* 逐盒证书只断言该 hub 盒的 atomic 判据；**域覆盖/partition 的完整性**属于 wrapper（stage2200 的 leaf cover
  已由 `DOMAIN-AUDIT.md` 的体积+不交+递归三重检查覆盖）。
* 不处理 `infeasible` 三类分支（沿用 wrapper 归约）；不改 lead 的 float 核。
* 分辨率上限：ring 盒最小宽 16/S ≈ 2.4e-7；若某 hub 盒在此分辨率内 unresolved，会明确返回 `unresolved` 而非假证明
  （本次 11 个被检盒均 certified）。
* S 可调（20–28，类内 assert 保护）：若将来需要更细分辨率，S = 2^28 仍在 int64 内（`32S² = 2^61 < 2^63`）。

---

## 0. 结论（可判定）

| 对象 | 整数核结果 | 与 float 核记录 |
|---|---|---|
| 原 positive 盒 `s∈[199/1000,201/1000], x∈[0,1/1000], y∈[23/2000,27/2000]` | **certified**：boxes 11875 / leaves 5818 / outside 120 / max 32575800681 / total 325759278632 / gap 1271822 | 逐字段相同 |
| stage2200 最紧 3 盒（relgap 1.85e-11、8.56e-10、1.86e-9） | **certified ×3**：25425/12609/104/gap 6；7843/3780/142/gap 278；9265/4438/195/gap 605 | 逐字段相同 |
| stage2200 最紧 8 盒（追加 5 个） | **certified 8/8**，无一 unresolved/budget | — |

**判读**：在 S = 2^26、深度 ≤ 23 的设定下，纯整数（int64）距离判据能**独立**复现全部被检盒的证明状态，
包括相对间隙仅 **6/3.24e11 ≈ 1.9e-11** 的 #946；整数核与 float 核的盒数/叶数/最大权/间隙**完全一致**
（一致性只是观察，结论依据是整数算术本身的 out-of-range 方向与下限保证，见 §2）。
⇒ 这些证书**不再依赖 IEEE 浮点陈述**；可作为 manifest 级独立重放核（按盒逐个 `status`）。

---

## 1. 设计（严格按 lead 规格）

* **尺度**：`S = 2^26`；atom 精确有理坐标 rectangle 由 `records + H` **重建**（不用 float X 数组），
  下端 `floor(·S)`、上端 `ceil(·S)` 取整（outward）；`assert max|endpoint| ≤ 2S` ✓（实测 = `S`，只用了一半余量）。
* **ring 盒**：dyadic，DFS 深度 ≤ 23；端点以 1/S 为单位是**精确整数**（`(a+b)` 偶性断言 ✓），
  最小盒宽 ≥ 16 单位（= 16/2^26 ≈ 2.4e-7）。
* **距离**：`dx = max(Ax0−Bx1, Bx0−Ax1, 0)`（同 y），`d2 = dx²+dy²` 用 `np.int64`；
  `|diff| ≤ 4S`、`d2 ≤ 32S² = 2^57`（**实测 max_d2 = 1.679e16 ≈ 0.117·32S²**，距 2^63 约 550× 余量）。
* **阈值（精确有理→整数，方向关键）**：`U2_ceil = ceil(U²S²)`（计 capture 当且仅当 `d2 ≤ U2_ceil`）；
  annulus `inner_floor = floor((1−U)²S²)`、`outer_ceil = ceil((1−U²)S²)`，
  丢弃条件 `high < inner_floor` 或 `low > outer_ceil`（严格、保守方向）。
* **权重/筛选**：权重仍为 `round(W(θ)·1e9)` 的正整数；曝光筛选在**精确有理**里做
  （j=1: `U·c ≤ s_lo`；j=2: `U·c ≥ −s_lo`）；单位向量只从 `evidence/atomic-unit-vectors-2048.json` 读取（无 `tan`）。
* **整数和**：capture 用 int64 求和（`≤ total < 2^60` 断言 ✓；`10·total < 2^63` 断言 ✓），
  接受判据 `10·val < total` 在 Python 整数里比较（无溢出）。

## 2. 为什么它是证明（两个方向）

* **无假阳性（outside ⇒ 真距离 > U）**：整数 atom 矩形是精确矩形的 outward 扩张 ⇒ `dx,d2 ≤ 真 d²·S²`；
  故 `d2 > U2_ceil ≥ U²S²` ⇒ 真 `d² > U²` ✓。ANNULUS 同理：ring 盒端点在 1/S 网格上**精确**，
  `low/S², high/S²` 就是真 min/max 半径²，配合 floor/ceil 阈值 ⇒ 丢弃只在"证明不交 annulus"时发生 ✓。
* **无假阴性（真距离 ≤ U ⇒ 必被计入）**：真 `d² ≤ U²` ⇒ `d2 ≤ U²S² ≤ U2_ceil` ✓。
* 唯一 slack 是 atom 矩形的 outward 扩张（≤ 1 单位/坐标 ⇒ 平方距离最多降 ~6/S ≈ 9e-8）；
  实测在 4 类盒 × 10,000 随机 (盒, atom) 样本上 **outward-rounded overcounts = 0**（连 slack 内的超计都没有），
  **false negatives = 0**，**shell violations = 0**。

## 3. 自检（每次运行都跑）

`py/integer_kernel.py` 内建：`max|endpoint| ≤ 2S`、ring 端点/中点精确性、`d2 ≤ 32S²`、
`total < 2^60`、`10·total < 2^63`；外加 Fraction 标定（随机 dyadic 盒 depth ≤ 23 × 随机 atom，双向）
——本次所有运行均为 `fn=0, ov=0, bad=0`。

## 4. 复现

```powershell
cd research-2026/n12-global/members/upper-audit/integer-atomic
py -3 -B py/integer_kernel.py positive                                   # 原 positive 盒
py -3 -B py/integer_kernel.py stage3                                     # stage2200 最紧 3 盒
py -3 -B py/integer_kernel.py stage ../../../evidence/hubline-domain-stage2200.json 8   # 最紧 8 盒
py -3 -B py/integer_kernel.py stage <manifest.json> all                  # 全 manifest 逐盒重放（按盒 status）
py -3 -B py/integer_kernel.py hub <idx>                                  # 指定 stage2200 叶
```
证据日志：`logs/positive.txt`、`logs/stage3.txt`、`logs/stage_tightest8.txt`（每行含 atoms/total/status/boxes/max/gap + 标定计数）。
约 0.75 s / hub 盒（3511–5534 atoms ⇒ 8 盒 7.4 s），可用于 manifest 批跑。

## 5. 边界 / 未做

* 逐盒证书只断言该 hub 盒的 atomic 判据；**域覆盖/partition 的完整性**属于 wrapper（stage2200 的 leaf cover
  已由 `DOMAIN-AUDIT.md` 的体积+不交+递归三重检查覆盖）。
* 不处理 `infeasible` 三类分支（沿用 wrapper 归约）；不改 lead 的 float 核。
* 分辨率上限：ring 盒最小宽 16/S ≈ 2.4e-7；若某 hub 盒在此分辨率内 unresolved，会明确返回 `unresolved` 而非假证明
  （本次 11 个被检盒均 certified）。
* S 可调（20–28，`assert` 保护）：若将来需要更细分辨率，S = 2^28 仍在 int64 内（`32S² = 2^61 < 2^63`）。
