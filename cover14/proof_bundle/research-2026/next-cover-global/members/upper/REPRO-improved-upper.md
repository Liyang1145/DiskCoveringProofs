# n14 · 改进上界对象复核（lead improved-upper-test.json）

成员 `upper-audit`（写域 `research-2026/next-cover-global/members/upper/**`），2026-09-26。
对 lead 资产**只读**（未运行旧核 `main()`、**未**写旧域、未改任何上游文件）。
**本件纯 given-centers**：root 方程 / `root_scout.py` / `root-scout.json` 的**数学原理不在本件范围**，也未作为前提使用。

---

## 0. 结论

| 项 | 结果 |
|---|---|
| 旧 isqrt BOX 核复现 | `analyse(C, T, grid=False)`：**候选盒 507、uncovered = 0**，argmax = `circum0,4,12` ⇒ `R(C) ≤ T` 由**旧核**独立确认 |
| 独立精确核（有理代数，无区间/无 float 判定） | 同一 (C, T)：**0 uncovered** ⇒ 与旧核一致 |
| 新对象精确半径 | argmax = 有理外心 `circum0,4,12`；`R_new = sqrt(q_new) = 0.3317320342762341225578155488024095382709427548290174780628283474770834…` |
| 与 lead 数字一致 | `R_new` 与 lead 报的 numeric `.3317320342762341225578` **逐位一致** |
| 精确改进量 | `T² < q0_old` ✓（`T < R_old`）；**`R_old − T = 9.155066e-19`**（与 lead “约9.15e-19”一致）；`R_old − R_new = 9.576911e-19`；`T − R_new = 4.218445e-20 > 0` |
| 旧域写检查 | 运行前后 `lead/c407_lead_result.txt` sha256/mtime **未变** ✓ |
| 口径 | **只是这一条有理构型的上界**；**不最优**；不是族内最小值，也不是 `r_D(14)` |

## 1. 出处（SHA256，全部只读）

| 对象 | SHA256 |
|---|---|
| `next-cover-global/lead/improved-upper-test.json` | `16D99E074FEFEECF463D1F3806B0470AF6666810790167B9655D74190A938892` |
| `next-cover-global/lead/root-scout.json` | `F2DCBE7507ACAAFDF7DFD57DC69B878D76914F7A2D3523214D19B32C28B4A60E` |
| `next-cover-global/lead/root_scout.py` | `9BCC8850F7D111301379A00412E38ACCB3A62BF657AEDD709D90314C0B38AECB` |
| 旧 box 核 `lead/verify_c407_lead.py` | `A728DD3D6C4C6D466923D01E09C2AE918ACE0C2325DF45E1D8F675C71066596F` |
| C411 字面对象 `session2/type14/out/hprec_sol.json` | `7689E60BDD2ECC8B54B589A3A30850E6A85040CA120C00BEA225763753B9448A` |
| 本件脚本 `py/repro_improved_upper.py` | 见 `hashes.txt` |
| 本件日志 `logs/improved_upper_result.txt` | 见 `hashes.txt` |

## 2. 被复核对象的原文（verbatim）

* `status = exact-rational-cover-test`；`scope = specific rational configuration upper bound only`
* `threshold = 1658660171381170613/5000000000000000000 = 0.3317320342762341226`（19 位小数，**精确有理**）
* `centers` = **14 个精确有理分数**（本件逐字读取，未做任何再生成/舍入；`|coord| ≤ 1.3317` 校验 True）
* 文件自报 `candidate_count = 493`、`uncovered = []`

## 3. 复现 1：旧 isqrt BOX 核（`analyse(C, T, grid=False)`）

以 `importlib` **仅导入**只读旧核模块（模块级只定义路径与函数；`main()` **未调用**），调用其 `analyse`：

```
candidates (boxes) = 507 ; uncovered = 0
R(C) enclosure     = [0.33173203427623410011, 0.33173203427623410011]   (10^-40 directed isqrt)
argmax(lo)=argmax(hi) = circum0,4,12
grid cross-check: skipped (grid=False, as instructed)
```
判别含义：**每个候选盒**都被半径 `T` 的某一个盘整盒覆盖 ⇒ 候选点（因而在完备性前提下整个 D）被覆盖 ⇒ `R(C) ≤ T`。
（候选盒数 507 与 C411 时相同——**同一套枚举**、同一 14 心结构；本件不重审完备性，沿用 §REPRO-C411 §4 的结论。）

## 4. 复现 2：本成员独立精确核（第二条独立通路）

同一 `(C, T)` 用纯有理代数判定（`α + B√q ≤ T²` 分符号平方，无 isqrt/无区间/无 float）：
**0 uncovered**。⇒ 两条不同表示的通路都给出 `R(C) ≤ T`。

## 5. 精确量（全部有理比较，无浮点）

* 新对象精确半径：argmax 为**有理**外心 `circum0,4,12`，`q_new = R_new² ∈ Q`；
  `R_new = 0.3317320342762341225578155488024095382709427548290174780628283474770834…`
* `T² < q0_old`：**True**（等价 `T < R_old = 0.3317320342762341235155066403893542386599009287817317893317705660612302…`）
* `q_new < q0_old`：**True**（新构型严格更优）
* `T² − q_new > 0`：**True**（阈值在**新对象半径之上**，这是覆盖判定能通过的原因）
* 改进量（由平方差换算，分母用半径和）：
  * **`R_old − T = 9.155066e-19`** ←与 lead 口径一致
  * `R_old − R_new = 9.576911e-19`
  * `T − R_new = 4.218445e-20`

## 6. 附注（非承重）

* `root-scout.json` 的 `z_c_r[2]`（numeric_only 的 r）字符串 `0.3317320342762341225578155488024095382709427548290174780628283469118412`
  与被复核对象的**精确** `R_new` 前 ~64 位一致，末几位不同（差 ~6e-71，量级即"数值根 vs 精确化后构型的实际半径"之差）。
  这只是元数据口径提示；**本件不依赖也不评价** root 方程。
* 旧核 `R(C) enclosure` 打印出的两段同一 double 数字并非"零宽度区间"，见 `REPRO-C411.md` §5.4 的解释。

## 7. 复现命令

```powershell
cd research-2026/next-cover-global/members/upper
py -3 -B py/repro_improved_upper.py      # 旧 box 核（import-only）+ 精确核 + 精确比较；1.5 s
```
日志：`logs/improved_upper_result.txt`（本件结果）、`logs/improved_stdout.txt`（控制台）。
