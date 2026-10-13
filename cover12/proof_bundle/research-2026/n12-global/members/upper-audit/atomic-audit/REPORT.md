# ATOMIC-AUDIT · `lead/hubline_atoms.py` + `hubline_atoms_fast.py` 独立核审报告

成员 `upper-audit`（子目录 `atomic-audit/`），2026-09-26。写域：`members/upper-audit/atomic-audit/**`。
**未改** `lead/**`、未覆盖任何 evidence（只读 `lead/hubline_*.py` 与 `evidence/hubline-atoms-1-1000-2048.json`）。
被审对象：H: `s∈[199/1000,201/1000]`、`x∈[0,1/1000]`、`y∈[23/2000,27/2000]`，`N=2048`，
记录证据：status certified、4858 atoms、11875 boxes、5818 leaves、120 outside、
`maxcap=32575800681`、`total=325759278632`、`gap=1271822`。

---

## 0. 结论速览

| # | 结论 | 等级 |
|---|---|---|
| C1 | **快的核（PAD=2^-42 绝对误差护栏）严格可用**：重推误差链得总误差 ≤ **1.865e-14 < 2^-45**（docstring 未列最后 `−PAD` 的舍入 ≤2^-48，补上后仍成立），到 PAD 的余量 **12.19×** | [已核对·纸面] |
| C2 | 「float 说 outside ⇒ 精确距离² > U²」方向**零违反**：记录配置上 worst leaf + 4 随机叶 + 4 随机丢弃盒 + 6 随机盒，每盒 4858 atoms 全查 ⇒ 0 失败；实测 `min(S−D) = 2.264e-13 ≥ PAD−err = 2.087e-13`（与理论预测一致） | [已核对·精确] |
| C3 | 快核与 directed 核**逐项同值**（certified/11875/5818/120/32575800681/325759278632/1271822）——仅作一致性检查，**结论不依赖**此项 | [已复现·一致性] |
| C4 | 区间原语（`bounds/add/sub/square/norm2`，`nextafter` 版，快核继承的 `bounds`）对精确 Fraction **0 违反**（3013 bounds + 6000 add/sub + 6000 square/norm2） | [已核对·精确] |
| C5 | 整数权：exact python 总权 = 325759278632 = 记录值；`<2^60` ✓、`10·total < 2^63` ✓、numpy int64 和 = exact ✓；快核 per-box 和 ≤ total 无溢出 | [已核对·精确] |
| C6 | 域完整：DFS 终止盒的**面积和 = 4 精确成立**（根盒 [−1,1]² 面积 4）；120 个丢弃盒**全部精确不交** annulus；根盒 ⊇ annulus（√(1−U²)<1 精确） | [已核对·精确] |
| C7 | atom 曝光筛选：4858 个保留 atom 逐点验证 `U·c ≤ s_lo`（j=1）/`U·c ≥ −s_lo`（j=2）**精确成立**（0 失败）——这恰是"对所有 s∈[sl,sh] 都暴露"的充要充分条件；moving-circle witness：每 atom 的精确位置范围（对 hub 盒）**含于**核用的 float 区间（4858/4858） | [已核对·精确] |
| C8 | 权重整数化：`round(W(θ_j)·10^9)` 与记录**逐个一致**（0 mismatch）；2048 个 stereographic 点满足 `c²+s²=1` **精确**（无超越数进入坐标） | [已核对·精确] |

**判读**：C1–C2 支持"把 nextafter 换成 PAD 护栏"的**严谨性**（不是靠 same-boxes）；C4–C8 覆盖 lead 列出的四项义务。
**两条卫生项**：(H1) docstring 的误差链缺最后 `−PAD` 的舍入项（≤2^-48），补上后 1.865e-14 < 2^-45 ✓（建议写进 docstring）；
(H2) 一次性审计的 4 个随机"丢弃盒"中有一个 `10·exact ≥ total`——**无害**（丢弃盒与 annulus 不交，不含任何 ring 中心；证书只要求 annulus 内的叶盒满足不等式），但读日志时勿误读。

---

## 1. 快核护栏的逐项重推（C1）

`hubline_atoms_fast.bound` 的全部运算与量级（`|端点|≤2` 的 assert 成立，实测 atom 端点 max = 1.000000，
DFS 盒端点在 [−1,1]）：

| 步骤 | 运算 | 量级 | 绝对误差界 |
|---|---|---|---|
| 差 | `X0−b`, `a−X1` | ≤4 | ≤ ulp(4)/2 = 2^-51（各一） |
| `max(·,0)` | 精确 | — | 保误差 |
| 平方 | `dx*dx` | dx≤4 ⇒ ≤16 | ≤ 8·2^-51 + 2^-102 + 2^-49 |
| 求和 | `dx²+dy²` | ≤32 | ≤ 2^-48 |
| **`−PAD`** | `fl(s−PAD)` | ≤32 | ≤ 2^-48（**docstring 未列**） |

⇒ 总误差 ≤ 2(2^-51 + 8·2^-51 + 2^-102 + 2^-49) + 2^-48 + 2^-48 = **1.865e-14 < 2^-45 = 2.842e-14 < PAD = 2.2737e-13**（余量 12.19×）。
annulus 分支同理（端点 ≤1 ⇒ 误差更小）；`+PAD` 侧的上界方向亦成立（high ≥ 真 max + PAD − 2^-46 ≫ 真 max）。

**两个方向都成立**：
* 「not possible ⇒ 精确 > U²」：`d2 ≤ S + err − PAD`，`d2 > r2[1] ≥ U²` ⇒ `S > U² + (PAD − err) > U²` ✓；
* 「精确 ≤ U² ⇒ 必被计入」：`d2 ≤ S + err − PAD ≤ U² − (PAD−err) < U² ≤ r2[1]` ✓。
有效性还依赖（已在别处核实）：`r2[1] ≥ U²`、`inner[0] ≤ (1−U)²`、`outer[1] ≥ 1−U²`（`bounds` 外扩 ✓）；
atom 端点由 `bounds` 做**精确有理→binary64 外扩**（C4/C7 ✓）；IEEE 正确舍入的基本 +/−/* 且无 FMA 缩并
（numpy ufunc 逐次调用 ✓）、无 subnormal/溢出（量级 ~1 ✓）。**结论：护栏严谨，可用。**

---

## 2. 四项义务的核对（C4–C8）

**(A) 区间原语**：`bounds(q)`（含 0、U、U²、(1−U)²、1−U²、10^±300、2^-1074、随机有理）0 违反；
`add/sub` 对精确和有向包含 0 违反；`square/norm2` 对**作为输入传递的 binary64 端点**取精确 min/max 0 违反
（注：首轮 61 个"违反"是**我控制件自己的错**——我把精确有理端点和实际传入的 float 端点混用了；
修正为按 float 端点算精确 min/max 后为 0，日志里保留这一更正说明）。

**(B) 整数权/溢出**：见 C5；快核 `W[d2<=r2[1]].sum()` 的 int64 和 ≤ total < 2^60 ✓。

**(C) dyadic 盒 + annulus 域**：DFS 与核同规则复现，终止盒面积和 = 4（精确 Fraction）⇒ 覆盖 [−1,1]² 完整；
120 个 annulus 丢弃全部"精确不交"；根盒覆盖 annulus（`√(1−U²) < 1` 精确）。

**(D) exact atom 曝光筛选 + moving-circle witness**：
* 曝光等价式（j=1）：`|atom−h₂|² = U² + 4s² − 4Ucs ≥ U² ⟺ s ≥ Uc`；对盒内所有 s 的充分条件 = `Uc ≤ s_lo` ✓（j=2 同理 `Uc ≥ −s_lo`）。
  4858 个保留 atom 全部满足（0 失败）⇒ 对**每个** hub 位置都落在暴露弧上 ✓。
* witness 全域性：atom 精确位置范围 = `(xl−sh+Uc, xh−sl+Uc)×(yl+Us, yh+Us)`（j=1）等，全部含于核的 float 区间 ✓；
  结合"capture 计数用位置区间 + 盒"⇒ 计数对**整个** hub 盒与**整个** ring 盒一致上界 ✓。

---

## 3. 证据与复现

| 文件 | 内容 |
|---|---|
| `py/atomic_exact_audit.py` → `logs/atomic_exact_audit.txt` | (A)(B)(C)(D) 全套：原语/Fraction 控制、atom/权/screen、DFS 面积=4、annulus、top-leaf 精确重算、outside 方向 |
| `py/fast_kernel_audit.py` → `logs/fast_kernel_audit.txt` | 快核 PAD 误差链重推、22 个真实盒 × 4858 atoms 精确对照、`min(S−D)` 实测、快核复现值 |

```powershell
cd research-2026/n12-global/members/upper-audit/atomic-audit
py -3 -B py/atomic_exact_audit.py 3000 > logs/atomic_exact_audit.txt 2>&1     # ~8 s
py -3 -B py/fast_kernel_audit.py          > logs/fast_kernel_audit.txt 2>&1    # ~3 s
```

## 4. 未做 / 边界

* 未重做全域 10k 盒扫描（lead 的生产者任务）；本审计只判"护栏与逻辑可用"，不代替全域跑。
* 全域跑时的注意：`|端点|≤2` 与 `total<2^60` 两个 assert 必须继续成立（新 hub 盒若把端点推过 2 会**硬崩**而不是降级，属好事但需知道）；
  丢弃盒的 capture 计数可以任意大（§0 (H2)），不得据此判"证据无效"。
* 本审计不覆盖 k10 归约本身（暴露边界引理、annulus 域来源等）——那些是 lead/twohub 的承重前提，沿用原 scope。
