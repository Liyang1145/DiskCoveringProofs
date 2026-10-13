# STATUS · upper-audit / atomic-audit（lead 原子核 `hubline_atoms[_fast].py` 独立核审）· 2026-09-26

写域：`members/upper-audit/atomic-audit/**`。未改 `lead/**`、未覆盖 evidence。报告：[REPORT.md](REPORT.md)。

## 一句话

**核审通过（认可）**：快核的绝对误差护栏 `PAD=2^-42` 严谨（重推总误差 ≤1.865e-14 < 2^-45，到 PAD 余量 **12.19×**，
docstring 需补最后 `−PAD` 的 ≤2^-48 项）；四项义务（区间原语/整数权无溢出/dyadic+annulus 域完整/exact 曝光筛选+witness）
在记录配置上 **0 违反**，且「float 说 outside ⇒ 精确 >U²」方向经 22 个真实盒 × 4858 atoms 精确对照 0 失败
（实测 `min(S−D)=2.266e-13 ≥ PAD−err=2.087e-13`，与理论预测一致）。

## 关键读数

| 项 | 读数 |
|---|---|
| 误差链 | 2(2^-51 + 8·2^-51+2^-102+2^-49) + 2^-48 + 2^-48 = 1.865e-14 < 2^-45 < PAD（余量 12.19×） |
| 原语精确控制 | bounds 3013 + add/sub 6000 + square/norm2 6000 → **0 违反** |
| 整数权 | exact 总权 325759278632 = 记录；`<2^60` ✓、`10·total<2^63` ✓、int64=exact ✓ |
| 域完整 | DFS 终止盒面积和 = **4 精确**；120 个丢弃盒**全部精确不交** annulus |
| 曝光筛选 | j=1 等价式 `s ≥ Uc` ⇒ 充分条件 `Uc ≤ s_lo`；4858 保留 atom **0 失败**；位置范围 4858/4858 含于核区间 |
| 权重整数化 | `round(W·10^9)` 逐个一致（0 mismatch）；2048 点 `c²+s²=1` 精确 |
| 一致性（仅参考） | 快核输出与 directed 核记录逐项同值（11875/5818/120/32575800681/325759278632/1271822） |

## 未决 / 注意

- 全域 10k 盒跑是 lead 的生产者任务；本审计只判"护栏+逻辑可用"。`py/fast_audit_reusable.py <eps> <N>`
  已就绪，可在新配置上复做 top-leaf × all-atoms 精确对照（本次 `1-1000 2048` → RESULT: PASS）。
- 全域跑前提：`|端点|≤2` 与 `total<2^60` 两个 assert 须继续成立；丢弃盒 capture 可任意大（**勿**据此判证据无效）。
- 未覆盖 k10 归约/暴露边界引理本身（沿用原 scope）。
