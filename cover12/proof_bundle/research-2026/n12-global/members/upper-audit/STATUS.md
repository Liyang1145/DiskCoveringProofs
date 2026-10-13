# STATUS · 成员 `upper-audit`（n=12 C182 源诊断 + D3 字面身份）· 2026-09-26

写域：`research-2026/n12-global/members/upper-audit/**`。未改共享 `STATUS.md`/`DEAD.md`/claims，未覆盖旧证据。
详细报告见本目录 [REPORT.md](REPORT.md)。

## 一句话

旧 `cover_n_uncovered=36` 与 REPORT `0/328` 的差异**已定论为域过滤口径差**（同一对象、同一阈值、同一候选族；
36 项全部是 D 外的近共线外心盒），D3 与 `centers_dec17` **逐坐标同一（0 差异）**；C182 单构型上界链
（D1 重放 + D2 区间 + 本成员独立精确复核）成立，等级仍是**单构型上界**，不是最优性。

## 已核对读数（等级见 REPORT §0）

| 项 | 读数 | 证据 |
|---|---|---|
| 36 语义 | 无域过滤候选未覆盖数；7 档 36/44/60/72/84/114/142 逐值命中；examples 逐字节一致 | `logs/cover_forensics.txt` |
| 36 位置 | 全为 `circ*`、36/36 与 D 不相交、`|p|²−1 ≥ 0.0151` | `logs/offender_profile.txt`、`logs/margins.txt` |
| 0/328 | 加域过滤后 328 盒中 0 未覆盖；checked 列 7/7 档对齐；§4 判别力 19/29/25 精确复现 | `logs/cover_forensics.txt`、`logs/threshold_sweep.txt` |
| 364−36=328 | 仅 n=12 行巧合（n=13: 44 vs 406, `455−44=411`） | 同上 |
| 并存证据 | `out/cert_all.json` 同文件含 flat `36` 与 nested `cover{328,0}`；`cert_batch.py` mtime 晚于 per-tag 输出 | REPORT §3 |
| D3 身份 | 24/24 坐标 `toFixed(17)` 整数 == JSON 字面整数；自报 14 是最短往返字面差异 | `logs/d3_ints_audit.txt` |
| D3 区间 | 与"直接跑原始字面整数"字符串相同；[..903,..904]，430 候选，filter_safe_halfdiag=true | 同上、`logs/c182-d3-official.txt` |
| D1/D2 重放 | bb_ok=true/8057/depth101；D2 [..903,..904] argmax bis5,10#0 | `logs/c182-d1-d2-replay.txt` |
| 独立复核 | 328 盒覆盖不等式失败 0（免 sqrt 平方比较）；余量 ≈4.5e-31（平方） | `logs/independent_cover.txt`、`logs/margins.txt` |

## 下一步（建议，不在本成员任务内）

1. 由独立成员以不同表述复核**候选族完备引理**（REPORT §6 的纸面副本）——这是单构型上界唯一的纸面承重步。
2. lead 若要入台账：把"36 = 无域过滤计数、0/328 = 域过滤计数"写成 DEAD 的**实现/诊断语义**条目
   （非数学判死），并保留 `candidate_coverage` docstring 方向错误的口径警示。
3. n=12 全局目标（下界/排除更小半径）仍为 gap；本次未触及。
