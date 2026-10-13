# members/stress-audit/atomic-final-audit — STATUS

Lead 指派的 k10 高风险义务（2026-09-27）：冻结整数原子核的**独立表示**审计 + 控制叶 4398 @ 2^28。
范围内只做关键核数学/表示审计，**非** 6723 叶全队列重放。写域仅本目录。

## 结论（已交付 = REPORT.md）

- 未发现影响 certified 的可靠性缺陷；核内 7 条判据方向逐条成立（D1–D8，含 8 个 annulus 严格性探针、
  1500 组 (atom,box) 对照 0 假阴性、4 个负/完整性探针）。
- 控制叶 4398：我的 exact-Fraction 重建 atoms=4778/demand=325879733812 与记录逐位一致；
  记录中 2^26 capture=32608767913 独立复现；冻结核 2^28 重跑与 escalated-scale28-evidence 的 scale_28_result 逐位一致。
- 三项发现（C1136，gap）：F1 快照存储计数不可复现且缺 scale（provenance）；F2 `depth` 字段在 2^28 不可信；
  F3 `screen=False` 非证书级（建议绑定）。三者都不影响叶 4398 的数学结论。
- 外部前提 P-a…P-d 按 lead 文档引用，未重证；建议 P-a 的 D∩ 包含条款写成显式承重引用。

## 台账

C1134 (proved, 核内方向审计) / C1135 (proved-exact, 控制叶数字) / C1136 (gap, 口径与绑定发现)。

## 复现

```
$env:PYTHONIOENCODING='utf-8'
py -3 -B members/stress-audit/atomic-final-audit/py/fraction_control_4398.py
py -3 -B members/stress-audit/atomic-final-audit/py/integrity_probes.py
```

## 未决 / 可接后续

全 6723 叶源绑定重放（属 obligation D 的 finite-reduction 侧）；partition/frontier 独立复核；其他 pending 叶的同类独立控制。
