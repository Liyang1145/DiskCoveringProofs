# STATUS · upper-audit / integer-atomic（纯 int64 距离核）· 2026-09-26

写域：`members/upper-audit/integer-atomic/**`。未改 `lead/**`、未覆盖 evidence。报告：[REPORT.md](REPORT.md)。

## 一句话

**纯 int64（S=2^26、深度≤23）独立距离核已实现并自检通过**：原 positive 盒 + stage2200 最紧 3 盒（含
relgap 1.85e-11 的 #946）+ 最紧 8 盒 **全部 certified**，且与 float 核记录的 boxes/leaves/outside/max/total/gap
**逐字段相同**；距离路径无 float、无 tan（单位向量只读 canonical2048）；证明方向由 outward floor/ceil 与
精确整数阈值保证，配 Fraction 双向标定 0 失败。⇒ 该阶段证书**不依赖 IEEE 浮点陈述**。

## 关键读数

| 项 | 读数 |
|---|---|
| positive 盒 | certified：11875 / 5818 / 120 / max 32575800681 / total 325759278632 / gap 1271822 |
| 最紧 3 盒 | #946 gap **6**（25425 盒）；#975 gap 278；#132 gap 605 — 均 certified 且与 float 核同值 |
| 最紧 8 盒 | certified **8/8** |
| int64 界（实测） | max\|endpoint\| = S（cap 2S）；max_d2 = 1.679e16 = 0.117·32S²（32S²=1.44e17；距 2^63 ≈ 550×） |
| 标定 | 每盒 10,000 样本：false negatives 0 / outward overcounts 0 / shell violations 0 |
| 内建 assert | 端点≤2S、ring 中点精确、d²≤32S²、total<2^60、10·total<2^63 |

## 复现

```powershell
cd research-2026/n12-global/members/upper-audit/integer-atomic
py -3 -B py/integer_kernel.py positive
py -3 -B py/integer_kernel.py stage3
py -3 -B py/integer_kernel.py stage ../../../evidence/hubline-domain-stage2200.json 8
py -3 -B py/integer_kernel.py stage <manifest.json> all   # 全 manifest（由 finite-reduction 负责）
```

## 状态：已冻结（等 finite-reduction 完整 run）

- **source 冻结**：`py/integer_kernel.py` SHA256 `0115C3F3660382CC5BCC53C1FAF287FF624CA2F2C649A02035B7494759C0FC50`；
  `py/guard_selftest.py` `D89F9F49720A02D637153F0268F2B9D85F63CC98973769EB87D466484C70D687`。
  **不再改动**，等 finite-reduction 用同 hash 跑全 manifest。
- **全 stage2200 重放已按 lead 指示停止**（避免同核同输入重复、避免与 run3 抢 CPU）：partial 日志
  `logs/stage_all_PARTIAL_STOPPED.txt`（120 行样本，全部 certified、标定 `fn=0,ov=0,bad=0`）+ 说明 `…STOPPED.md`。
  **不得**引用为"全叶完成"；该义务由 finite-reduction 承担。

## N 泛化模块（新增独立文件；冻结文件未动，缓存继续有效）

- `py/integer_kernel_n.py` SHA256 `A89A2CEE8DCBCF4DD7585B6878A6AD48A2DB6543C109473936E08096A7085D53`
  （`import integer_kernel` 复用其 `bound`/`certify` ⇒ **这两部分明确非独立**；构造、前提 guards、溢出检查独立重写）。
- 向量文件（members scope；evidence 不可写）：
  `evidence/canonical-unit-vectors-8192.json` SHA256 `E2FE3E7D6F0AB37587E83A9214B1ABBE1127F8A83593732DE1A584D88B7FB77A`（8192 点，逐点 c²+s²=1 精确）；
  `evidence/canonical-unit-vectors-2048.json` SHA256 `7E809EA2AF5E012D6E802EE15ADE8B1A0B645E0CE17F641E41F67228DF779137`（与 evidence 版 canonical2048 **逐元素相同**）。
- **N=8192 纯 int 复核 two-hub 保存证**（源 `two-hub/proposal-repair/N_scan.json` 的 H + `weights_o6`；该文件 SHA256 `0A6630F42B89D802FEE10F3F4C031FF0757D4EA1B6118861E067B31D8E3E5192`）：
  逐字段复现 FastAtoms 记录 certified：boxes 16911 / leaves 8334 / outside 122 / max 130169221852 / total 1301696319067 / gap 4100547 / atoms 18886（`logs/n8192_check.txt`）。
- API：`IntAtomsN(H, weights, vectors, Sexpt=26)`，`vectors` 可传 **整数 N**（自动读/生成 members 目录向量文件）、
  **json 路径**、或**显式向量 list**；`bound`/`certify` 语义与冻结版一致；`A.N` = 向量数。CLI：`vectors <N>`、`check-n8192`、`selftest`。

## scale-28 源审（新；只读，冻结核未动）

- 报告：`audit-scale28.md`；短小独立检查 `py/audit_scale28_checks.py`（SHA256 前缀 `18C09ADD94E50197…`，
  文案修正后重跑），日志 `logs/audit_scale28_checks.txt`（**ALL CHECKS PASS**，1.8 s，无大规模重放）。
- 结论：**S=2^28 int64 安全成立**（实际最坏 d²≤18S²=1.297e18，断言上限 32S²=2.306e18，均 <2^63；7.11×/4.00× 余量）；
  阈值逐位精确；`10·val<total` 走 Python 大整数、strict gap ≥1（三叶 gap 674622/2959381/300128>0）；
  exposure 恒等式 `dist²−U²=4s(s∓Uc)` 精确、保留方向（充分性）在 [s_lo,s_hi] 上 0 反例；annulus discard 严格方向 0 反例。
- **26→28 翻转机制已复算**：idx 4398 记录盒重算 bound = 32608767913 = 记录 cap **逐位相同**；
  同实盒 ×4 抬到 28 ⇒ bound 32477300738，10·bound<total（余 1.107e9）⇒ 纯分辨率效应。
- **口径澄清（lead 指正后修正）**：单坐标分裂次数 = `Sexpt−3`（26→23、28→25；先前误写 `Sexpt−1`）；
  DFS 每步只裂一轴 ⇒ 路径步数上限 `2(Sexpt−3)`（26→46、28→50）。
- **缺陷 D1（非可靠性）**：`certify(max_depth=23,…)` 的 `max_depth` 只被回显、不参与停止判据 ⇒
  28 尺度若出 unresolved，其 `depth` 字段会写 23（与 `Sexpt−3=25` 不符，错值）。不影响 certified。
- **exposure 措辞（lead 指正后修正）**：保留条件是"对 relaxed H 区间充分"，**不是**对 legal 子集的必要性；
  被丢弃原子只在 `s = s_lo`（可能非法）处严格在内 ⇒ 丢弃只是**保守少收需求**，不得表述为"保留不安全"。
- **接口前提**：annulus 两条 discard 依赖上游归一化前提；`assert H[0][0] >= 0` 文案写 `[0,U]` 但只查 s_lo≥0；
  尺度必须与证书绑定（26/28 互为不同对象，不可互相代用）。

## 未决 / 注意

- S 可调 20–28（`S=2^28` 时 32S²=2^61 < 2^63，若需更细分辨率）；ring 最小盒宽 16/S ≈ 2.4e-7，
  超限会返回 `unresolved` 而非假证明。
- 只审逐盒 atomic 判据；域覆盖/partition 完整性属 wrapper（stage2200 已由 DOMAIN-AUDIT.md 三重检查覆盖）；
  未处理 infeasible 三类分支。
- 新 guard 抓到的**助手 bug 已修**（随机盒负数取模 → 改索引构造），与核逻辑无关；finite-reduction 若写随机标定需注意同一点。
