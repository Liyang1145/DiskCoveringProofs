# DOMAIN-AUDIT · `hubline-domain-stage2200.json` 的 leaf partition + 最脆弱 hub 盒的 all-atom 精确控制

成员 `upper-audit`（子目录 `atomic-audit/`），2026-09-26。写域 `members/upper-audit/atomic-audit/**`；
只读 `lead/**` 与 `evidence/**`，未改任何外部文件。被审：`evidence/hubline-domain-stage2200.json`
（**partial**，processed=2200，certified(atomic)=1021，infeasible=76，pending=7，split=1103）。
误差界/PAD 论证见 [REPORT.md](REPORT.md) §1（本文不重复）。

---

## 0. 结论

| # | 结论 | 数值 | 等级 |
|---|---|---|---|
| P1 | 终止盒（1097 leaves + 7 pending = **1104**）的有理体积和 **逐字等于**根盒体积（精确 Fraction） | 相等 | [已核对·精确] |
| P2 | 1104 个终止盒**两两内部不交**（flat 表示、精确比较，O(n²) 全对枚举） | 0 重叠 | [已核对·精确] |
| P3 | 独立递归下降（最宽边分裂、并列取最小下标）**恰好到达全部 1104 个终止盒且各一次**，内部节点数 = 1103 = 记录的 `split` | 1104/1104 | [已核对·精确] |
| P4 | 所有终止盒含于根域内 | 0 失败 | [已核对·精确] |
| P5 | canonical 单位向量文件（2048 点）**逐点 c²+s²=1 精确**，且与平台 `tan` 生成器**逐元素相同**（⇒ 重放输入无平台依赖，且未改动 atom 集合） | 2048/2048 | [已核对·精确] |
| P6 | 按 `gap_integer/total` 最小的 3 个 hub 盒，其内层 ring DFS **逐字段重放一致**（boxes/leaves/outside/max/total/atoms 全同） | 3/3 | [已复现·一致性] |
| P7 | 对上述每个 hub 盒的 **top ring leaf** 做 **all-atom Fraction** 控制：精确计数 == float 计数；`10·精确 < total` 成立；「float 说 outside ⇒ 精确 S > U²」0 失败；`min(S−D) = 2.267e-13 ≥ PAD−ERR = 2.087e-13` | 3/3 | [已核对·精确] |
| P8 | **最脆弱叶(#946)的整数间隙是精确的**：精确计数给 `total − 10·exact = 6`（= 记录 `gap_integer`），非浮点伪影；#975、#132 分别给 278、605 = 记录值 | 6 / 278 / 605 | [已核对·精确] |

**判读**：stage2200 的 leaf cover 在"体积+不交+递归覆盖"三种不同表示下都精确成立；
被选出的 3 个最脆弱 hub 盒（relgap 1.85e-11、8.56e-10、1.86e-9）的原子证书在**全原子精确算术**下成立，
且间隙值与记录逐位一致。**注意**：这是 partial stage，不是全域证明；#946 的相对间隙 ~1.9e-11（6/3.24e11）
意味着该处**几乎没有余量**——证书有效，但对 atom 集/权重的任何改变都敏感（换分盒会让该 hub 盒的原子集变化）。

---

## 1. PART 1：三种表示的 leaf partition

* **体积记账**：`root 3-D volume = Σ terminal volumes`（精确有理数，打印见 `logs/domain_leaf_audit.txt`）✓。
* **flat 不交**：1104² /2 对全枚举，判据 `∀k: max(lo_i,lo_j) < min(hi_i,hi_j)`（严格 ⇒ 内部相交）；**0 对相交** ✓。
* **独立递归**：从根盒按 `j = max(range(3), key=width)`（并列取最小下标）分裂到终止集；
  `reached = 1104/1104`、每盒恰一次、`splits = 1103` = 记录 `counts['split']` ✓（说明记录的 split 计数与 partition 树一致）。
* 与 `replay_hubline_domain.py` 的树式检查**互为不同表示**（它递归、我体积+flat；两者都通过）。

## 2. PART 2：最脆弱 hub 盒的 all-atom Fraction 控制

选取规则：对 1021 个 atomic hub 盒按 `relgap = gap_integer / total_integer_demand` 升序取前 3。

| hub 盒 | relgap | atoms | 记录 result | 重放一致 | top ring leaf 精确控制 |
|---|---|---|---|---|---|
| #946 | **1.850e-11** | 3511 | boxes 25425 / leaves 12609 / outside 104 / max 32431389509 / total 324313895096 / gap 6 | ✔ | float==exact=32431389509；`10·exact < total` ✓；outside 方向 0 失败；`min(S−D)=2.2671e-13 ≥ PAD−ERR=2.0872e-13` |
| #975 | 8.560e-10 | 4974 | 7843 / 3780 / 142 / 32476113316 / 324761133438 / 278 | ✔ | float==exact=32476113316；✓；0 失败；2.2670e-13 |
| #132 | 1.862e-09 | 3581 | 9265 / 4438 / 195 / 32499205431 / 324992054915 / 605 | ✔ | float==exact=32499205431；✓；0 失败；2.2672e-13 |

* **精确间隙**：`total − 10·exact_cnt` = **6 / 278 / 605** = 各自记录的 `gap_integer` ✓ ⇒ 记录的间隙是精确整数量，不是浮点巧合。
* atom 位置范围与曝光筛选均用精确有理（j=1: `[xl−sh+Uc, xh−sl+Uc]×[yl+Us, yh+Us]` 等；筛选 `Uc ≤ s_lo` / `Uc ≥ −s_lo`）；
  本 stage 的 3 个盒全部通过（0 失败）。
* canonical 向量替换 `A.units` 后重放（与 `replay_hubline_domain.py` 同法，只在本进程 monkey-patch）✓。

## 3. 证据与复现

| 文件 | 内容 |
|---|---|
| `py/domain_leaf_audit.py` → `logs/domain_leaf_audit.txt` | PART 1（体积/flat 不交/递归）+ PART 2（3 个 hub 盒重放 + top leaf 全原子精确控制） |
| `py/hubbox_leaf_control.py` → `logs/hubbox_leaf_control*.txt` | **可复用**：`py -3 -B py/hubbox_leaf_control.py [stage.json] [索引\|min]`——对任意冻结 stage 取一个 atomic leaf，重放内层 DFS 并对 top ring leaf 做全原子精确控制（run3 落地后可直接用；已测 `min`→leaf#946 PASS gap=6、索引 `132`→PASS gap=605） |
| `py/fast_kernel_audit.py`、`py/fast_audit_reusable.py`、`py/atomic_exact_audit.py` → 同目录 `logs/` | 先前的原子核审计（PAD 误差界、原语、曝光、单点配置 all-atom 控制） |

```powershell
cd research-2026/n12-global/members/upper-audit/atomic-audit
py -3 -B py/domain_leaf_audit.py > logs/domain_leaf_audit.txt 2>&1     # ~5 s
```

## 4. 边界 / 未做

* 只审 **stage2200（partial）**：全域证明仍需 lead 的 run3 完成；本审计不主张全域。
* 未改原子核运算、未重复 PAD 误差界推导（引用 REPORT.md §1）。
* 未审 `infeasible` 三类 necessary-condition 的数学语义（那是 wrapper 的归约前提；`replay_hubline_domain.py` 已在实现层重放它们）。
* 敏感性提醒：#946 处 relgap ~1.9e-11；若 run3 的分盒使某 hub 盒的原子集变化，该处的间隙可能变负——但那样 DFS 会继续细分（`certify` 行为），不产生假证书。
