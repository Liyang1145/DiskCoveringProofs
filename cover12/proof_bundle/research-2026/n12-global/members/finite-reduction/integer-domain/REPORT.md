# integer-domain — 全 hub manifest 独立复核器（stage2200 / stage6700）

复核者：finite-reduction。**只读** Lead/evidence 源；只写本成员目录。承重计算**不用** mpmath/scipy 的浮点/区间（仅 core net 的 60 位取整鲁棒性检查用到 mpmath，非承重）。`U` 用精确字面。

## 结论（先说本质）

### stage6700（当前，`evidence/hubline-domain-stage6700.json`，sha256 `c5c9271e…a287`，与冻结值逐位一致 ✓）

| 环节 | 读数 |
|---|---|
| 结构（3 维、lo<hi、type∈{atomic,infeasible}、无重复 H、leaf/pending 不交） | **0 bad** |
| **精确 partition（独立 recursive tiling）** | `nodes=6705`、`visited_frontier=3353 == n_frontier`、`n_unresolved=0`、`exact_partition=true` |
| 非法叶 **274**（outer 20 / core witness 104 / bisector 150） | **全部独立复现**，reason 逐条一致 |
| prune3 与其 radical 形式（精确 isqrt +100bit） | **150/150 一致，undecided 0** |
| **atomic 叶重放** | **3074/3074 certified，0 非 certified**（**1021 命中 stage2200 缓存 + 2053 新算**） |
| 事后核 `check_results.py` | **all_pass=true**（行绑定当前四源 / 索引集精确 / 全 certified / summary 数字一致 / **无越权 global**） |
| **总体口径** | `verdict = complete-for-snapshot(partial frontier)`；`global_certificate = **false**`（snapshot 自身 pending **5** 盒） |
| 诊断 | 最小 gap **6**（idx 946），≤1000 的叶 5 个；`max_d2 ≤ 3.26e10` |

### stage2200（前一版，`hubline-domain-stage2200.json`，sha256 `fd7e2ac0…0ab7`）

| 环节 | 读数 |
|---|---|
| 结构 / 拓扑 | 0 bad；`exact_partition=true`（`nodes=2207`、`visited==frontier=1104`、0 unresolved） |
| 非法叶 76（outer 20 / core witness 43 / bisector 13） | 全部独立复现；prune3 **13/13**，undecided 0 |
| **atomic 叶重放** | **1021/1021 certified**；行绑定四源 hash，resume `preloaded_valid=1021` |
| **总体口径** | `complete-for-snapshot(partial frontier)`、`global=false`（pending 7 盒） |

**数值一致性（口径更正）**：我这边最小 gap 为 **6 / 278 / 605**，与 upper-audit 在新 hash 下跑出的"最紧 3 盒 gap 6 / 278 / 605"一致。**但这不构成独立实现的数学对照**：我与 upper 调用的是**同一个** `IntAtoms` 实现，故这只是**同一核的重复执行**（可作为回归/复现证据，不可作为独立性证据）。本条独立的部分是：manifest 的 **tiling / prunes / inference**（我自己的精确有理实现）；核层面的表示独立性只在"相对 Lead 的 float→int 翻译"这一意义上成立（由 upper 承担，我未重写核）。

## 承重设计（对应 Lead 的两轮指正）

1. **partition 不能用 containment+等体积**：重叠可补洞。改为**独立 recursive tiling**：从精确 root 起，盒要么是记录 frontier 盒，要么其最宽维两半的**精确有理中点**递归可解；并额外要求 `visited_frontier == frontier set`（无未用盒⟹无重复/重叠）且 leaf/pending 无重复、无交叉。当前 2207 节点全解。
2. **resume 绑定**：每行绑 `snapshot/units/kernel/atoms` 四 hash + `leaf_sha` + `atom_weight_sha`；预载逐行比对，不符计入 `rejected_by_binding`；certified 从合并后 `done` 重计；`idx_set_exact` = 恰为 `range(n_atomic)`；`global_certificate` 额外要求 pending 空 + `exact_partition`。resume 实测：`preloaded_valid=1021, rejected=0`（二次运行零重算）。
3. **持久化**：每 100 叶 `rep['atomic_replay']=…` 后**原子写**（tmp→`os.replace`）；JSONL 逐行 append+flush；字段名 `structural_checks_pass`（不再叫 checks_all_pass）。
4. **prune3 对照**：不用粗界；精确 scaled isqrt（+100 bit），无决定计 `undecided` 且不算 verified。
5. **atomic 对照口径**：与记录 `max_integer_capture` 的一致性只作 `diagnostic_*`；承重的是我自己的 status。calibration 按指示**跳过**，不做每叶随机点。

## 被复核 kernel 的 floor/ceil/overflow 方向（Lead 要求先审）

`members/upper-audit/integer-atomic/py/integer_kernel.py`（冻结 sha256 `0115c3f3…fc50`，实测一致）：
- `ceilF/floorF` 为精确整除法（`-((-n)//d)` / `n//d`），方向正确；
- 捕获判据 `d2 <= U2_ceil = ceil(U^2 S^2)` 是**放宽**方向（不会漏掉真捕获）；`inner_floor/outer_ceil` 的丢盒亦为放宽方向；
- 溢出界：`|endpoint|<=2S`、`|diff|<=4S`、`d2<=32S^2=2^57<2^63`，且 `total<2^60`、`10*total<2^63`，均自检；
- 实测 `max_endpoint_units <= S`、`max_d2` ≤ 3.26e10 ≪ 32S²（S=2²⁶）。
- **无问题**（与 Lead 独立结论一致）。

## 范围内外

**成立**：snapshot 的 frontier 精确铺满 root；76 个非法叶的排除理由逐条独立复现；1021 个 atomic 叶在**我自己的调用路径下**全部 certified；全部行绑定当前四源 hash。
**不成立/未做**：**核本身不是我的独立实现**——我与 upper 同用 `IntAtoms`，数值一致仅为同一核的重复执行；核的独立表示是相对 Lead 的 float→int 翻译（upper 承担）。snapshot 本身 `status='partial'`（pending 7 盒未处理）⟹ **不宣称全域**；nearmerge/k9/root 未再评；分区换用 upper 的 tree 实现亦不作为我这边依据（我用自己的递归 tiling）。

## 稳定使用命令（Lead 自行 background 最终重放）

```powershell
cd research-2026/n12-global/members/finite-reduction/integer-domain

# (0) 无缓存逐叶跑（最保守；新 snapshot 直接这样跑即可）
py -3 -B py/verify_manifest.py --snapshot <NEW_SNAPSHOT.json> --out-stem <NAME>

# stage6700（已完成）：1021 命中 stage2200 缓存 + 2053 新算 = 3074/3074 certified
py -3 -B py/verify_manifest.py --snapshot ../../../evidence/hubline-domain-stage6700.json --out-stem stage6700 --cache out/certified-cache.jsonl
py -3 -B py/check_results.py --snapshot ../../../evidence/hubline-domain-stage6700.json --out-stem stage6700

# (1) 复用 stage2200 的 1021 个 certified 判定作为缓存（严格校验导入，一次即可）
py -3 -B py/verify_manifest.py --build-cache `
  --snapshot ../../../evidence/hubline-domain-stage2200.json --out-stem stage2200 `
  --from-jsonl out/verify-stage2200.jsonl --cache out/certified-cache.jsonl

# (2) 用缓存跑新 snapshot（命中的叶不重算；tiling/prunes 仍按新 snapshot 全量重做）
py -3 -B py/verify_manifest.py --snapshot <NEW_SNAPSHOT.json> --out-stem <NAME> `
  --cache out/certified-cache.jsonl

# (3) resume（同 out-stem 重跑 = 零重算；仅读该 stem 的 jsonl）
py -3 -B py/verify_manifest.py --snapshot <NEW_SNAPSHOT.json> --out-stem <NAME>

# (4) 事后核
py -3 -B py/check_results.py [--snapshot PATH --out-stem NAME]   # 事后核
py -3 -B py/test_cache_binding.py       # 缓存绑定负控制（7 项）
```

产物命名：`out/verify-<out-stem>.jsonl`（逐叶追加）、`out/verify-<out-stem>-summary.json`（每 100 叶原子写）、`out/certified-cache.jsonl`（内容键缓存）。

**缓存语义（为什么它不会引入新错）**：
- 命中键 = **内容键** `ckey = sha256(H) : sha256(weights)`，且必须同时满足 `kernel`/`units` hash 与当前一致；不按旧 `idx` 寻址。
- 新行**永远**绑定**当前** snapshot hash 与**当前** idx；命中的行另记 `cache_origin={stem,snapshot,idx}` 以保留出处，`from_cache=true`。
- 因此"命中缓存"只表示"**同一份 (H, weights) 在同一 kernel/units 下此前已被判定**"，不会误述被验证的是哪个盒子。计数上分开 `certified_from_cache` 与 `certified_fresh`。
- `IntAtoms` 冻结核未改动（`0115c3f3…fc50`）。

## 控制读数（本次实测，未启动额外大 run）

| 控制 | 读数 |
|---|---|
| stage2200 同输入 resume（另起 stem + 缓存） | **1021/1021 命中缓存、fresh=0、耗时 1.5s**；tiling/prunes 按 snapshot 全量重做：`exact_partition=true`、`all_reproduced=true`、`n_struct_bad=0`、`verdict=complete-for-snapshot(partial frontier)` |
| 缓存导入校验 | `admitted=1021, rejected=0` |
| N1/N2 外来 kernel/units hash | 被 `load_cache` 忽略（各 1 条 foreign，仅 1 条生效） |
| N3 内容扰动（H 或 weights +1e−9） | 内容键改变 ⟹ **不命中**（必须重算） |
| N4 合成 snapshot 交换两叶 | 命中**跟随内容**：当前 idx 0 的行携带的 ckey 来自旧 idx 5（`origin_idx=5`），且该行绑定**当前** snapshot hash；当前 idx 集完整 |
| N5 不给 `--cache` | `certified_from_cache=0`，做 fresh 工作 |

七项全 true（`out/cache-binding-controls.json`）。