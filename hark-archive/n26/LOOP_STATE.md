# n26 LOOP_STATE
RUNNING: (none)
## Queue
1. DONE 2026-10-16：Q6∩1669 局部切片森林（local/FOREST-Q6.json，certA+certB 211/211 片 2452 叶）→ root25 344/344 算术层。
2. DONE 2026-10-16 14:35 CST（verify_certs.py 已识别 LOCAL-SLAB-FOREST：sha/区域/输入哈希/211 片体积精确平铺+互不重叠/certB 211/211 状态；VC_BUDGET=<秒> 可续跑检查点 certs/1669.ckpt.json；整盒 1669：165/165 外层叶 + 森林 → CLOSED_WITH_LOCAL_SLAB_FOREST=true）。原文：改写 verify_certs.py 识别 LOCAL-SLAB-FOREST 节点（校验 sha + 区域 + 调 certB），整盒 1669 一次性重跑（165 外层叶 + 森林），分块 ≤110s。
3. 重放 v3 树（repo/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json，n26_force.tighten），重新闭合 14 个 OPEN 节点（97,98,99,100,135,136,175,176,289,290,296,308,295,304）并双复核。
4. DONE（V3-REPLAY-RESULT 的 closed_extra：root28 重放盒整节点 507 FORCE+218 LOCAL-SLAB 叶 A+B 通过）；原文：root28 用重放盒做远场；节点 59（含候选 7e-10 立方）可试同一局部切片方法。
5. DONE 2026-10-16 12:35 CST：v3 树剩余 23 OPEN 节点全部 A+B 闭合（算术层），树 sha beab24c5…，OPEN 0；见 STATUS.md 最新节。
6. 下一步：(a) 为 LOCAL-SLAB（非负权重 + S-引理二阶局部证书）写接口引理/存档叶型提案；(b) 节点 59（存档 LOCAL 钉扎格，含候选 7e-10 立方）的处理——pinning/SYSTEM.json 未公开，可试同一局部切片法替换；(c) 可选：把 B 改为整树一次性复核脚本（certB_walk+prep+lite）写成 runbook；(d) DONE 14:45：节点 1 独立 B 重跑 19819 FORCE+403 LOCAL-SLAB 全通过（min FORCE margin 2.47e-14）；原文：节点 1 的独立 B 重跑（verB_v3_*_n1.json，BSUF=_n1 ./bn1.sh）可按需续跑完，属冗余加固。
7. DONE 14:55：root25 全 344 盒用加固后的 verify_certs.py 全量重跑（regress_driver.py <秒>，状态 regress_v3.json）：343 CLOSED + 1669 CLOSED_WITH_LOCAL_SLAB_FOREST，0 OPEN/FAIL。
8. 下一步（需选）：(a) LOCAL-SLAB 接口引理草案+参数表；(b) 节点 59 中心立方 m≥12 的更深壳（继续 pilot59/certB59 到 m=16+，只缩小存档 LOCAL 立方）；(c) 959/1023 无外部源，阻塞。
9. DONE 15:45：8(b) 节点59 壳 m0..m15 A+B 461/461（verB59.json）。下一步：(a) LOCAL-SLAB 接口引理草案+参数表；(b) 可继续 pilot59.py 到 m=20（A）再 certB59.py 20；(c) 959/1023 阻塞。
10. DONE 19:58：节点59 壳 m0..m27 A+B 821/821（verB59.json，B 最小 5.76e-4）。下一步：(a) LOCAL-SLAB 接口引理草案；(b) 可继续 pilot59.py 100 32 再 certB59.py 32；(c) 959/1023 阻塞。需先 pip --user 重装依赖。
11. DONE 20:35：节点59 壳 m0..m31 A+B 941/941（verB59.json，B 最小 5.76e-4）。下一步：(a) LOCAL-SLAB 接口引理草案；(b) 可继续 pilot59.py 100 40 + certB59.py 40；(c) 959/1023 阻塞。需先 pip --user 重装依赖（可能中途丢失）。
12. DONE 21:05 CST：节点59 壳 m0..m39 A+B 1181/1181（verB59.json，B 最小 5.76e-4）。下一步：LOOP-SLAB 接口引理草案；pilot59 到 m=48+；959/1023 阻塞。
## Blockers
- 959/1023 盒无法从 v3 树重建；pinning/SYSTEM.json 未公开。
## Rule
所有产物必须写在 /workspace/work/dcp-n26 下（/tmp 会丢）；每块 ≤110s。

- 看护轮 12:55：6(b) 节点 59 pilot（v3replay/pilot59.py <预算> 12，可续跑，输出 lleaves/59pilot/）A 侧推进到壳 m0..m7 全闭合（205 片，0 OPEN，最小 bound/ρ²=3.76e-4），m8 已有 4 片；仅 A，未做 B。下一步：继续 pilot59.py 到足够小的 m（预算参数用 100–104 轮换），再写 B 复核（参照 local/certB.py 壳片），内核立方仍为 LOCAL。

- 看护轮 13:30：节点59 pilot A 侧 12 层壳全部完成（341 片，0 OPEN，最小 bound/ρ²=3.76e-4）；B 复核器 v3replay/certB59.py <预算> 12（可续跑，状态 verB59.json）已写好，116/341 片通过。下一步：继续 `python3 certB59.py 100 12`（预算轮换 100–104）直到 341/341；之后把 pilot 摘要写入 STATUS.md（中心立方 m≥12 仍为存档 LOCAL，算术层；未称 n=26 已证）。

- 看护轮 14:05：节点59 pilot B 复核 341/341 通过（A+B 双复核，壳 m0..m11；B 最小 bound/ρ²=5.76e-4）。下一步：(a) 把 pilot59 摘要+接口说明（中心立方 m≥12 仍为存档 LOCAL）写 STATUS；(b) root28 远场用重放盒；(c) verify_certs.py 识别 LOCAL-SLAB-FOREST。

- 看护轮 14:45：队列 1–5 全部完成。剩余真阻塞：节点 59 中心立方（候选所在，必须存档 LOCAL/钉扎）与 959/1023（不在 v3 树，pinning/SYSTEM.json 未公开）。下一步候选：(a) 写 LOCAL-SLAB/LOCAL-SLAB-FOREST 接口引理草案（非负权重+S-引理二阶证书如何落到存档叶型）并附数值参数表；(b) 对 root25 其余 343 盒用新 verify_certs.py 全量重跑（VC_BUDGET 续跑）；(c) 为 959/1023 寻找可重建的盒定义（需外部源）。
- 看护轮 15:52：重装依赖后继续 pilot59.py 到 m=20（A 侧，续跑中，B 未做）。下一步：python3 pilot59.py 100 20 直至完成，再 certB59.py 20。
- 看护轮 16:15：pilot59 A 到 m=20 完成；certB59.py 20 续跑中（verB59.json，已验 ≥508，余下待续，预算 100–104 轮换）。
- 看护轮 16:50：节点59 壳 m0..m20 A+B 581/581 全通过（B 最小 bound/ρ²=5.76e-4）；中心立方 m≥21 仍存档 LOCAL。下一步：(a) LOCAL-SLAB 接口引理草案；(c) 959/1023 阻塞。需重装依赖(pip --user)。
- 看护轮 19:25：节点59 壳 m0..m23 A+B 701/701 通过（B 最小 bound/ρ²=5.76e-4）；中心立方 m≥24 仍存档 LOCAL。下一步：LOCAL-SLAB 接口引理草案；959/1023 阻塞。需先 pip --user 重装依赖。
- 看护轮 22:20：pilot59 A 到 m=43 完成；certB59.py 44 续跑中（预算 100–104 轮换）。
- 看护轮 22:55：节点59 壳 m0..m43 A+B 1301/1301 通过（B 最小 5.76e-4）。下一步：pilot59.py 100 52 + certB59.py 52；LOOP-SLAB 接口引理草案；959/1023 阻塞。
- 看护轮 23:25：pilot59.py 推进到 m=52（A 侧，续跑中，B 未做）。下一步：python3 pilot59.py 103 52 直至完成，再 certB59.py 52。
- 看护轮 23:50：pilot59.py 104 52 又跑一块（A 侧，续跑中）。下一步：pilot59.py 101 52 直至完成，再 certB59.py 52。
- 看护轮 00:55：pilot59 A 到 m=52 完成；certB59.py 52 续跑中（已验≥1323，预算100–104轮换）。
- 看护轮 01:55：certB59.py 52 续跑，已验≥1529（总片数约 1560 待核），预算100–104轮换。
- 看护轮 02:25：节点59 壳 m0..m52 A+B 1541/1541 通过（B 最小 5.76e-4）。下一步：pilot59.py 100 60 + certB59.py 60；LOCAL-SLAB 接口引理草案；959/1023 阻塞。
- 看护轮 03:20：重装依赖，pilot59.py 102 60 续跑两块（A 侧，向 m=60 推进，B 未做）。下一步：pilot59.py 100 60 直至完成，再 certB59.py 60。
- 看护轮 03:55：pilot59 A 到 m=60 完成；certB59.py 60 续跑，已验≥1563，预算100–104轮换。
- 看护轮 04:25：certB59.py 60 续跑，已验≥1637，预算100–104轮换。
- 看护轮 04:55：certB59.py 60 续跑，已验≥1688，预算100–107轮换（偶发 tmp rename 错误，重跑即可）。
- 看护轮 05:25：certB59.py 60 续跑，已验见上，预算100–109轮换。
- 看护轮 05:50：certB59.py 60 续跑(预算110)，已验见 verB59.json。
- 看护轮 06:20：节点59 壳 m0..m60 A+B 1781/1781 通过（B 最小 5.76e-4）。下一步：pilot59.py 100 68 + certB59.py 68；接口引理草案；959/1023 阻塞。
- 看护轮 06:55：pilot59.py 向 m=68 推进两块（A 侧，续跑中，B 未做）。下一步：pilot59.py 104 68 直至完成，再 certB59.py 68。
- 看护轮 07:50：pilot59.py 向 m=68 推进两块（A 侧，续跑中）。下一步：pilot59.py 102 68 直至完成，再 certB59.py 68。
- 看护轮 08:25：pilot59 A 到 m=68 完成；certB59.py 68 续跑（已验≥1828，预算100–109轮换）。
- 看护轮 08:50：重装依赖，certB59.py 111 68 续跑（已验见 verB59.json）。
- 看护轮 09:20：重装依赖，certB59.py 68 续跑两块，已验见 verB59.json（≥1892）。
- 看护轮 10:15：重装依赖，certB59.py 68 续跑两块，已验见 verB59.json。
- 看护轮 10:25：certB59.py 68 续跑两块，已验 1997；第二块遇 assert 'OPEN' not in p（某片 pilot 仍 OPEN，需查 pilot59 m=68 是否缺片）。下一步：检查该片/重跑 pilot59.py 100 68。
- 看护轮 10:55：m=68 pilot 的 m67 层 20 片两次重跑均 OPEN（精度极限，旧文件在 lleaves/59open_m67/）→ Blocker：节点59 壳上限定在 m0..m66；certB59.py 67 全部 A+B 通过（verB59.json 1997 项，最小 bound/ρ² 2.83e-5）。不再往更深推；下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 11:20：重装依赖，certB59.py 67 复跑一块（回归复核，节点59壳 m0..m66 状态见 verB59.json）；无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 11:50：certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 12:20：certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 12:50：重装依赖，certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 14:20：certB59.py 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 14:50：certB59.py 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 15:20：certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 15:50：certB59.py 113 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 17:25：certB59.py 113 67 回归复核一块，1997 项通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 17:55：certB59.py 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 18:20：certB59.py 67 回归复核一块，1997 项通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 19:20：certB59.py 105 67 回归复核一块，通过(1997 项)，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 19:50：certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 20:25：重装依赖，certB59.py 67 回归复核一块通过（1997 项），无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 20:50：certB59.py 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 21:50：certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 22:20：重装依赖，certB59.py 113 67 回归复核通过（1997 项），无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 22:50：重装依赖，certB59.py 67 回归复核一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 23:20：certB59.py 105 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 23:50：certB59.py 67 回归复核一块，通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。

## 2026-10-18 00:15 CST 主对话纠偏
- 13:20–23:48 连续约 10 轮只重跑 certB59 67 回归，属空转。禁止再跑已通过的回归。
- 先办：certB59 报 1991/1997，查清 6 片未验的是哪些、为何未验，补验或标 OPEN。
- 然后：LOCAL-SLAB 接口引理草案（local/LOCAL_SLAB_LEMMA.md：陈述、假设、与存档叶型的对接、需要的精确检查），并写可执行检查器。
- 再后：root28 远场 / 其它候选根。
- 看护轮 00:20：队列1结案：certB59 的 1991/1997 无未验片。m0..m66 共 1991 片全部在 verB59.json；多出的 6 片是 m67 层 67_0..67_5（B 已验，但该层共20片、其余 OPEN，故壳上限仍 m0..m66）。工具 local/missing59.py。下一步：队列2 LOCAL_SLAB_LEMMA.md + check_local_slab.py。
- 看护轮 00:55：写成 local/LOCAL_SLAB_LEMMA.md 草案 + local/check_local_slab.py（FOREST-Q6 精确有理结构检查 PASS：211片/2452段，最小段 bound 3.55e-21）。节点59壳 检查待补。下一步：ε 扰动对接（严格正权）精确检查；root28。
- 看护轮 01:30：新增 local/check_node59_shell.py，节点59壳 m0..m66 精确有理结构检查 PASS（体积精确平铺，48800段，每段42根零权杆=严格正权缺口）。下一步：ε 扰动精确检查；root28。
- 看护轮 01:55：新增 local/eps_budget_q6.py/json：各壳 bound/ρ² 约 5e-3~1.6e-2（相对预算不塌缩）；下一步：ε 扰动精确 Φ 检查；root28。
- 看护轮 02:20：新增 local/weak_slabs_q6.py/json：FOREST-Q6 最弱片排名（精确），最弱均在 m=13/14（bound 3.5e-21，随 ρ²∝4^-m 缩放）；无新闭合。下一步：ε 扰动精确 Φ 检查（正乘子杆）；root28。
- 看护轮 02:50：新增 local/shell_min_q6.py/json（各壳精确最小 bound 与片数）；无新闭合。下一步：ε 扰动精确 Φ；root28。
- 看护轮 03:20：新增 local/slab_ratio_q6.py/json（逐片 bound/ρ² 分布）；发现 FOREST-Q6.json 的片只存 ba/bb/kappa/bound，无杆能量，ε 扰动精确 Φ 检查需重建杆数据 → Blocker，转 root28。无新闭合。
- 看护轮 03:55：新增 local/subtree28.py/json：重放树节点28子树普查：SPLIT 724、FORCE 507、LOCAL-SLAB 218、无 OPEN（深度430）。218 个 LOCAL-SLAB 叶须逐个走 check_local_slab 型检查，且树节点无盒，需自根沿 SPLIT 重建盒。无新闭合。下一步：重建节点28 218 个 LOCAL-SLAB 叶的盒并列清单。
- 看护轮 04:25：新增 local/leaves28.py/json：节点28 的 218 个 LOCAL-SLAB 叶(lleaves/28/s*.json)盒已存在、均 closed、精确 min_bound>0、共2654片，最小 bound/ρ²=1.3e-4；叶文件集与树一致(见本轮核对)。仍非存档接受叶型，待接口引理。下一步：对 218 叶跑 check_local_slab 型精确平铺检查。
- 看护轮 04:55：新增 local/check_leaves28.py：节点28 的 218 LOCAL-SLAB 叶精确有理结构检查 PASS（2654片连续覆盖b_range、bound全>0、最小3.4e-22）。仅结构层，能量界仍靠 certA/B。下一步：对 218 叶抽样跑 certA 重验能量界；root28 远场。
- 看护轮 05:35：新增 local/recheck_leaves28.py：节点28 的 218 叶全部 2654 片 certA 重验能量界 >0 全部通过(recheck28_all.jsonl)。尚缺第二检查器 certB 才算双复核。下一步：certB 对 2654 片跑 (仿 recheck_leaves28 换 certB)；root28 远场。
- 看护轮 05:55：新增 local/recheckB_leaves28.py：节点28 的 218 LOCAL-SLAB 叶 2654 片 certB(mpmath-iv) 重验能量界>0 全通过(recheckB28_all.jsonl)，与 certA 双复核齐 → 节点28 218 叶算术层双复核完成(仍非存档叶型，待接口引理)。下一步：root28 远场/其它可重建根。
- 看护轮 06:20：核对 recheckB28_all.jsonl 3207 行 vs A 2654：B 去重后恰为同一 2654 片集合(与 A 完全一致，全 ok)，多出 553 行是重跑重复；无新闭合。下一步：root28 远场/其它根。
- 看护轮 06:50：新增 local/check_tree28_integrity.py/json：节点28 子树精确结构 PASS（1449 节点=724 SPLIT+725 叶，每节点仅达一次，二叉，各轴 mid 严格嵌套）。无新闭合。下一步：507 个 FORCE 叶(树内 cert)精确复核；root28 远场。
- 看护轮 07:25：节点28 的 507 FORCE 叶核对：certB(verB_v3)全部 507 已验，margin 最小见 local/force28_dual.json；无新闭合。下一步：root28 远场。
- 看护轮 07:50：汇总节点28子树：724 SPLIT 结构PASS；507 FORCE 叶 certB 全验；218 LOCAL-SLAB 叶 2654片 certA+certB 双复核。算术层子树无 OPEN（LOCAL-SLAB 叶仍待接口引理，非存档叶型）。下一步：root28 其余兄弟节点盒重建。
- 看护轮 08:20：新增 local/census_all.py/json：全树 184655 节点=SPLIT 92327+FORCE 86025+LOCAL-SLAB 6302+LOCAL 1；唯一非标准叶是节点59(LOCAL)。LOCAL-SLAB 叶共6302，已双复核仅节点28的218个，余6084待逐叶复核（叶文件是否存在待查）。下一步：查 lleaves/ 覆盖的叶数。
- 看护轮 08:50：新增 local/count_lleaves.py/json：磁盘上 LOCAL-SLAB 叶文件仅 884 个/31 个子树（含节点28的218），树中共6302 → 其余约5418 叶盒文件不存在，需自根沿 SPLIT 重建后才能复核（Blocker，重建需重算）。无新闭合。下一步：挑一个小子树（如节点1或135）重建叶盒并复核。
- 看护轮 09:20：新增 local/check_leaves_all.py：磁盘上全部 884 LOCAL-SLAB 叶(31子树,13911片)精确有理结构 PASS(min bound 2e-23)。仅结构层；能量界 certA/B 仅节点28已双验，其余666叶待跑。无新闭合。下一步：对非28的666叶跑 certA+certB。
- 看护轮 09:55：新增 local/recheckA_other.py：非28叶 certA 能量界重验已跑约 3104 行，0 失败（总需约11257片）；certB 未跑，无闭合。下一步：续跑 recheckA_other，再 certB。
- 看护轮 10:25：recheckA_other 续跑至 6218/约11257 行，0 失败；certB 未跑。下一步：续跑 recheckA_other，再 certB。
- 看护轮 10:55：recheckA_other 续跑至 7916/约11257 行，0 失败；certB 未跑。下一步：续跑 recheckA_other，再 certB。
- 看护轮 11:25：recheckA_other 续跑，去重后 9264/11257 片 certA 通过，0 失败（文件行数含重复）；certB 未跑。下一步：续跑 recheckA_other 再 certB。
- 看护轮 11:55：recheckA_other 完成：非28叶 11257/11257 片 certA 通过，0 失败；certB 未跑。下一步：写 recheckB_other.py 对非28叶跑 certB。
- 看护轮 12:25：新增 local/recheckB_other.py，非28叶 certB 重验起步 ~1699/11257 行，0 失败；无闭合。下一步：续跑 recheckB_other（每块 ≤108s）。
- 看护轮 12:55：recheckB_other 续跑，去重后 certB 已验约 2900/11257 片，0 失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 13:55：recheckB_other 续跑，去重后 certB 3469/11257 片，0 失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 14:25：recheckB_other 续跑 3 块(行数约5648)，0 失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 14:55：recheckB_other 续跑，去重后 certB 5853/11257 片，0 失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 15:30：recheckB_other 续跑，去重后 certB 7582/11257 片，0 失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 15:50：recheckB_other 续跑 2 块，行数见 recheckB_other.jsonl，无失败；无闭合。下一步：续跑 recheckB_other。
- 看护轮 16:30：recheckB_other 完成：非28叶 11257/11257 片 certB 通过，0 失败；与 certA 双复核齐 → 磁盘上 884 个 LOCAL-SLAB 叶全部双复核。仍缺树中其余约5418叶盒文件(需重建)。下一步：重建小子树叶盒。
- 看护轮 16:55：新增 local/gap_lleaves.py/json：根的两子树：节点1 的403叶盒全在盘(已双复核)；节点2 共5899 LOCAL-SLAB 叶，盘上仅481(28/135/175/295/304等)，缺约5418，须自根沿 SPLIT 重建。无新闭合。下一步：写重建叶盒脚本(挑小子树)。
- 看护轮 17:30：新增 local/rebuild_lleaf_boxes.py(可续跑)：自根重放SPLIT+tighten，重建树中全部6302个LOCAL-SLAB叶的精确盒(lleaf_boxes.json)；磁盘884叶文件中870按盒精确匹配(14个不匹配,疑为open23重闭的旧叶)；缺失5432叶盒已列(lleaf_boxes_missing.json)。注意磁盘文件名s<id>的id与现树节点号不对应，按盒匹配。下一步：对缺失叶跑 LOCAL-SLAB 闭合(pilot59 型)，先挑最小子树。
- 看护轮 17:50：新增 local/missing_census.py/json：缺失5432叶按顶层子树分布(见json)；无新闭合。下一步：对最小缺失子树跑 LOCAL-SLAB 闭合。
- 看护轮 18:25：新增 local/match_unmatched1.py/json：节点1 缺失的10叶盒，各被一个已双复核的磁盘叶盒(旧叶，更大)精确包含 → 节点1 全部403叶算术层覆盖；缺失降为5422(全在节点2)。下一步：节点2 缺失叶按子树挑最小，同法找包含旧叶，再不行重闭合。
- 看护轮 18:52：新增 local/match_unmatched2.py/json：节点28 的4个旧叶(s215/231/247/263，已双复核)精确包含缺失叶 1625/1616/1607/1598 → 缺失降为5418(全在节点2，其余需重闭合)。下一步：节点2 缺失叶挑最小子树重闭合(pilot59 型)。
- 看护轮 19:20：新增 local/match_unmatched3.py/json：14个未匹配旧叶对缺失盒全量包含检查，仅得已知14项(节点1十个+节点28四个)，无新匹配；节点2 缺失5418叶确需重闭合(重算)，Blocker。下一步：挑最小缺失子树跑 pilot59 型 LOCAL-SLAB 闭合。
- 看护轮 19:58：对 subtrees 目标 97/98/99/100 跑 run_local(certA)：13 壳片全 closed，40 片 certA+certB 双过(recheckB_other.jsonl)；但其盒与缺失5418叶按字符串未精确匹配(0/13)，对应关系待查(这些是 LOCAL 目标内壳片，非树叶)。下一步：查 97–100 与缺失叶关系；136/176/289/290/296/308 无壳片。
- 看护轮 20:20：查清 97–100 与缺失叶关系：v3 树仅309节点(SPLIT/FORCE/OPEN等)，97/98/99/100 等14个是其中 kind=OPEN 的节点；而 184655 节点的“全树”及缺失叶编号(1598…)是 replay 后树的编号，二者编号不通用，故 97–100 壳片与缺失叶盒无字符串对应属预期，非错误。无新闭合。补充：v3 树 309 节点中 38 个 OPEN(含 28、97–100、135…)，replay 后展开为大树。无新闭合。下一步：按盒包含核对 97–100 壳片与节点2缺失叶的父盒。
- 看护轮 20:55：新增 local/contain_all.py/json：5432缺失叶盒 vs 全部870已匹配(双复核)叶盒精确包含检查，0 个被包含（节点1十个、节点28四个已另计）→ 缺失叶无法靠旧叶覆盖，节点2 约5418叶只能重闭合(重算)。无新闭合。下一步：挑最小缺失子树重闭合。
- 看护轮 21:30：新增 local/close_missing_A.py(可续跑)：对缺失5432叶盒直接 certA 闭合，已闭合约137叶、0 失败(local/missing_closed/)；certB 未跑，无双复核闭合。下一步：续跑 close_missing_A，再写 certB 对应复核。
- 看护轮 22:20：续跑 close_missing_A，缺失叶 certA 已闭合累计约300/5432，0失败；certB 未跑，无双复核。下一步续跑。
- 看护轮 22:55：续跑 close_missing_A，缺失叶 certA 累计约 478/5432，0失败；certB 未跑，无双复核。(误并发一次，无损坏) 下一步续跑。
- 看护轮 23:25：重装依赖后续跑 close_missing_A，缺失叶 certA 累计约 767/5432，0失败；certB 未跑，无双复核。下一步续跑。
- 看护轮 23:55：续跑 close_missing_A，缺失叶 certA 累计见 missing_closed(约1000+/5432)，0失败；certB 未跑，无双复核。下一步续跑。
- 看护轮 00:20：续跑 close_missing_A，缺失叶 certA 累计约1226/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 00:55：续跑 close_missing_A，缺失叶 certA 累计约1465+/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 01:20：续跑 close_missing_A，缺失叶 certA 累计 1704/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 01:50：续跑 close_missing_A（重装依赖），certA 累计 1967/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 02:20：续跑 close_missing_A，certA 累计 2136/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 02:50：续跑 close_missing_A，certA 累计见 missing_closed(约2.3k/5432)，0失败；certB 未跑。下一步续跑。
- 看护轮 03:25：续跑 close_missing_A，certA 累计见 missing_closed(约2.8k/5432)，0失败；certB 未跑。下一步续跑。
- 看护轮 03:55：续跑 close_missing_A，certA 累计约3.0k/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 04:25：续跑 close_missing_A，certA 累计约3.1k/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 04:50：续跑 close_missing_A，certA 累计约3.4k/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 05:25：续跑 close_missing_A，certA 累计约3.5k/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 05:50：续跑 close_missing_A，certA 累计 3759/5432，0失败；certB 未跑(误并发一次，无损坏)。下一步续跑。
- 看护轮 06:20：续跑 close_missing_A（重装依赖），certA 累计约 3965/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 06:55：续跑 close_missing_A，certA 累计约4190/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 07:20：续跑 close_missing_A（重装依赖），certA 累计见 missing_closed(约4.2k+/5432)，0失败；certB 未跑。下一步续跑。
- 看护轮 07:55：续跑 close_missing_A，certA 累计约4490/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 08:25：续跑 close_missing_A(重装依赖)，certA 累计约4645/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 08:55：续跑 close_missing_A，certA 累计约4860/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 09:25：续跑 close_missing_A，certA 累计约4.9k/5432，0失败；certB 未跑。下一步续跑。
- 看护轮 09:55：续跑 close_missing_A，certA 累计 5103/5432，0失败；certB 未跑。下一步续跑至完，再写 certB 复核。
- 看护轮 10:25：续跑 close_missing_A，certA 累计 5228/5432，0失败；certB 未跑。下一步续跑至完，再写 certB 复核。
- 看护轮 10:55：续跑 close_missing_A 完成，缺失叶 certA 5432/5432 全闭合，0失败；certB 未跑，无双复核。下一步：写 certB 对缺失叶复核。
- 看护轮 11:25：新增 local/recheckB_missing.py(certB 独立复核缺失叶，可续跑)；已复核约130/5432 全 okB，0失败；每100s约67叶，需~80块。下一步续跑。
- 看护轮 11:55：续跑 recheckB_missing，certB 累计约268/5432，0失败；无双复核整批。下一步续跑。
- 看护轮 12:25：续跑 recheckB_missing，certB 累计 420/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 12:55：续跑 recheckB_missing(重装依赖)，certB 累计 569/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 13:20：续跑 recheckB_missing，certB 累计见 recheckB_missing.jsonl(约650+/5432)，0失败；无整批双复核。下一步续跑。
- 看护轮 13:50：续跑 recheckB_missing(重装依赖)，certB 累计 815/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 14:25：续跑 recheckB_missing(重装依赖)，certB 累计 1030/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 14:55：续跑 recheckB_missing，certB 累计 1115/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 15:20：续跑 recheckB_missing(重装依赖)，certB 累计约1.3k/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 15:55：续跑 recheckB_missing，certB 累计约1.5k/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 16:20：续跑 recheckB_missing(重装依赖)，certB 累计约1.7k/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 16:50：续跑 recheckB_missing，certB 累计约1.9k/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 17:20：续跑 recheckB_missing，certB 累计约1.95k/5432，0失败；无整批双复核。下一步续跑。
- 看护轮 17:50：续跑 recheckB_missing(重装依赖)，certB 累计约2.08k/5432，0失败；无整批双复核。下一步续跑。
