# 最新接续：原点搜索与B16离线有限块证明

2026-10-05 12:37（Asia/Shanghai）状态快照。
goal active，不用子代理；n25优先，继而n23/n24，之后才选n26+或n11。
n11未启动、编译或修改。此记录优先于B14-CLOSED等旧交接的活作业状态。
不得热改任何活作业绑定文件；本轮新证明的绑定文件也须保持字节不变。

## 不要重复的完整成果

N25/B14全部172092个必要父图已独立总验收闭合，pending0。
入口仍为`n25-B14-all-parent-lower-chain-audit-20261005-v1/VERIFIED.json`。
不要重跑B14枚举、2287族补全、80族通用补全、13族细化或整父审计。
这只是B14家族闭合，不是N25全局定理。

## 三个仍活的完整搜索

以下PID均在上述时间重新用Linux ps及完整命令核查，下一轮仍需再核查。

| 会话 | Linux PID | 作业 |
|---|---:|---|
|51611|15141|n25-B15-origin-streamed-search-20261005-v1|
|8602|12311|n25-B16-origin-streamed-search-20261005-v1|
|36794|12332|n25-B17-origin-streamed-search-20261005-v1|

均为`peel_origin_streamed_collar-linux`，N25，对应B，node-limit0，
dfs，未seed，原严格库，cap8=4058615，slab100000，origin flag1。
最后约170/437/274百万calls；这些不是完成率或完整型数。
三个都尚未有可接受的完整终止/全块并集。

B15旧无原点条件的流式作业已在上一轮有序替换：
原native3757实际exit15，原会话12893的Python拒绝非零运行。
`n25-B15-streamed-eight-sparse-search-20261005-v1/NATIVE-TERMINAL.json`
及`n25-B15-controlled-origin-replacement-20261005-v1`保留。
旧块不删除、不是恢复点或全集；新B15从完整根开始，不能再启动第二份。
不要修改`b15_controlled_stop.py`及新B15已冻结驱动。

## 本轮已结束的有限B16证明

1. 已有64个闭slab0样本由新输入适配器
   `sparsify_verified_group_prefix.py`压缩为9个独立严格障碍。
   原逐删面自身整角域重证逻辑不变；缓存仅按同一规范图复用证明。
   `n25-B16-origin-prefix64-sparse-20261005-v1`，
   `n25-B16-origin-prefix64-sparse-library-20261005-v1`。
   `audit_paid_prefix_sparse.py`全64来源注入通过，8项坏输入拒绝。
   `verify_sparse_maps_fast.py`保留达到型。
2. 第0块用9个障碍全100000行独立重放，7634 strict/92366 pending。
   目录`n25-B16-origin-slab0-new9-sparse-payments-20261005-v1`。
3. 从92366未付位置按等间隔索引选256个有限发现图。
   `n25-B16-origin-slab0-pending256-discovery-20261005-v1.json`，
   不是枚举耗尽；适配器`sample_pending_closed_slab.py`。
   原`probe_family_discovery.py`+原独立重放：199 strict/57 pending。
   `n25-B16-origin-slab0-pending256-proofs-20261005-v1`；
   `n25-B16-origin-slab0-pending256-fresh-exact-20261005-v1.json`。
4. 原`sparsify_family_discovery.py`将199图压缩为153障碍，
   原group重放/原exporter及新逐来源映射审计通过。
   `n25-B16-origin-pending199-sparse-20261005-v1`，
   `n25-B16-origin-pending199-sparse-library-20261005-v1`。
5. 同B离线合并旧2+新9+新153，164障碍。全部树新鲜重放，
   原exporter通过，不导入优化器：
   `n25-B16-offline-union-sparse-20261005-v1`，
   `n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json`。
   1154显式映射、522独立存在性对照及达到型保留通过：
   `n25-B16-offline-union-sparse-map-controls-20261005-v1/VERIFIED.json`。
   **这164库未接入任何活搜索。**
6. 164库全slab0逐行独立付款：88802 strict/11198 pending。
   `n25-B16-origin-slab0-union164-sparse-payments-20261005-v1`。
   `pay_closed_origin_slab.py`只提议显式映射，未命中始终pending；
   `replay_closed_origin_slab.py`另进程新鲜验收全部树/全部行/所有正映射。
   `n25-finite-closed-slab-partition-controls-20261005-v1`完整正重放及8拒绝通过；
   坏测试文件重新绑定SHA后仍因结构/映射失败，不只是旧hash拒绝。
7. 原未付57样本由冻结linked通用补全面递归处理，5族直接闭合，
   52族完整叶未付，但全部frontier0：
   `n25-B16-finite-pending57-linked-fillings-20261005-v1`，会话8069实际exit0。
8. 原simple-hole叶细化器仅机械替换schema/源身份/linked provider，
   严格可逆派生，未改force与树结构逻辑：
   `linked-leaf-refinement-source-derivation.json`，
   `refine_linked_collar_leaves.py`，`replay_refined_linked_leaves.py`。
   候选控制又付13叶，但真实exact-rstar完整规范码显式留在未付叶中；
   4结构负对照通过：
   `n25-linked-leaf-refinement-controls-20261005-v1/VERIFIED.json`。
9. 对全部52族仅替换旧FULL_PENDING叶，force-limit31，整树重新接受；
   **52族全部闭合，未付0**：
   `n25-B16-finite-pending52-linked-force31-20261005-v1`，
   会话68467实际exit0。不是重启拓扑递归。
10. 新`audit_finite_slab_filling_supplement.py`标准库重新验收全部57整树，
    对完整100000行再次检查源数组/稀疏映射/补全绑定，扣38重叠，
    净新增19，最终88821 paid/11179 pending。
    `n25-B16-origin-slab0-combined-sparse-and-fillings-20261005-v1`，
    会话52608实际exit0。

以上所有作业已结束，不要重跑发现样本、153稀疏化、57补全或52细化。
完整256有限样本已由199严格弱图和57补全族支付，但不是B16家族全集。

## 最新有限块pins

- 164库：3143b385ccbe127c27c0778496b9e9ffbf766cbb945e2e244582f09d9da23902
- combined VERIFIED：966d820f61f9cced28c916d585d97da773ddbf96de902c6ed07f24580d97bac2
- combined PARTITION：f12adf74a3649c05cea89da9ef0853b2db0aa8ef20935617e3c2ad445ef2063f
- combined PENDING：7aa29cb1e3df0ab1e20b2c1f8f4022c4d71ceaf17aaf4b92eba7cc8f6b2b2b66
- source slab0：3949442a79dfed352306147be1c05e85a1ab42763a7ed5e3859db9a8fb93b0d7

用户交付：
`C:\Users\Administrator\Documents\Codex\2026-10-04\he\outputs\证明推进记录.md`，
同目录`n25-B16有限块证明进展.md`。

## 下一步

1. 核对三搜索实际状态，不因无新块或等待超时重启。
   实际exit0后用冻结`merge_origin_collar_chunks.py`完成所有slab独立
   规范码/精确集合归并、输入字节绑定，再使用已控制的origin批处理接口。
2. 164严格库可离线支付最终完整目录；57补全族须按完整规范面数组及中心数
   对最终并集重新运输，不能沿用本块row id或累计重复付款。
   本块88821不是全B16已付数，11179不是全B16残余数。
3. 若继续处理本块，使用combined PENDING的11179，不再用旧11198/92366。
   `sample_pending_closed_slab.py`当前入口只接受原sparse阶段schema，
   不可直接喂combined报告；需要新增明确适配器，不能热改已绑定源。
4. 既有B16达到图的91补全族（90 strict+1 exact-rstar核心）已闭合，
   补全库8476型运输已通过，但不在活native内。
   不用strict>U排除达到型；可用精确核心/既有完整补全族。
5. V24隐藏圆心`|h|≤5ρ−1`仍未接入力内核，不能冒称已用该加强条件。
6. B14..17全部必要族闭合、任意覆盖源接口及精确上界合成之前，
   n25和goal不能complete；之后还必须完成n23/n24。
