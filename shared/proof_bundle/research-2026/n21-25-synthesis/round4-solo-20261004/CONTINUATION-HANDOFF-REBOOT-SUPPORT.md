# 最新接续：重启恢复、B16快筛控制与全有限残余

2026-10-05 14:24（Asia/Shanghai）。goal active，无子代理。
n25→n23/n24，之后再选n26+或n11。n11未启动/编译/修改。
本记录覆盖ORIGIN-PREFIX-SPARSE等旧交接的活作业状态。
不得热改任何活作业输入/库/源/接受器/二进制及本轮已接受证明绑定文件。

## 本轮真实外部中断

Win32_OperatingSystem.LastBootUpTime确认为2026-10-05 13:39:23；
旧所有数学native与Windows Python真实不在进程表，旧会话不可访问。
这是机器重启，不是仅工具观察超时。旧三个目录均无完整manifest/
SUMMARY/NATIVE-TERMINAL；**实际旧退出码未知，不伪造非零/零退出**。

`n25-machine-reboot-interruption-20261005-v1/VERIFIED.json`已成功生成：
B15 4闭块、B16 11闭块、B17 11闭块全部逐行扫描、严格排序、
原点条件下中心数<25及字节哈希通过；旧文件未删或修改。
sha e8620c5d772ad1467aa38eb6c950a997017f04c505cbbda8dd9241f22fd02efd。
旧前缀不是内存恢复点或完整目录。旧15141/12311/12332不得重杀或沿用。

新`reboot_interruption_gate.py`验证机器boot、旧输入早于boot、旧目录/
身份/所有冻结输入、当前没有任何相同B的N25 native后才允许恢复。
新driver`run_reboot_origin_search.py`机械从原driver派生，只替换生命周期门槛；
原全部严格库/八杆/注入/原点/流式/最终union门槛保留。
`n25-machine-reboot-recovery-controls-20261005-v1.json`6拒绝通过，
包括真实活B15/B17与synthetic新旧B16重复进程。
不要调用旧B15 controlled_stop去处理本次重启：此前手工替换记录仍保留。

## 当前实际活作业（下轮必须重新核查）

|会话|Linux PID|Windows Python|任务|
|---|---:|---:|---|
|58506|556|15336|B15原验证版，从完整根重启|
|76892|559|15240|B17原验证版，从完整根重启|
|58793|1228|6040|缓存版N23/B16 audit完整控制|
|81962|无，Python链|9684主/17944补全|全slab0原11179残余→8049补全|
|16626|无，Python链|5104主|下一批512个已完成pending族叶细化|

B15新目录`n25-B15-origin-streamed-search-reboot-20261005-v1`；
B17新目录`n25-B17-origin-streamed-search-reboot-20261005-v1`。
均原`peel_origin_streamed_collar-linux`，N25，对应B，node-limit0，
dfs，未seed，原库，cap8=4058615，slab100000，origin1。
**B16全族目前没有活生产枚举器**，等以下四控制闭合后恢复新版本，
不要先启动原2障碍版本再主动重启。

## 已完成：B16必要匹配快筛/有界候选缓存

没有修改原`peel_origin_streamed_collar.cpp`/matcher或原二进制。
新源只加来自中心/面注入的必要条件：
总面数、各1/2/3边界面类型数、边界支持位集合。
不新增数学障碍、角度阈值或枚举规则，保留原成功变换及内部搜索顺序。
缓存键完整含N/B/边界支持/面数/三类型数；4096键+1048576候选索引限额，
清空或超限不剪递归，单列表超限仍完整执行而不缓存。

- 源论证：`SPARSE-SUPPORT-NECESSARY-FILTERS.md`、`SPARSE-SUPPORT-CACHE-SOURCE.md`。
- 可逆机械派生：`sparse-support-filter-source-derivation.json`、
  `cached-sparse-support-source-derivation.json`。
- 新native：`sparse_support_cached_match-linux`、
  `peel_cached_support_origin_collar-linux`（另有eight版本，未用生产）。
- 原/uncached与原/cached均逐请求严格相等：1507合成/独立/达到请求+
  100000真实slab请求，命中与具体中心/锚点/面映射完全一致。
  接受`n25-B16-cached-support-map-controls-20261005-v1/VERIFIED.json`。
- 真实N25候选与真实严格来源，各origin0/1共4受限完整种子结果正确：
  `n25-B16-cached-origin-seed-controls-20261005-v1/VERIFIED.json`。
  达到型保留；严格来源由实际注入支付。不是完整N25家族。
- 有界100000calls性能诊断，所有测试实际非零NODE LIMIT，非完整证明：
  原2库2.281s、164未缓存4.422s、164缓存3.297s。
  `n25-B16-support-prefix100000-performance-20261005-v1/DIAGNOSTIC.json`。

### 四个完整小族控制接续

原N22 dfs/audit均真正exit0并已完成union，303→62。
`audit_completed_N22_cached_controls.py`新鲜重验2个全部残余集合及482差集映射：
`n25-B16-completed-N22-cached-controls-fresh-20261005-v1.json`。
sha 811341db60b25a16a55cfd81d3a00834dbdba3e6d05fc1957addf8b5e5d8563a。
不要重跑这两例。

重启前的N23控制未完，旧输出保留，不算完成。
新`test_N23_cached_origin_partition.py`仅机械限定N23，仍原全部union/
差集/正映射与拒绝检查：
`n25-B16-cached-support-N23-partition-reboot-20261005-v1`。
其dfs已经实际exit0：48500435基准calls/14709图→44357588 calls/4039残余，
native约1210s。当前audit仍活pid1228。4个控制使用**N25常数**，
不是n22/n23新全局下界成果。

该会话真实结束、最终VERIFIED存在后，执行：

```
python join_cached_origin_partition_controls.py --N22 n25-B16-completed-N22-cached-controls-fresh-20261005-v1.json --N23 n25-B16-cached-support-N23-partition-reboot-20261005-v1/VERIFIED.json --output n25-B16-cached-support-all-four-partition-controls-20261005-v1.json
```

已有新`cached_origin_production_gate.py`和机械派生
`run_cached_reboot_origin_search.py`，要求全部四例、101507请求对照、
实际N25种子、可逆源派生、完整原角度/储存/原点/生命周期门槛。
不能在joined四例报告缺失时放宽门槛启动。
全部通过后，从完整根启动一次：

```
python run_cached_reboot_origin_search.py --library n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json --maps n25-B16-cached-support-map-controls-20261005-v1/VERIFIED.json --eight-controls n25-eight-rod-collar-controls-20261005-v2/VERIFIED.json --guard-controls n25-B16-cached-support-all-four-partition-controls-20261005-v1.json --origin-controls n25-origin-collar-controls-20261005-v1/VERIFIED.json --failed-search n25-B16-origin-streamed-search-20261005-v1 --storage-controls n25-streamed-collar-controls-20261005-v1/VERIFIED.json --output n25-B16-cached-origin-streamed-search-reboot-20261005-v1
```

`--failed-search`是沿用参数名，本次实际退出码未知，由reboot gate处理，
不是冒称已收取失败terminal。启动前必须再次核对无活N25/B16。

## 全有限slab0残余已推进（不是B16全族）

前期164独立严格库与57补全族闭合仍保留；原闭合88821/11179，
不要重跑旧64/256样本、153稀疏化、57补全及52细化。
B14整个172092必要家族闭合仍有效，完全不重跑。

`run_all_finite_slab_residual.py`冻结全部11179未付图后做root严格提案，
原接受器独立重放：**3130 excluded/8049 pending**。
重启前的同名阶段已中断、原输出保留，真实已恢复链为：
`n25-B16-origin-slab0-all11179-residual-reboot-20261005-v1`。

- `ALL-PENDING-SNAPSHOT.json` sha
  4dd425f18ca44190d848eb7990c9f89deef406e416431a351f990b694f9ab369。
- `STRICT/SUMMARY.json`与`STRICT-EXACT.json`已完成，**不要重跑严格阶段**。
- 新全100000行严格补充审计实际exit0：
  `n25-B16-origin-slab0-all3130-force-supplement-20261005-v1`，
  91951 paid/8049 pending，旧所有稀疏映射/补全树/新力树再接受。
  report sha 7377d142d08de79c8abc60f673dc1b09930a2c0eeb5181b981f42189cbdc41e3。
- 主`FILLINGS`仍处理全部8049，最后观察约1206族；
  131直接闭合、其余大多完整叶pending，不能把打印计数当整阶段完成。
  不热改`pay_finite_discovery_fillings.py`。

### 已关闭族的并行单次冻结细化

新`refine_closed_linked_stage_snapshot.py`只选已最终发布STATUS、
成功独立terminal、FULL_PENDING>0/frontier0的完整族；精确核查source
snapshot图/旧提案/旧EXACT后freeze。只替换旧完整未付叶，整树另进程重放。
不是主阶段重启或完整父族证明。

- 第一批
  `n25-B16-all8049-completed-pending-snapshot256-force31-20261005-v1`，
  会话45508实际exit0，256全部闭合、still_unpaid0。
- 下一批
  `n25-B16-all8049-completed-pending-next512-force31-20261005-v1`，
  会话16626仍活。明确`--already-refined`排除第一批所有索引，
  已冻结512族，不要重复启动或先计作完成。
- 后续选择时传两批的`--already-refined`，即使第二批尚活也可由
  INPUT-SNAPSHOT排除其已分配索引；不要让多个细化作业重复图。
- 同force-limit31会跳过已经尝试的族；仍未付若要升到101需新明确流程，
  不偷偷把数值诊断当排除。达到型精确控制始终显式留未付。

### 最新整块独立分割

`audit_closed_filling_supplements.py`对主阶段已完整闭合131族和上述
已结束256族再独立整树重放，所有源图与全100000行一一匹配；
旧所有正付款也重新接受，净新增387，无重叠。
会话70328实际exit0：
`n25-B16-origin-slab0-closed-fillings-supplement-20261005-v1`。

最终：88802稀疏+3130弱力+406补全+7662未付=100000；
**92338 paid/7662 pending**。这不是完整B16族数或完成率。

Pins：

- VERIFIED c03320937ab9f4657c74bc78f110d1dbc4d858cf98974888d99590ffe30314ce
- PARTITION 45fad23a5a01f3641e5a21c25bc7066b6fffe6956906c6da4ed292679c1bf5e1
- PENDING 5ceee30ecf7cb273acda4740c2ff4542da3549ed29300ec4eff20bffe69c093f
- 原slab0 3949442a79dfed352306147be1c05e85a1ab42763a7ed5e3859db9a8fb93b0d7

下一批512实际结束后，可对**最新payments目录**再运行
`audit_closed_filling_supplements.py`，传第一与第二批`--refinement`，
读取主阶段已结束status的更多直接付款。旧已付行会按图识别重叠并扣除，
不要把计数相加。输出新唯一目录，不覆盖前一个分割。
保持原ALL-PENDING-SNAPSHOT不变；它仍是完整原11179来源映射，不是最新
7662未付列表。任何新抽样/严格复跑必须排除已付图，不能重复原11179阶段。

## 全局未付边界保持

三个全N25必要族必须真实耗尽、全部slab精确union、输入绑定不变；
164离线障碍与有限块付款运输到最终union时要按完整规范面数组及center
计数重新核查，不沿用局部row id或重复加付款。
B16达到图用精确rstar核心/已验收91补全族，不能strict>U误排。
V24隐藏h的|h|≤5ρ−1仍未接入力内核，不冒称已使用。
四族闭合+任意覆盖源接口+精确上界合成前，n25/goal不complete。
n23/n24无条件全局证明仍未完成；n11未动。

用户交付说明和最新推进记录在项目less outputs中已更新到14:24。
