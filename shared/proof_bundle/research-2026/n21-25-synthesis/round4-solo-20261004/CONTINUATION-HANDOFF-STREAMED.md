# 最新接续：B14完整必要目录、残余补全与B15流式存储

目标 active；不使用子代理；顺序仍为 n25 → n23/n24。
n11未启动、编译或修改。目录中的20261005为沿用标识。
本记录更新 EIGHT-ROD 交接中的运行状态，旧数学成果不撤回。

## 最新覆盖归约与运行状态（优先于下方历史段落）

新增的`UNEXPOSED-ORIGIN-CENTER-SOURCE.md`给出关键实际覆盖必要条件：
边界圆心模长≥1−ρ，任何外露内部圆心模长≥1−3ρ；
ρ≤U25<1/4时它们的盘均不含原点。原点必须由一个未外露圆心覆盖。
投影、严格余量和中心面星形补点都保留覆盖原点的旧标签。
因此实际反例的外露中心数V≤24。**不是任意弱图几何不可实现结论。**

`refine_collar_origin.py`，会话22223已实际exit0：
`n25-B14-complete-origin-refined-residual-20261005-v1/VERIFIED.json`。
完整93441残余再分割：

- V25的87333图，由实际覆盖原点条件支付。
- 剩6108：V22有13、V23有299、V24有5796。
- 1−4U25严格正；已核查已知N25/B16达到图仍有24外露中心而保留。
- 带纯内部面的图不能把全部中心数当外露中心数；测试已明确区分。
- quarter及更大半径拒绝；在r=1/4的局部杆等号控制不能误排。
- 原点条件报告SHA：
  b493bb908ba52f1a4a1318efd1eeec4392a5e354e04fa95dfbb5a83b95e6e325。
- 新残余SHA：
  4c62bcd18e588aa31f9dec40adf4e11624644c439f374db9a72d87dd02632514。

V24另有必要条件：唯一未外露中心h覆盖开核心 |x|<1−4ρ，
故 |h|≤5ρ−1<5U25−1。尚未加进力内核，不能计作已有力树。
未来若加固定原点锚，几何原点(0,0)不是0号边界中心或q0=(1,0)。

本轮六项会话已收取：

- 34216/B16八杆、32524/B17八杆均真实2百万内存保护exit1，
  完整目录不存在；禁止把日志计数当全集或恢复点。
- 5476/旧25障碍B14实际exit0，完整必要弱图103993。
- 94521/百族补全实际exit0：89族严格闭合，11族pinched未处理。
  这些100个父id与最终6108残余没有交集，不重复处理。
- 8917/真实20族实际exit0：19族严格闭合，1族pinched未处理。
  其中552、555、581、583、586、589这六个属于最终6108，
  均已有CLOSURE，可直接整目录逐id再付款；不能重复相加。
- 50651/全部172092图的力提议实际exit0：
  125363排除候选、46729待处理。整阶段独立重放尚未做。
  优先对最终6108中的排除候选选择性独立重放，避免重放已付V25大类。

现仅两项native仍活（已逐命令ps核对）：

|会话|Linux PID|任务|
|---|---:|---|
|66157|444|B14八杆25障碍|
|12893|3757|B15流式八杆9障碍|

新增原点守卫源已经生成并编译成功，会话41852已exit0：

- `cover_origin_obstruction.inc`：只在n=25且显式开启时使用。
  检查B中心的闭邻域是否覆盖全部25标签；实际覆盖必须否定这个条件。
  样本仍核查B面顶点并集与邻接掩码相等。
- `derive_origin_streamed_collar.py` → `peel_origin_streamed_collar.cpp/linux`：
  旧递归、角守卫、稀疏守卫、slab存储不变，新增实际覆盖条件剪枝。
  argc15，末参数origin-cover-screen为0或1；前一参数仍slab-limit。
- 新schema：`complete-cover-origin-collar-sorted-chunks-v1`，
  元数据明确只用于实际覆盖，不宣称弱图几何排除。
- `derive_origin_chunk_merge.py` → `merge_origin_collar_chunks.py`：
  全部旧块校验/规范码/零退出/精确归并检查机械保留，
  新增原点scope、U、样本核对和开启时所有剩余V≤24的检查。

**新守卫还未做独立native控制，未启动生产。** 下一步必须先控制：
开关关闭与旧完整小族相等；N≠25不改变小族；真实达到图及重标号
保留；cpp掩码与独立Python逐图一致；完整N25控制、错误flag/
node-limit/不完整输出拒绝。通过后只替换真实失败的B16/B17，
不要热改或重复启动活B14/B15。

## 耳覆盖压缩试验（不能与已有族付款相加）

`ZERO-BUDGET-EAR-COVER-SOURCE.md`：
无新增内部中心的简单孔填充，面双邻接为树；大孔至少有两个
不相邻耳。枚举各孔耳选择给出完整必要分支覆盖。
N>V时明确拒绝此零预算结论。

- `probe_zero_budget_ear_covers.py`，g0控制全部217完整型有显式覆盖：
  单耳9分支仍2未付；双耳27分支全部支付。
- `derive_zero_budget_ear_kernel.py`提取同一函数为
  `zero_budget_ear_kernel.py`，无优化器导入。
- `replay_zero_budget_ear_cover.py`独立标准库接受：
  `n25-B14-g0-ear27-exact-closure-20261005-v1.json`，
  11严格树+16整数负环，固定族下界闭合。
  单耳9报告仍pending2，未误称闭合。
- g548的1430完整型也逐型覆盖，但双耳35分支中仍14未付；
  `n25-B14-g548-ear35-exact-partial-20261005-v1.json`明确不闭合。
  g548本身已有1430型穷尽闭合，且V25又已由原点条件支付。

后续不要继续为V25尝试更深耳覆盖。若扩展到条件子节点，原
`simple_holes`要求每面含B，不能直接用于已有纯内部耳面的混合
部分复形；该断言失败不是排除。须另派生并控制泛型流形检查器。
当前6108实际残余V<25，零预算耳覆盖不适用；必须处理新增1–3中心。

## 真正完成的目录

旧12障碍B14，会话96878、Linux35578，实际exit0，已收取终止。
目录：`n25-B14-sparse-collar-search-resume-20261005-v1`。

- 172092个完整必要弱图，原生产接受器已核查规范码与映射。
- GROUPS SHA：a52729cbd01664e744eac859af86e425b389d50f51316a4276161f497c7b85e2。
- 原native目录SHA：42a97b039ad5a04bd4d3be6a93f6c0ca4581b2a168dcc98bd9981d31da065938。
- 全部冻结输入已再次核对不变。
- **这是完整必要外露面目录，不是172092个完整盘，也不是B14下界完成。**

## 已验收的新数学进展

完整旧目录的首20000图：
`n25-B14-old-complete-force-prefix20000-exact-20261005-v1/VERIFIED.json`。

- 16447个严格弱图下界逐树标准库精确重放。
- 3553个待处理；数值可实现诊断没有当成覆盖或排除。
- 全部首20000个父目录身份映射核查。
- 首1000的809 strict /191 pending被此较大前缀包含，不能相加。
- 仍不是完整证明阶段receipt；完整阶段会话50651仍在运行。

首1000待处理中的六个固定外露面补全族已闭合：

|父弱图id|完整型|闭合证据|
|---|---:|---|
|0|217|n25-B14-complete-g0-collar-closure-20261005-v1.json|
|2|217|n25-B14-first-pending-collar-payments-20261005-v1/parent-0000002/CLOSURE.json|
|3|429|同目录parent-0000003/CLOSURE.json|
|7|429|同目录parent-0000007/CLOSURE.json|
|17|429|同目录parent-0000017/CLOSURE.json|
|21|429|同目录parent-0000021/CLOSURE.json|

共2150个完整型，逐型严格证书、独立重放、盘结构/规范码/
完整外露面映射审计均通过，pending0。
这些是固定 N25/B14 简单盘补全下界，不能改成弱图几何不可实现。
与既有B14/8385和B16/91族的区别与运输条件不变。

会话94521继续首1000待处理中的接下来100族：
`n25-B14-next100-pending-collar-payments-20261005-v1`。
实际Python协调进程12592；逐族STATUS与CLOSURE为独立检查点。
先收取其实际终止和SUMMARY，不重复启动或覆盖已写证据。
node limit是每族1000000；限制失败、未处理或待证明都不计付款。

## B15流式替代已验收并上线

旧八杆B15：会话83277、Linux704，真实2百万内存保护exit1。
旧B16/两障碍/三角帽：会话79193、Linux2049，也真实内存保护exit1。
两者保留日志和终止记录，没有完整目录，也不能用内存计数恢复。
旧B16终止的native_pid=null仍是旧正则遗留，不是未启动。

新文件：

- collar_chunk_storage.inc：有序slab，生产100000行，20GiB输出硬保护。
- derive_streamed_collar.py → peel_streamed_collar.cpp/linux。
- merge_collar_chunks.py：真实exit0后逐块校验、规范码重放、精确流式集合归并。
- test_streamed_collar.py：四个完整小族集合相等，真实跨块重复去除，五项拒绝。
- streamed_storage_gate.py：重新核对完整小例、实际终止、各块/集合与冻结源。
- derive_streamed_driver.py → run_streamed_eight_search.py。

控制：`n25-streamed-collar-controls-20261005-v1/VERIFIED.json`，已exit0。
SHA：0e4f2ced660a412eb25202b431322e0ce3ec9c14fced4c929e59276889d2c049。
原角守卫、稀疏映射与递归分支没有变化，存储不参与剪枝。

生产会话12893，Linux3757，Windows Python18792，WSL proxy20432：
`n25-B15-streamed-eight-sparse-search-20261005-v1`。
实际参数 N25/B15、node-limit0、cap8=4058615、slab100000。
已经实际写出多个slab，但**slab是前缀，不是完整目录或独立类型数**。
不要修改其绑定文件或重复启动B15。

pins：

- streamed cpp：709fc136c48b42d000338af8cb2185083d22a62a59280b40c2ef6f4f9f99d9a7。
- streamed binary：ca3ebfbaa3a4888ee793f3d8ff0ce94c33c9e260f3af39c719a9b8d193331d7f。
- streamed driver：862781f4f25ece07f6b6db1582901ff76abf75d5995bb735334df217d8d88659。
- storage gate：e98139a71753bb16ec1f5badb219f3803ce7992d0f0068237f86dfc9b8484383。
- 原八杆源/二进制/producer pins仍为前一交接的31df.../0562.../f448...。

## 分批证明接口已通过实质控制

- batch_streamed_collar.py：逐行扫描完整union、父身份绑定、最多4096/默认128图批次。
- derive_collar_batch_proposer.py → probe_collar_batches.py：
  仅适配N21小例缺失候选文件，N25候选控制、力树构造及精确接受不变。
- audit_collar_batch_payments.py：逐父行比较、再次精确重放、严格/未付双台账。
- test_collar_batches.py：
  `n25-collar-batch-payment-controls-20261005-v3/VERIFIED.json`，实际exit0。

18个完整小例图分成四批，全部仍pending，没有误称排除；
另3个真实N25严格算术控制重放通过，真实N25达到型保留；
错阈值、非零退出、缺失/重复批次、自洽但错误锚映射均拒绝。
v1因旧N21候选文件不存在失败；v2是较弱中间控制，不作最终入口。
尚未给B15生产全集支付下界，因为生产还未完整结束。

## 完整旧目录逐图再付款：已验收

`filter_complete_collar.py`不是新枚举；它对完整旧172092图逐图检查
25障碍严格源注入、独立8杆整数负环、七个已付严格固定补全族。

第一遍会话9691在maps-000324遇WSL proxy exit1且stdout/stderr均空。
v1目录保留，没有VERIFIED，不算完整。
真实pgrep检查未见遗留sparse matcher；没有重启任何生产枚举器。

新缓存接受器：

- cached_collar_maps.py：校对每条缓存请求与当前父图相等，原真实exit0，
  新一遍仍逐图验证所有正映射；已完成批次不重算native。
- derive_cached_collar_filter.py → filter_complete_collar_cached.py：
  数学分类与完整父行检查机械保持不变。
- 后端失败只导致该批没有稀疏付款；图仍经独立角/补全检查或保留未付。
  不把失败或未知匹配当成排除，也不伪造新native exit0。

会话39712已真实exit0并收取：
`n25-B14-complete-old-collar-paid-partition-20261005-v2`。

完整172092行逐图验收、无缺失或重复的分割：

- 严格稀疏源注入68099。
- 独立整数8杆负环10547。
- 完整简单盘补全族下界5（并非弱图几何不可实现）。
- 尚未支付93441。
- 68099+10547+5+93441=172092。

`VERIFIED.json`含很大的冻结绑定字典，**不要整文件打印**；
只提取所需标量或开头几十行。下一轮从`RESIDUAL.jsonl`处理真正
未付父图，不必等待新B14枚举。其父图id仍是原172092目录的id。
首20000的16447力树与本分割有重叠，不能相加；已闭合补全族
也可能已有严格稀疏付款，计入全集时需要逐id分割。
第一遍失败日志不作最终余额；v2所有缓存请求均逐图核对相等，
所有正映射再次核查，源、库、证明与缓存字节再次核对不变。

最终pins：

- 完整再付款报告：8fe23d28b46061dafb04593996aefff165d9a541d05416260141c4ef856dd78d。
- 残余JSONL：df85996dd00f9a873ddc075c9709af5ff6abd7e1ee9815ba43e030216acc3186。
- 付款JSONL：4953acd68de794f7ec75791299621f87f3602d2683cc9edccebb38ee5afda791。

## 已切到真正残余的补全选择

新机械派生器`derive_real_residual_closer.py`生成
`close_real_residual_collars.py`；原补全/力树/独立重放/闭合步骤均未改。
仅在首20000的3553待处理图中，取真实93441残余的交集，并排除
仍活百族作业INPUT-BINDINGS中已计划的所有父id。
排除后905个候选；首20个为：
548,549,550,552,555,568,571,573,576,577,
578,579,581,583,586,588,589,590,888,976。

会话8917：
`n25-B14-real-residual20-collar-payments-20261005-v1`。
实际启动，尚未收取终止；不重复启动。其新目录不会与百族目录
覆盖，父id选择也不重叠。枚举限1百万，任何限制/未处理/未付
均不称闭合。优先收取其逐族STATUS与最后SUMMARY。

## 仍活的五项native搜索

最后逐命令ps确认；运行状态需要下次再次实查：

|会话|Linux PID|任务|
|---|---:|---|
|66157|444|B14八杆25障碍|
|34216|2443|B16八杆2障碍|
|32524|774|B17八杆20障碍|
|5476|36899|旧B14三角帽25障碍|
|12893|3757|新B15流式八杆9障碍|

会话50651（Windows Python17928）：
`n25-B14-old-complete-force-stage-20261005-v1`，
冻结原probe_groups对全部172092图，limit1、route-weak-realizable，
内部数学线程数1。完整SUMMARY尚未产生，禁止作完整receipt接受。
结束后按原GROUPS用冻结replay_group_stage独立重放，并检查全图覆盖。

## 下一步

1. 优先从93441个真正残余图继续付款，收取8917真残余20族、
   94521百族闭合；
   接着核对全部活作业，39712已完成，不重复启动。
2. 首1000待处理批次含一些已被新25障碍支付的旧待处理图；
   后续补全选择应先与真实93441残余取交，避免无必要的重复付款。
   现百族工作本身仍有效且在运行，不热改它。
3. 残余弱图能实现时，恢复全部内孔补全；未处理pinched情形仍未付。
4. 活B16/B17若确实内存失败，再派生新的流式驱动与各族门槛；
   当前流式driver只允许B15，不能热改它放行别的B。
5. B15真实exit0后完整块归并、分批力树与独立付款台账；守卫终止不算完成。
6. n25四必要族、全部残余、源覆盖运输与全闭盘上界合成后，才可报全局证明。
   n23/n24尚未因此自动完成；goal active，不blocked，不complete。
