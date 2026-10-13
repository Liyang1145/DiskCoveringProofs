# 最新接续：八杆必要搜索与两个闭合补全族

目标 active；继续 n25 → n23/n24；不使用子代理。n11未动。
本记录取代上一份 COLLARS 交接中的运行状态；旧数学成果不撤回。
不要根据目录名推断完成相位，不重复启动活作业。

## 已通过的实质门槛

- 新C8=4058615/10⁷，精确sin(πC8)>4U25。
- 8杆角守卫：361项原/新native及独立整数负环对照，
  148项比旧2/4/6杆更强的排除；4个已知达到图/重标号控制均保留。
  18项完整no-screen集合相等、2项完整N20/B14参考运输/角排除，
  7项坏证书/参数拒绝。最终控制
  `n25-eight-rod-collar-controls-20261005-v2/VERIFIED.json`。
  v1未完成，曾遇WSL proxy exit1且无诊断；v2只在真实ps确认无
  对应native且无目标输出之后有界重试小例。生产不使用此重试。
- B17有界发现2931图，首64严格证书+独立重放，压缩20个严格障碍：
  `n25-B17-new-sparse-library-20261005-v1/LIBRARY.json`。
- 四族八杆+稀疏守卫已各通过新鲜整库数学接受、N25显式映射、
  另序存在性控制、4项完整小族差集逐图注入付款及3项拒绝。
  不依赖旧慢速控制仍在进行的任何状态旗标。
- B14一个21中心/21面/七边内孔的完整N25补全族：
  4个新内部中心、8385个完整同构型、1297726递归调用。
  8385单DUAL整角域证书全部独立精确重放；随后全部盘结构、
  canonical_full、完整外露面映射相等、证书与绑定再审。
  `n25-B14-ring21-collar-closure-20261005-v1.json`，pending0。
  这只闭合该外露面图，不是整个B14。
- 新库
  `n25-paid-completion-family-library-20261005-v1/LIBRARY.json`
  已绑定B14的8385全严格族和B16的90strict+1exact-core共91型族。
  不是几何弱图严格障碍库，尚未接入native。
  源论证 `CLOSED-BOUNDARY-FAN-TRANSFER.md`：
  完整边界扇的面注入到同N/B简单盘，迫使其全部外露面恰等于源像。
  N必须25；B14排除≤U25完整实现，B16只排除严格短于精确rstar的
  完整实现。不能把B16达到型说成≤U25不可实现。

## 当前真实活句柄

最后ps逐命令/参数确认运行：

|会话|Linux PID|WSL proxy|任务目录|
|---|---:|---:|---|
|66157|444|16276|n25-B14-eight-sparse-search-20261005-v1|
|83277|704|21344|n25-B15-eight-sparse-search-20261005-v1|
|34216|2443|16184|n25-B16-eight-sparse-search-20261005-v1|
|32524|774|13864|n25-B17-eight-sparse-search-20261005-v1|
|96878|35578|11480|旧12障碍B14，resume目录|
|5476|36899|22260|旧25障碍/三角帽B14，union目录|
|79193|2049|5036|旧2障碍/三角帽B16，sparse目录|

四项新作业binary为 `peel_eight_rod_collar-linux`，从完整初始根，
真实node limit0，末参数4058615。各目录有INPUT-BINDINGS、
LINUX-NATIVE-IDENTITY；新PID已经在低号区，不能复用旧PID身份。
最后新B14约111百万calls/93365未付弱图，B15约141百万/1905986，
B16约21百万/545，B17约92百万/453；这些不是类型全集或完成率。
B15仍可能触发2百万内存保护；只能等真实terminal，不先报失败或完成。

旧B16派生驱动还有B14 PID正则和目标文件名，因此没有自动
LINUX-NATIVE-IDENTITY，实际字段N25/B16，实际native2049。
辅助确认在其 `EXTERNAL-VERIFIED-NATIVE-IDENTITY.json`。
不能热修正在绑定的驱动。它将来数学接受时还有可能被旧正则/名字
遗留影响，需按实际N/B和header检查；不能据错误console判断B14。

## 已终止失败，不重启

- 无守卫B15/B16/B17均因2百万弱图保护真实exit1，均没有完整目录。
  B17会话2693已收取terminal，native38328已不活。
- 旧三角帽+9障碍B15，会话48071，在101百万calls附近同样真实
  内存保护exit1。驱动记录native_pid=null是B14正则遗留，
  非“未启动”：native日志有完整进度。保留所有文件，不接受为完整。
- 本轮完成的75895(补全/8385证书/重放)、46457(8385结构映射审计)、
  7327(补全族库接受)均已收取exit0，不需要重跑。

## 冻结pins

- eight cpp: 31DF43F9AD8D4D6AA04538C787AEE096E992BC1D3116793E0CD2C6EAE22A6D26
- eight binary: 0562CDA8E823EA68A3D1554F863F041C8E87334284F7FD13574D9AB0471BE1B4
- eight angle inc: F3967185AA9AE2A81D0688971E697F7B0C2138DA3C3DDC8D55E8BBB6E8198AB2
- independent angle checker: 99E6EDB29D46A6F2B01DEE8D6F47EFF82D23A65D0F9FB5494BEC1487C93B2141
- eight producer: F448966D252E2517646FE9615DD936414F29FDE0EB492F8C146EAEBFC9DD6933
- eight controls v2: 284D94BE0EDC7A4FDB5A69D101AD30C6FC77B2F581D7378CFDF8EF7AF93A7F56
- B14 closed collar: C29E8FAD1AC8887791EB6645B86BB2C83A9ABA0388BDE0B0F94B0E1C6F925233
- two completion-family library: BA50D57879169399048AB36201394D1A4B8CF5D9D0BE4846F942C3412C4AEB72

任何活搜索绑定的文件都不可热改，包括test/acceptor/doc和二进制。

## 下一步

先观察七个活句柄，逐项确认真实终止、code、绑定不变、完整目录。
对真实成功的新八杆目录用冻结probe_groups/replay_group_stage付款；
仍可实现的弱图需恢复全部内部补全，不强报几何排除。

可在新文件/新二进制中接入已付完整边界扇库，需独立库接受、
匹配/坏映射、完整小例与真实N25补全运输控制。特别区分
严格几何子图付款和有完整盘补全前提的精确rstar付款。
当前库仅准备好，还没有任何生产剪枝计入它的付款。

不再启动重复生产变体；先使用当前四族加强作业的结果。
若某项实际内存失败，保留失败并选择有证据的下一种缩减/分块，
不能把未落盘内存数据当恢复点。三阶全局证明仍未完成，goal active。
