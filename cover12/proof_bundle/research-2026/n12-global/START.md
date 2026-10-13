# n=12 — 全局最优性研究入口

状态：2026-09-26建档，供新会话启动；本次文档整理没有开始全局证明或重跑旧证书。

## 目标与口径

D={x∈R²: ||x||≤1} 为单位闭圆盘。r_D(12) 是能以12个等半径闭盘覆盖 D 的半径下确界，中心允许任意位于 R²。

目标：找出严格定义的最优半径R*，证明在R*达到，并排除所有r<R*的覆盖。不限对称性、边界盘数、固定拓扑或一般位置。任何域缩减必须先证明。局部最优/族内最优/数值夹逼不是完成。

[本题 STATUS](STATUS.md) / [本题 DEAD](DEAD.md) / [新会话提示词](NEW-SESSION-PROMPT.md)。根当前结论见 [STATUS](../../STATUS.md)。

## 已有资产（原位只读复用）

| 对象 | 入口 | 使用边界 |
|---|---|---|
| C182精确有理构型 | [cert_n12_othern.json](../session2/n1314/cfg/cert_n12_othern.json) | centers_dec17为认证对象，R_float不是精确定义 |
| 历史认证结果 | [cert_n12_othern.json输出](../session2/n1314/out/cert_n12_othern.json) | bb_ok及D2与cover诊断必须分开解读 |
| 批量历史输出 | [cert_all.json](../session2/n1314/out/cert_all.json) | 是旧证据，不是本次重跑 |
| D1/D2入口 | [certify_cfg.py](../session2/n1314/py/certify_cfg.py) | 依赖cert_cand/cert_bb/certlib；先读后跑 |
| D3入口 | [enc17.mjs](../session2/n1314/js/scale/enc17.mjs) | 依赖根n11/upper/enclose17.mjs；审计Number转换后的字面一致性 |
| 历史状态/报告 | [STATUS](../session2/n1314/STATUS.md)、[REPORT](../session2/n1314/REPORT.md)、[DEAD](../session2/n1314/DEAD.md) | 含旧公开值/搜索结论，禁止照抄新颖性或局部最优性 |
| 候选来源 | [n12_d3_kkt.json](../../flash-n11/members/othern-scout/s3/n12_d3_kkt.json) | 仅作为来源，不能代替认证对象 |
| 文献对照 | [pegg_n12.md](../../lit2/pegg_n12.md) | 私人通信转述的代数对照，非最新文献全查 |

## 第一阶段：核对资产，然后选结构义务

1. 用 claim_get 读取C182/C191及当前状态；比较精确输入、输出和脚本，核对下述诊断差异。先用已知答案/正负对照校准需要复用的器械。
2. 有限复现已有上界，日志写到本题新目录，不覆盖旧输出。本阶段要回答“已有上界确实针对哪个对象、由哪个完整命题支撑”，不是增加小数位。
3. 提取候选的实际边界覆盖/内部极值/接触结构；先检查退化，不把猜测的9+3或D3结构当成全局WLOG。
4. 按需读 n=11 的 [主证明](../team-current/lead/N11-GLOBAL-OPTIMALITY-THEOREM.md)、[任意覆盖归约](../team-current/lead/UNRESTRICTED-PROOF-ASSEMBLY.md)、[审计入口](../team-current/lead/FINAL-PROVENANCE-AUDIT.md)，区分通用引理与依赖n=11的分类。未证明的迁移只写条件命题。
5. 明确原目标、当前子命题及其间缺失蕴含。优先完整排除一个构型类、消去参数或建立通用接口；不默认扩大随机搜索或照搬旧证书。

### 可复现命令（从工作区根执行；本次只核对路径/CLI，未执行数学计算）

以下D1/D2显式传入C182阈值，以免CLI默认上取整到24位变成较弱目标。创建新的日志目录；避免用旧输出文件名。

```powershell
$runDir = 'research-2026/n12-global/evidence/replay-' + [guid]::NewGuid().ToString('N')
New-Item -ItemType Directory -Path $runDir -ErrorAction Stop | Out-Null
py -3 -B research-2026/session2/n1314/py/certify_cfg.py research-2026/session2/n1314/cfg/cert_n12_othern.json --key centers_dec17 --nd 17 --claim 0.361102963744508672616920293904 > "$runDir/c182-d1-d2-replay.txt" 2>&1
node research-2026/session2/n1314/js/scale/enc17.mjs ../../cfg/cert_n12_othern.json > "$runDir/c182-d3-replay.txt" 2>&1
```

D3的输入相对 **脚本URL** 而非当前工作目录解析，因此保留 `../../cfg/...`；其源代码将字面转Number，必须检查输出的 literal-vs-certified differences，不能先假设与原精确字面同一对象。而且该 differences 诊断比较的是 **Number的最短字符串与toFixed固化值**，不是原始JSON字符串；即使为零也不足以证明输入身份。必须将原 centers_dec17 字符串对应的有理数与最终 certified 整数逐坐标直接比较，必要时换成直接读字符串的独立核。不以多次相同读数替代输入身份检查。先检查Python依赖可用，不擅自安装包；长计算设任务级超时并后台运行，timeout不是数学否证。

## 不随建档自动成立的猜想

9个边界盘+3个内部盘、D3对称、接触图完整性、局部驻点精确唯一性、最优构型唯一性，均未在本次确立。上一会话的路线建议只是建议，不是已经登记的n12归约定理。

## 文件维护

STATUS只记当前；DEAD按否证/撤回/实现/方法/预算分类；bulk logs放evidence或独立任务目录。claim账本继续用工作区统一账本，不复制新账本。复用证据采用原路径+哈希，不批量移动旧文件。插件按关键义务使用，无固定打卡配额。
