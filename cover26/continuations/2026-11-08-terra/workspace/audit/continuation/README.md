# n26 原生接纳链的缺口与接口检查

`interface_gate.py` 是针对 2026-10-13 midarc 头的拒绝式预检，不是证明检查器，不会接受全局定理。它要求 final/current 的原始 SHA、特定 schema、同一个精确候选区间、同根 Rstar 条件作用域，检查未决根、逐族未决分支及全局未付标志。它还无条件报告几何/连续域数学重放与全局合成尚未实现。因此即使人为伪造所有状态字段，也不可能产生接受结果。新版本必须有新的适配与可信关联，不能把新结果套用旧哈希。

执行：

    python -m unittest -v test_interface_gate
    python interface_gate.py --formal-final PATH --formal-current PATH

第二条命令目前固定拒绝并返回非零。文件 SHA 仅绑定字节，不证明该文件的数学内容。八项小型控制覆盖伪造成功、缺件、旧半径/作用域替换、未决根/族、布尔值混作整数和缺失全局义务；它们不是覆盖完整证明的测试。

原 `recheck_midarc_source_current.py` 的实质接口包括：

1. 读取 current 的原始 `files` 并逐一重哈希，父 current/独立 final 的原路径、SHA、执行器及候选层保持绑定；另需明确路径重定位，不改历史字节。
2. 几何源必须对应真实父前沿；MANIFEST 关联父 current、final 与原 frontier，且原 frontier 等于冻结副本。几何接受、publication 和 semantic replay 字节一致，执行冻结数学程序，不能只查这三个哈希相等。
3. 对全部 5637 个原始前缀重建和重新核对可行子分支；680 个新严格排除加 4957 个未付前沿，另核查全部 9172 原物理数与 shadow 情况、逐族守恒和未支付兄弟。必要时精确重演 5 个书面几何证明与界常数。
4. 中间收据必须是同根 Rstar 作用域，不能将其升格到原 U；同根半径区间、`radius_upper`、候选身份与父链一致。候选16根、每根历史、终态负担、52坐标局部余量、87全型和215收据等原接口不得重标或覆盖。
5. final 是一个阶段性账本，原作者明确将 unrestricted reduction、完整目录、global lower bound 和 optimum 设为 false。全局证明还要独立支付任意覆盖的投影/严格余量/不可约化及拓扑穷尽、所有竞争支和候选完整角域、同根上界与局部隔离；其结论不能由该 final 的存在推得。

本次以恢复的 final 和缺失 current 运行，final SHA 与保存清单相符，但记录显示 16 个未决候选根、4957 个未决条件前沿，各族仍未闭合。当前未读取到数学依赖，也未进行新鲜完整的几何重放。算术线的 344 OPEN 属独立账本；不得合并抵扣几何线。

本次还从离线 Git 对象库恢复 `native/verify_midarc_source_geometry.py`、`native/n26_midarc_source_accounting.py`、`native/n26_candidate_identity_after_midarc.py`，其中 accounting 的 SHA256 `ceb35e425deb35dddc787028b54220d3bc180fd4b535f95b2a5c535005a4e92c` 与 formal final 中记录的源匹配。几何执行器本身明确区分其 own acceptance 和后续 current/final；其十个拒绝控制包括候选层旧根替换、缺失连续弧证明、shadow 框架偷换、重复支付以及将条件源错误升格为原 U。它仍依赖不能离线取得的 `audit_prefix_origin.py`、`n26_force.py` 等文件与原始证明输入，故未运行其完整数学主程序。
