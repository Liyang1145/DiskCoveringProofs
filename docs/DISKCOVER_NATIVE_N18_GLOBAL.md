<!-- SPDX-License-Identifier: MIT -->
# n=18：全局最优性与精确重放

设 $t_*$ 为[独立复验的 174 维整数多项式系统](DISKCOVER_NATIVE_N18.md)
在锁定根盒中的唯一根的半径平方坐标。十八个相同闭盘覆盖单位闭盘的
精确最小半径为 $r_D(18)=\sqrt{t_*}$，约 $0.290167717640566729$。
这是计算机辅助证明；没有假设任意严格反例对称，也不是 Lean 形式化。

**达到性。** 独立核验器重建整数接触与驻点方程、收缩及 72 条
精确接触杆。定向三角链和 12 个圆弓覆盖整个闭单位盘；不使用
浮点采样的通过记录。

**任意圆心归约。** 若存在半径 $r<\sqrt{t_*}$ 的覆盖，先取
$r<\rho<\sqrt{t_*}$，用严格余量依次正规化与扰动，再取不可约
子覆盖。无返回引理和面内补点产生简单圆盘三角剖分，边界拥有者数
必在 11、12、13；补点不改变边界，所有见证杆仍长至多 $\rho$。
这些论证及角度安全剪枝见[原生拓扑普查](DISKCOVER_NATIVE_N18_CENSUS.md)。
使用更松的有理上界只会放宽角度必要条件，不使任何力证书或局部
隔离叶要求的精确半径范围失效。双遍历规范面表逐项相同，分别
保留 397、6,971、7,191 个轨道，共 14,559 个。

**连续域排除。** 唯一候选图先经同构映射到原始标签，再用反射
（如需）及旋转把原始候选锚点零置于 $(1,0)$。其
[完整角盒分支](DISKCOVER_NATIVE_N18_CANDIDATE_REPLAY.md)逐项验收
609 次分裂、548 个精确力叶及 62 个
[隔离邻域叶](DISKCOVER_NATIVE_N18_ANCHOR_ISOLATION.md)。每个非候选图
的全角域由精确有理力证书排除。全量归档用新鲜的原生普查逐项绑定
所有记录，拒绝遗漏、重复、错误重标、未决盒或不严格的不等式。
其中 14,359 个非候选图由本库新生成力证书；候选树和剩余
199 个困难非候选图以参考作者的数据作数值见证输入，
接受仍由本库重算每项不等式；不运行原作者的验收程序。

由此排除任意圆心下的所有严格改善，匹配同一个根的达到构型。

## 一键重放

```sh
base=https://raw.githubusercontent.com/VonEquinox/DiskCoveringSolve/089584973f41e6374ce110f6e5b5ee456df19352/cover18/proof_bundle/core
curl --fail --location "$base/root18.json" -o root18.json
curl --fail --location "$base/candidate18_tree.json.gz" -o candidate18_tree.json.gz
python verification/n18/replay_global.py root18.json candidate18_tree.json.gz
```

根与候选树输入由锁定哈希校验；其余所有非候选图证书随本库提供。
验收只需标准 Python 与 C++17 编译器，不需要数值优化器或 Lean。
任一环节不通过，不给出全局最优通过记录。
