# members/stress-audit — STATUS

scope: 只审 lead 的 conditional sharp-stress 接口（本 36 边网络）。不写 shared/lead/claims/n11 目录；claims 记在台账 C971–C981。

## 状态

- 三条主义务（cos/Hessian 机制；stress_interval↔probe 同一性 + 独立 mixed 证书；七轨道平衡/T/分支 guard）**全部独立复核通过**，未发现 lead 侧承重错误。
- 扩展：root-T Krawczyk 证书（我自写区间核复核 q≤4.0874e−28、K⊂box）、full-simplex 网络证书族 60 份（全部 margin>0，最小 2.926037875967e−04）、333↔6-face 桥接身份（组合层面成立）。
- 最终口径（已按 lead 澄清修正）：**固定图 lower bound 是无条件的**；缺的是 cover→graph 类接口与 upper coverage/全局。
- 修正记录：我自己的 3 个实现错误（消元双扣、D=9L−π、max‖d‖² 多乘 D²）已在 REPORT §4 记录；报告里两处过强表述（T 分支“精确线性”、Taylor 余项“交错级数”）已改。
- 台账：C979 supersedes C974（T 分支改正）；C980 supersedes C977（无条件固定图口径）；C971/C972/C973/C975/C976/C981 为各项证据。

## 复现

见 REPORT.md §7（step1–step14，`$env:PYTHONIOENCODING='utf-8'`）。

## 未决（不在本 scope）

cover→graph 类接口（9 边界切弧 ⇒ 图与 gap∈(0,L] 域）、13-face/upper coverage、k10/k11、其它网络分类、r_D(12) 全局判定。
