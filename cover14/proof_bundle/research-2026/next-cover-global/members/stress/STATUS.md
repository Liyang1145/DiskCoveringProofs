# members/stress — STATUS (n14 bearing-method 可行性)

Lead 指派：新主攻 n14（proof C1142：任意 r≤U=.33173203427623414 投影 k10/11；sharp 候选 = 14 中心/10 边界锚/活动内孔图）。
本目录职责：**bearing-method 可行性小实验**（数值仅路线诊断；不做全面搜索；candidate 在降维精确根、topology 在完整图枚举）。
只读旧资产：`session2/type14/out/*`、`research-2026/lead/verify_c407_lead.py`。旧 n11/n12/type14 全只读。

## 结论（已交付 = REPORT.md）

1. **校准通过**（一候选一校准）：`stress_core` 在 n12 已证候选上复现 0.0116599219 / 6.68400214e−05 / 2.3661546922e−03。
2. **独立画像**（采纳 Lead 更正，弃用 candidate 画像）：D2 轨道 **2×4+3×2**；10 anchor（owners 见 REPORT §2）；D 内 Voronoi 16=14 活跃+2 slack；
   **cap 活跃 gap={4,9}**；L*−L_U 差 3.49e−17；5L*>π。
3. **决定性判定（C1145, gap/方法限制）**：r*-cap KKT 锥**空**（63×62 nullity=2；唯一非负核方向在两 active gap 上导数为正 +0.0096/+0.3034；另一方向含负元）；
   子网络 106 个硬 KKT 可行 0 个；16face 诊断 λ_min(M|1⊥)=−4.8124e−3（负方向来自 d=5 对径对 cos=−1）；局部 Hessian 1⊥ λ_min=−2.383e−3。
   ⇒ n12 式「单一常应力全域凸性」**不能原样搬用**；这是方法限制，不是判死。
4. **接口缺口（C1146）**：无精确 r* 根 box；活跃面的拓扑保证无文档；kkt_clean 权重非图应力；我的核为数值版。

## 文件

- `py/stress_core.py`（LP 应力 + Schur + 有理 c_d + Gram 基特征值）
- `py/calib_n12.py`（校准，只读）
- `py/n14_extract.py`（几何/锚/面提取；无副作用）
- `py/n14_portrait_stress.py`（画像，logs/n14_portrait_stress.txt）
- `py/n14_stress_cone.py` / `n14_stress_cone2.py`（锥与 KKT 探索；含早期含错 g 的版本，**以 final 为准**）
- `py/n14_cone_exact.py` / `n14_kkt_rank.py` / `n14_kkt_final.py`（决定性高精度判定）
- `py/n14_negative_direction.py`（负方向来源）
- `py/n14_subnet_search.py`（子网络扫描）
- `evidence/*.json`, `logs/*.txt`

## 已知自身错误（已修）

- `n14_portrait_stress.py` 初版 `r = norm(c)` 用错变量（用成上一循环的 C[13]）→ 断言失败；已修。
- **g 公式初版多加了 τ_0**（应为 g_k=Σ_{i=k+1..9}τ_i，因 δθ_10=0）；由 g_9≡0 检验发现并修；含错版本的 LP infeasibility 结论作废，以 `n14_kkt_final.py` 为准。
- `n14_cone_exact.py` 初版取错 Vt 行（应取最后 null_dim 行）；已修。
- 早期 KKT LP 出现过软/硬 LP 容差矛盾（z*=1e−9 vs infeasible）→ 改用核向量精确代入判定。

## 下一步（待 Lead 指派）

(a) 混合 core+anchor 松弛的应力锥小实验；(b) n14 图核转精确有理/区间版；(c) 复核 three-hub/topology 的 n14 侧产物。
