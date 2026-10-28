# SOURCE-MAP —— 源命题 → Lean 对象 → 证书 → 缺口

`level` 只记真实形式化等级：`kernel-proved`（无条件内核通过）/ `conditional-kernel`（带显式未证前提）/
`gap` / `numeric`。**未形式化 ≠ 假**；本表不评判 C924 的数学真假。

## 0. 对象与主命题（GUIDE §2）

| 源对象 | Lean 声明 | level |
|---|---|---|
| `Point := ℝ²`（欧氏） | `N11Formalization.Point`(`Definitions.lean`) | kernel-proved（定义） |
| `D = {x : ‖x‖ ≤ 1}` | `unitDisk` | kernel-proved（定义） |
| `Covers c r := ∀x, ‖x‖≤1 → ∃i, dist x (c i) ≤ r` | `Covers` | kernel-proved（定义） |
| 半径可行集合 | `feasibleRadii := {r | 0 ≤ r ∧ ∃c, Covers c r}` | kernel-proved（定义） |
| 强接口 | `StrongInterface R` | kernel-proved（定义） |
| 主命题 | `N11MainStatement R` | kernel-proved（定义） |

### 0.1 抽象层（**无条件** kernel-proved）

| 义务 | Lean 声明 |
|---|---|
| 强接口 ↔ `IsLeast`（**双向**） | `isLeast_iff_strongInterface` |
| `IsLeast` → `sInf = R` | `sInf_feasibleRadii_eq` |
| 非空 / 下有界（`sInf` 前置） | `feasibleRadii_nonempty` / `feasibleRadii_bddBelow` |
| `sInf ∈ set` → `IsLeast` | `isLeast_sInf_of_mem` |
| 任意 `r < R` 不可覆盖（含 `r<0` 分支） | `no_cover_below` |
| 由强接口得主定理 | `n11_main_of_strongInterface` |
| **中心可局部化到 `B(0,1+r)`** | `Covers.localize` |
| **`sInf` 无条件被达到**（极小化序列 + 紧子列 + `Fin 11` 个 eventually 交集） | `exists_covers_sInf` |
| `StrongInterface (sInf feasibleRadii)`（无条件！） | `strongInterface_sInf` |
| `feasibleRadii = [sInf, ∞)`，闭 | `feasibleRadii_eq_Ici` / `feasibleRadii_closed` |

### 0.2 锐化口径与**反漂移**（stmt-audit 的对抗审计产物，已进核心）

| 命题 | Lean 声明 |
|---|---|
| 强接口 ⟺ `R = sInf feasibleRadii` | `strongInterface_iff_eq_sInf` |
| **主命题 ⟺ 两条标量不等式** `sInf ≤ R ∧ R ≤ sInf` | `n11MainStatement_iff_two_bounds` |
| **警告：`N11MainStatement (sInf feasibleRadii)` 无条件为真且不含源常数** | `n11MainStatement_at_sInf_is_free` |

⇒ 任何「`r_D(11) = sInf feasibleRadii`」形式的表述**不是**源命题，不能充当进度。
承重形式是两条不等式：`sInf ≤ Rstar`（达到侧，C892）与 `Rstar ≤ sInf`（下界侧，C923+C921+C922）。
另：`N11MainStatement` 的第二合取项在已证达到性下由 `.1` 可推，**不是**独立内容。

## 1. `R*` 的定义链（GUIDE §2）

| 源对象 | Lean 声明 | level |
|---|---|---|
| 十六进制字面量 → 精确二进有理（dyadic 解码） | `HexFloat.parse`/`toQ`/`hexNatVal_lt_pow` | **kernel-proved** |
| 源字面量与生成器解码**逐位绑定** | `src_parse_binding` | **kernel-proved** |
| 盒半宽 / 中心第 6 坐标的精确值 | `decRadiusHex_toQ` / `decCenterHex_six_toQ` | **kernel-proved** |
| 包络 ⊆ 盒 `[中心 ± 半宽]` | `rootBoxCert_box_containment` | **kernel-proved** |
| checker 语义（数据 ⇒ `encHi < 19/50`） | `RootBoxCert.check_sound_lt_R0` | **kernel-proved** |
| 具体证书通过内核（`#print axioms` 仅 `[propext]`） | `rootBoxCert_check` | **kernel-proved** |
| 用证书数据实例化 12 维盒；`certBoxHi 6 < 19/50`（去 Krawczyk 前提） | `certBoxHi_six_lt_R0` / `Rstar_lt_R0_of_cert_box` | **kernel-proved**（数值）/ conditional（根） |
| **12 变量 TC/KKT 系统（`sys` 显式钉死）** | `TCSystem` / `adjointBlock`（Fréchet 导数） | **kernel-proved（定义层）** |
| **源构型的 11 个中心（C892 的目标对象）** | `centersOfRoot` / `C892Attainment` | **kernel-proved（定义层）** |
| **Krawczyk 收缩步（Banach 形式，**不依赖区间库**）** | `krawczyk_banach` | **kernel-proved（无条件）** |
| **12 变量 TC/KKT 系统在盒内存在唯一根** | `C891RootSpec.exists_unique` | **gap**（显式前提；残差已精确化为 §2.3 的三条区间不等式） |
| **`sys` 的显式解析式（`res5`）= 源文 §2 几何定义** | 定义层已对齐；**表达式树级语义桥**未做 | **gap，最高风险**（见 TRUST §5.1） |
| `R* := 根的第 radiusIndex 坐标`（`Classical.choose`，**非公理**） | `Rstar` | 定义（前提为假设） |

### 2.3 Krawczyk 解析链（G1 的**全部非数值环节**已无条件付清）

| 环节 | Lean 声明 | level |
|---|---|---|
| **Krawczyk 收缩步（Banach 形式）** | `krawczyk_banach`：`hlip`（`g = id − Y·F` 球上 Lipschitz `K<1`）∧ **残差条件 `η + K·ρ < ρ`** ∧ `Y` 单射 ⇒ `∃! x ∈ B(c,ρ), F x = 0`；**包含性 `K(B) ⊆ B` 在定理内部推出**，不用 Brouwer | **kernel-proved** |
| **导数算子界 ⇒ Lipschitz 界（中值不等式）** | `lipschitzOn_ball_of_deriv_bound`：`‖I − Y·(fderiv F x)‖ ≤ K` 在球上 ⇒ `g` 的 Lipschitz 界 | **kernel-proved** |
| **完整解析链** | `krawczyk_banach_of_deriv_bound`：可微性 + 算子界 + 残差界 ⇒ 球内唯一根 | **kernel-proved** |
| **球 = 证书积盒** | `closedBall_eq_pi_Icc` / `mem_closedBall_iff_box` / `mem_certBox_iff`（`E = Fin 12 → ℝ`，Pi 范数 = sup 范数） | **kernel-proved** |
| **实例化到源系统与证书盒** | `exists_unique_TCSystem_of_krawczyk` / `exists_unique_TCSystem_of_cert_box`（结论 = C891 的 `exists_unique` 字段，`boxLo/boxHi` 口径） | **kernel-proved**（条件形式，前提显式） |
| **行和 ⇒ ∞-算子范数** | `opNorm_le_rowSum`（`v = Σ_j v_j • single j 1`；Pi 范数 = sup 范数） | **kernel-proved** |
| **逐元素包络 ⇒ 算子范数界** | `abs_le_max_abs` / `opNorm_le_of_entry_bounds` | **kernel-proved** |
| **G1 完全组装** | `krawczyk_unique_root_of_entry_bounds`（任意有限维）与 `TCSystem_unique_root_of_entry_bounds`（源系统实例）：**逐元素包络 + 行和界 + 残差界 ⇒ 唯一根** | **kernel-proved**（条件形式，前提全为区间侧可算量） |
| **G1 前提的区间对象化** | `opNorm_le_of_interval_matrix`、`TCSystem_unique_root_of_interval_data`（前提 = `RatInterval` 矩阵包络 + 行和 + 残差） | **kernel-proved** |
| **源同一性（G0 可核验部分）** | `SourceIdentity.lean`：六条结构描述逐条具名 kernel 引理（`angleVec_eq_list`/`rhoK_eq`/`thetaOf_rec`/`{ringCenter,arcEnd,Uvec,hub0,hub1}_coord`/`fin9_succ_val`/`residual_comp_0..4`/`residual_eq_list`/`wPoint_coord`/`m_eq`,`d_eq`）+ `dist_point_eq_sqrt` | **kernel-proved** |
| **区间内核 M5b** | `Interval/Shift.lean`：`exists_shift_halfPi`（R2 移位选择，claim C984）；`Interval/Phase.lean`：四态表 + 两侧 ℕ 归纳（R3 核心，C987）；R3 的 `k:ℤ` 封装在 `IntervalZ.lean`（**Lead 侧交付**，C990）；**R4 未做** | R2/R3 核心 **kernel-proved**；R4 **gap** |
| **G1 导数义务的显式化** | `Assembly/G1HasFDeriv.lean`：`lipschitzOn_ball_of_hasFDeriv`、`krawczyk_banach_of_hasFDeriv`、`TCSystem_unique_root_of_hasFDeriv`——导数换成**供给的 `J`** + `HasFDerivAt` | **kernel-proved**（claim C989） |
| **源构件平滑性（G1 义务 (2) 一阶半）** | `Smoothness.lean`：`contDiffAt_coord`/`angleVec`/`thetaOf_angleVec`/`rhoK`/`UvecX`/`UvecY`/`dist_Uvec_hubOf`/`dist_wPoint_ringCenter`/`residual_0..4`/`residual`（非退化条件显式列出） | **kernel-proved**（claims C988/C993） |
| **C² 构件 + `TCSystem` 可微性（G1 义务 (2) 收口）** | `SmoothnessC2.lean`（`contDiffAt_fderiv_residualFun`）+ `TCSystemSmooth.lean`（`differentiableAt_adjointBlock`、**`differentiableAt_TCSystem`**） | **kernel-proved**（claim C995） |
| **搬运引理 + G1 最终形态（单套条件）** | `Transport.lean`（`residual_transport`、`differentiableAt_TCSystem_of_conditions`）+ `Assembly/G1Final.lean`（**`TCSystem_unique_root_of_final_data`**） | **kernel-proved**（claim C996） |
| **矩阵桥（G1 义务 (1) 可算形式）** | `KrawczykMatrix.lean`：`dotR_eq_sum`、`ratMatCLM`、`incrMat`/`krawczykMat`、`mem_krawczykMat`、`opNorm_le_of_jacobian_enclosure`、**`TCSystem_unique_root_of_jacobian_enclosure`** | **kernel-proved**（claim C1000） |
| **G1 完全有理化（语义前提清零）** | `Precond.lean`：`injective_ratMatCLM_of_leftInverse`、`dist_sub_eq_norm`、`norm_ratMatCLM_le`、**`TCSystem_unique_root_of_full_data`** | **kernel-proved**（claim C1001） |
| **预条件子单射性（R10 修正）** | `PrecondRight.lean`：`injective_of_norm_id_sub_lt_one`、`injective_ratMatCLM_of_right_contraction`、`krawczykMatR`/`mem_krawczykMatR`、`injective_ratMatCLM_of_right_enclosure` | **kernel-proved**（claim C1005）；**替换** R8 的左逆路线 |
| **`Fm` 的阻塞点（R9 量化发现）** | `Interval/Trig.lean` 的 sin/cos 是**低阶** Taylor（3 阶+5 阶余项 / 2 阶+4 阶余项），在证书角值上包络宽度达 `1.676e-4`（sin）/`2.272e-3`（cos），而 `hres` 需 `η < 9.956e-10` ⇒ **缺口 ≈ 1.68e5 倍**；根因是残差的**灾难性相消**（量级 0.38 的项相减得 ~1e-17）。`sqrt`/`π` 不是瓶颈；`Jt` 只需 ~1e-3 故当前内核够用 | **gap（方法极限，非反例）**，见 `DEAD.md §C′`；待办 = 高阶 Taylor 有理界（`n ≥ 9` 够本工程盒） |

⇒ **G1 的剩余义务只有两条**：
(1) **数值**：逐元素包络 `lo/hi` 与 `K`（行和）、`η` 的**精确有理界**（`K < 1` 且 `η + K·ρ < ρ`）；
(2) **可微性**：`TCSystem` 在盒上可微（残差含欧氏范数 `dist`；盒内各 `dist` 有正下界，由区间侧有理下界给出）。
`Q`、`η` 的数值与 `ρ` 已在 `evidence/root/` 与 `certificates/root-box.json` 备好。

**义务 (2) 的精确化（本轮读代码时发现，必须记）**：`TCSystem` 的乘子块 `adjointBlock` 用的是
`fderiv ℝ residualFun z`，所以 `TCSystem` 关于 `u` 的可微性需要 **`residualFun` 是 `C²`**
（一阶导数可微），而不只是一阶可微。因此义务 (2) 实际是：
* `residualFun` 一阶可微——需各 `rhoK` 的根号内量 `> 0`、各 `dist` 的被减量 `≠ 0`（盒内有理下界给）；
* `fderiv ℝ residualFun` 可微（即 `residualFun` 的 `C²` 性）——需 `sin/cos/sqrt/dist` 的二阶链式法则。
若不想付这条义务，替代路线是**把乘子块改成「由区间侧供给的 Jacobian 函数 `Jreq`」**
并证明 `Jreq = fderiv ℝ residualFun`（等价于把 (2) 换成一条等式义务）；两条路线都**不得关闭对象漂移**
（`sys` 仍是源系统）。已记入 `DEAD.md`/本表，未做。

**定义层对象（`TCSystem.lean`，全部 kernel-proved）**：`angleVec`（九槽角向量，`a4 = π−2Σ`）、
`thetaOf`（+`thetaOf_rec` 递推正确性 + `thetaOf_four`）、`sum_angleVec : Σa_k = π`、
`rhoK`/`ringCenter`(`C_k`)/`arcEnd`(`B_k`)/`Uvec`(`U_k`)/`hub0`/`hub1`/`wPoint`(`W`)、
`residual`（五个残差，源文顺序）、`centersOfRoot`(+`_ring`/`_nine`/`_ten`)、
`first7`/`last5`/`residualFun`/`adjointBlock`/`TCSystem`(+`_eR_at_eleven`/`_six_no_eR`/`_first`)、
`C892Attainment`、`tcRootSpec`、`n11_main_of_C892`。
`tcRootSpec` 用显式 `TCSystem` 实例化 `C891RootSpec` ⇒ **`sys` 不再是任意函数字段**，
stmt-audit 发现的 schema 漂移（F3）在定义层被消除。

**schema 警告**：`C891RootSpec` 的 `sys` 是任意函数字段 ⇒ 盒 + 索引**不**唯一确定 `Rstar` 的数值身份
（stmt-audit 已 kernel 反例：同盒同索引两实例 `Rstar` 相差 `2·radius ≈ 2e-9`）。
对 `R* < 19/50` 无害（盒上端已 `< 19/50`，余量 1.615e-5），但**任何更精细的数值身份主张都必须先钉住 `sys`**。

## 2. 几何桥（cap-arc 交付，**全部 kernel-proved**）

| 源义务（UNRESTRICTED-PROOF-ASSEMBLY §1） | Lean 声明 | level |
|---|---|---|
| `8 asin(R0) < π` | `arcsin_R0_lt_pi_div_eight` / `eight_mul_arcsin_R0_lt_pi` | **kernel-proved** |
| cap = 半平面截圆 | `mem_sphere_closedBall_iff` | **kernel-proved** |
| cap 含于角宽 `≤ arcsin r` 的弧 | `cap_subset_arc` | **kernel-proved** |
| **弧宽计数：`2π ≤ #ι · 2 arcsin r`** | `card_mul_two_arcsin_ge_two_pi` | **kernel-proved** |
| 推论：`r < R0 ⇒ 9 ≤ #ι`（圆周 / 闭盘两版） | `nine_le_card_of_covers_circle/disk_of_lt_R0` | **kernel-proved** |
| 8 盘不可能覆盖 `D` | `not_eight_ball_covers_disk_of_lt_R0` | **kernel-proved** |
| 内根替换（**需 `0 < c`**） | `dist_inner_root_le` / `_sqrt` / `inner_root_pos` | **kernel-proved**（注意隐含前提） |

### 2.1 装配接口（Lead）

| 义务 | Lean 声明 | level |
|---|---|---|
| 「触圆」对象化 | `MeetsCircle` / `BoundaryIdx` | kernel-proved（定义） |
| **`Covers c r ⇒ 至少 9 个盘触圆**（源文 "at least nine boundary disks"） | `nine_le_card_boundary` | **kernel-proved** |
| **触圆盘中心范数 `≥ 1-r`；`r<1/2` 时覆盖原点的盘不触圆** | `one_sub_le_norm_of_meetsCircle` / `not_meetsCircle_of_norm_le` | **kernel-proved** |
| **`Covers c r ⇒ 至多 10 个盘触圆** | `card_boundaryIdx_le_ten` | **kernel-proved** |
| **§1 边界盘计数夹逼：触圆盘数恰为 9 或 10** | `card_boundaryIdx_eq_nine_or_ten` | **kernel-proved** |
| `Covers` 口径下 8 盘不可能覆盖 `D` | `not_eight_covers` | **kernel-proved** |
| **内根替换保覆盖**（源文 §1 "coverage and actual arcs are preserved"） | `dist_innerRoot_le_of_dist_le` / `covers_of_innerRoot_replace` | **kernel-proved**（前提：`0<r<1`、被换盘在外根、被换盘触圆） |

装配只做对象翻译与调用；几何内容全部来自 §2。**结构收益**：C450 的残余义务被钉成**单一条**
——排除触圆盘数 = 10（等价地：证至少 2 个非触圆盘）。

### 2.2 可信区间算术内核（interval-core 交付，已集成）

| 义务 | Lean 声明 | level |
|---|---|---|
| `RatInterval` + **ℝ 侧**语义 | `toSet`/`Mem`/`mem_iff` | **kernel-proved** |
| `add/neg/sub/mul/inv/div` 的包含性与 `Valid` 保持 | `add_mem`/`mul_mem`/`inv_mem`/`div_mem`/… | **kernel-proved** |
| `Real.sqrt` 的精确有理外向端点（`Nat.sqrt`） | `sqrtLo`/`sqrtHi` + 包含性 | **kernel-proved** |
| 反射求值 + 声音性（含 `app1` 挂点与保守回退） | `IExpr.eval_sound` | **kernel-proved** |
| `exp/log/sin/cos/atan2` | 未覆盖 | **gap**（`evidence/interval/INTERVAL-GAPS.md`） |

## 3. 达到侧（C892）

| 源义务 | Lean 目标 | level |
|---|---|---|
| 「存在某个最优构型」 | `exists_covers_sInf` | **kernel-proved（无条件）** |
| **在 `Rstar` 处的覆盖构型**（`sInf ≤ Rstar`） | `n11_main_conditional` 的 `hattain` | **gap** |
| 边界弧铺满 + 完整 Voronoi 极值判据（非采样） | 未定义 | **gap** |

⇒ 达到性整体（"min 存在"）已由紧致性付清；C892 的残余**不是**消失了，而是缩小为
「源构型半径 = `sInf feasibleRadii`」这一条标量等式。

## 4. 下界侧（C923 + C921 + C922）

| 源义务 | Lean 目标 | level |
|---|---|---|
| 任意覆盖 → 嵌入两 hub 图 | 未定义 | **gap** |
| 拓扑分类穷尽（只剩 q0(6,7)） | 未定义 | **gap** |
| oracle 松弛 `V(U) ≤ r`（单向） | 未定义 | **gap** |
| 8 维闭单纯形全域下界（2386 能量叶 + 120 局部叶） | 未定义 | **gap** |
| **`Rstar < T`（同根阈值，只需 2 次 Krawczyk）** | **已被内核蕴含（接口级，2026-09-29 audit-s3 更正；原记"未定义"已过期）**：`Rstar_lt_R0_of_krawczyk`（sys=TCSystem → box=boxLoCert/boxHiCert → idx=6 → `Rstar < 19/50`）＋ `boxHiCert_six_lt_R0`（norm_num 内核件）；依赖 = C891 spec 本身（见 §2/audit C1387 项 4） | **proved（接口级）** |

## 5. 主定理组装

| 声明 | level |
|---|---|
| `n11_main_conditional` / `n11_sInf_conditional` | conditional-kernel |
| `n11_main_of_cert_box`（真实证书盒实例化，3 条显式前提） | conditional-kernel |
| **`N11MainStatement Rstar` 无条件内核证明** | **未达成（gap）** |

## 6. 接口级发现（必须记，勿再漂移）

| # | 发现 | 发现者 | 影响 |
|---|---|---|---|
| F1 | 源文 §1「内根替换」**隐含前提 `0 < c`**；缺则命题为**假**（精确有理反例 `u=(1,0), x=(-1/4,0), r=1/2, a=-1, b=-3/4, c=-7/8`）。**后续已加固**：cap-arc 在 `ArcRoots` 里把 `0<c` 从"需补前提"升级为**几何定理**（`c = cos θ ≥ √(1-r²) > 0`，由 `θ ≤ arcsin r < π/2` 推出），故对源文是加固而非削弱 | cap-arc | 源文陈述已补全；**不是** C924 的反例 |
| F2 | guide 建议的 `arcWidth` 次可加性**为假**（分离弧：并集最小包含弧宽 `π+1 > 2`） | cap-arc | 方法限制；已换测度次可加，结论未削弱 |
| F3 | `Rstar` 数值身份只被盒钉住到 `1e-9` 宽（`C891RootSpec` 是 schema） | stmt-audit | 更精细数值主张须先钉 `sys` |
| F4 | `N11MainStatement (sInf feasibleRadii)` 无条件为真且不含源常数 | stmt-audit | 禁止把 `sInf` 形式当源定理 |
| F5 | C891 单件 R 包络宽 `4.302140678393767e-15`；`max_K_shift≈4.372e-12` 由 index 4 支配 | root-audit + lead | 两个量不可混用 |
| F6 | C922 的 `~4.853e-31` 区间**有来源**（`contract_exact_root_threshold.py` 6 次收缩），GUIDE 的 `6e-31` 是其外向十进制取整 | root-audit | 撤回 lead 的"缺来源"初判 |
| F7 | `repaired_tc_krawczyk.json` 的 `source_hashes` 缺 6 个传递依赖 → 盒不可由记录哈希重导（可复现性缺口，数学无碍） | root-audit | 已在 provenance.json 补齐 |
| F8 | **包含判据检测不到 1e-16 量级的"函数搞错了"**：把 π 换成 binary64 使 F 偏 `4.7e-15`，Krawczyk 包含**照样通过** | root-audit | ⇒ 语义桥必须先于区间工作（TRUST §5.1） |
| F9 | **转写漂移（已修）**：源文 `e_R` 位于 **F 下标 11**（= z 下标 6 = `R`），不是 F 下标 6。首版 `TCSystem` 写成下标 6；现由 `TCSystem_eR_at_eleven`／`TCSystem_six_no_eR`／`TCSystem_first` 三条 kernel 定理钉死 z 指标 ↔ F 指标的对应 | lead（自查发现） | 说明这类漂移只能靠指标绑定的 kernel 定理排除 |

详见 `evidence/lead/PRINT-AXIOMS.txt`、`manifests/source-hashes.json`、`TRUST.md`、`DEAD.md`。


## 4. G1 接口链的当前映射（Lead，R36 更新 —— 此前本文件未覆盖近 20 轮的模块）

> 本节的每一条都**在根 import 图内**（传递可达），除注明外 `lake build` exit 0 / **0 warning**。
> 详表与"还差什么"见 `evidence/lead/FINAL-STATE.md`。

| 接口 | 承重件 | 提供 | 等级 |
|---|---|---|---|
| 源系统 | `TCSystem.lean` + `SourceIdentity.lean` | `residual`/`TCSystem` + 逐条具名绑定 | proved |
| 可微性 | `Smoothness.lean`/`SmoothnessC2.lean`/`TCSystemSmooth.lean`/`Transport.lean` | `ContDiffAt` 链 + 7 条非退化条件下的 `DifferentiableAt` | proved |
| Krawczyk/Banach | `Krawczyk.lean`/`KrawczykDeriv.lean`/`OpNorm.lean` | 唯一根的存在唯一性骨架 | proved |
| **矩阵包络** | `KrawczykMatrix.lean`（+ `dotR_eq_sum` 桥） | `I − Y·J` 的逐元素区间包络 + 行和界 ⇒ 收缩 | proved |
| **预条件子单射 `hY`** | **`PrecondRight.lean`** | **右侧收缩** `‖I − J·Y‖ < 1 ⇒ Y` 单射（源 `Y` 是 **binary64 近似逆**、无精确左逆 ⇒ 左逆路线作废，C1005） | proved |
| **残差界 `hres`** | **`Precond.lean`**（+ `dist_sub_eq_norm`、`incrMatVec`） | `hres` 的有理化；`‖Y(F c)‖ ≤ η` | proved |
| **`Fm`（值侧）** | **`ResidualInterval.lean`** + `ResidualIntervalReadout.lean` + **`ResidualIntervalReadoutLag.lean`** | `residualInterval` + **无条件包含性**；阶乘版读数宽度 **1.06e-19 < 9.956e-10**（余量 9.4e9 倍） | proved |
| **`Fm` 的 `Fin 12` 拼装** | **`FmAssembly.lean`** | `mem_fmCert_cert`：**`Fin 5` vs `Fin 12` 形状缺口闭合**；前提收缩到 **`hD` 一条**（`λ` 不是前提、`∂f/∂λ = 0` 不是假设） | proved |
| **三角端点** | `IntervalsHigh.lean`（MVT 路线，纯幂）+ **`IntervalsHighLag.lean`**（**积分/Lagrange 阶乘余项**：`sinLoNLag`/`sinHiNLag`/`cosLoNLag`/`cosHiNLag` + 包含性 + `sinIHighLag`/`cosIHighLag` + **窗口算子可靠性**）+ `Interval/Taylor19{C}.lean` | 窗口 `[-1,1]` 上宽度上界 **`2/29!`** | proved |
| 一元区间 AD | **`IntervalAD.lean`** | `AD`/`ADRule`（**删掉双参 `df` 只留 `dfv`** ⇒ 组合问题从根上消失）；`const/id/add/neg/sub/mul/sq/sin/cos`；`pow`/`sqrt` 留 `*GapStatement` | proved（一元 scope） |
| 盒↔球接口 | `Assembly/TCKrawczyk.lean`/`Assembly/G1Final.lean` + **`BoxRstar.lean`** | 球口径 ⇒ `C891RootSpec`；`Rstar` 盒锁定、`Rstar < 19/50`、`0 < Rstar` | proved |
| 根证书 | `Certificates/RootBox.lean` → `Conditional/{RootSpec,CertBox}.lean` | 纯 ℤ 检查 + `check_sound` + `root_box` 内核核查（生成器→已证 checker） | proved |
| **G2 几何** | `Geometry/*` + `Assembly/BoundaryCount.lean` + **`Assembly/ArcCover.lean`** | 边界盘计数夹逼、**整个 S¹ 覆盖**、精确紧性、**零余量方向条件式闭合** | 混合（含 1 条 `gap`） |
| **`D : Fin 5 → Fin 7 → RatInterval`** | **`ResidualDeriv.lean`** | **线性脊柱 ✅**（9×7 整数 `fderiv` 矩阵 + `dTheta_eq_dThetaSum` + 具名结构零）；**非线性 5 节点 ❌** | **gap** |
| **`Jt`（12×12）** | 同上 | 与 `D` 同源 | **gap** |

**⇒ G1 的前提清单现在只剩 `D`/`Jt`**（七个 `hnd*` 属数值/方法件、`hD`/`hsum`/`hres` 待 `D`/`Jt`）。

### 4.1 独立对照件（**不属于** `D` 的来源，见 C1060）

| 件 | 用途 | 等级 |
|---|---|---|
| `evidence/interval-ad/dz_iv_enclosure.json` | 35 格 `∂f_k/∂z_i` 的**严格**区间包络（MPFI 向外舍入；**不得经 `mp.mpf` 中转**）+ 可采纳端点；作**对照件/宽度参照** | numeric |
| `evidence/interval-ad/dz_cross_read.*` | 四腿互校（sympy 符号 / mpmath 自适应 / 加密差分 / 旧对照表）⇒ 抓出旧表 **8/35 格错**（`k=2` 列 0.4517） | numeric |
| `evidence/interval-ad/d_review_intersect.py` | **复核仪器**（已自校准）：相交性（**无容差**）+ **来源红旗**（端点恰等于外部表 ⇒ 红旗） | 工具行为 proved-exact |
| `evidence/box-rstar/fm_cert_values.out.txt` | **旧**目标值表 —— **仅 24 格可用**（`k=2` 列等 8 格已证错） | numeric |

## 7. 接口级补充（Lead，R79 —— 补 C922 的独立条目 + 两个**决策性仪器**，此前本文件零覆盖）

**为什么补**：`g3-recon` 在 G3 侦察里指出 **C922（`R* < T`）是 G3 的隐藏承重件**，而本文件此前**只在 §4 标题里提名过它、没有条目** —— 这正是"承重项在映射里看不见"的典型缺陷。同轮又产生两个**改变判断**的读数（K 预算、范围核对），本文件此前**零命中**，一并补入。

### 7.1 C922（`R* < T`）—— G3 的**隐藏承重件**（源 §4 未列）

| 项 | 内容 |
|---|---|
| 命题 | `R* < T`（`T = 1899919265599193545242591/5e24`，即 G3 侧的能量阈值） |
| 为何**承重** | G3 的下界论证要在 **9 个单形顶点**上给出 `V(e_r) > T`，而顶点检查只给出 `> T`；**把它接到 `R*` 需要 `R* < T`** ⇒ 它是**从"顶点下界"到"覆盖半径下界"的必需环** |
| 为何**隐藏** | 源文把它与**超越函数表**绑在一起（Python 侧），形式化时须把该表搬进 Lean ⇒ 作者判为 **G3 的隐藏承重件**、估计 **15–40 人-轮**、风险性质 = **数学 + 表示** |
| 现状 | **未形式化**；源文档**自述**无缺口（**源作者自评，非认证** ✓） |
| 关联 | `STATUS` 的 C922 条目 + `evidence/g3-recon/G3-PLAN.md §3` |

### 7.2 决策性仪器一：**Krawczyk 真实宽度/精度预算**（已登记 **C1131**，件 `evidence/jth-assembly/K-BUDGET.md`）

- **结论**：`Hess` 块宽度预算 **`w* ≈ 0.3834`**、叶子精度预算 **`eps* ≈ 3.39e-6`** ⇒ **比"必须 ≪`1e-16`"宽 12 / 10 个数量级** ✗ —— **本文件与 `STATUS` 中一切"必须 `1e-16`"的表述据此作废**。
- **但**：`d-nodes` 的**换叶子仍必要**（换前 `D` max **`4.787 > 0.383`** ✗，换后 `6.670698e-17` 余量约 5000 倍 ✓）⇒ **"做对了、理由是错的"**；`D` 已完成的事实不变（已付成本）。
- **双校准逐位 PASS**（对内核 `decide` 已验端点 + 对 `contraction_Q_inf_upper_exact`）⇒ **仪器可用**；`TRUST.md §7` 立项后**第一个"事前"做到位的读数** ✓。

### 7.3 决策性仪器二：**「包络/界」型前提的量词范围核对表**（已登记 **C1132**，件 `evidence/hnd-lean/SCOPE-AUDIT.md`）

- **(C1)** G1 链上「范围不一致」**只有一处** = `Jt` 的逐元素包络（`hJ`/`henc`，= §6 的 **F1**）⇒ **修 F1 一处即把该族风险清零** ✓（**有价值的否定结果**）。
- **(C2) 静默类 (S) 危险点 4 处**：① `hJ`/`henc`（球 vs 心，**类型相同** ⇒ 不报错）；② **`hsum` vs `hsumR`**（`Y·J` 与 `J·Y` 是两个不同矩阵、两个同名 `K`）—— **Lead R78 现场复核：当前槽位正确**（`BoxRstar.lean:429` 用 `hsumR` 于 `I−J·Y`、`:447` 用 `hsum` 于 `I−Y·J`，源码自文档化 ✓）**但潜在类真实存在** ✗；③ `hηb`/`hres`/`hK`（两条 `K` 口径，`η` 容差差 `≈4.4e-13` = 相对 `4.4e-4`）。
- **已固化为常设程序**：`TRUST.md §7.1`（四步判据 + **两条操作规则**：写槽位前先抄消费者量词；**每次供给升级必须复跑并复核量词**）。

---

# §8 承重接口映射更新（R166–R183）—— 新增/变更的承重件与它们的"供-需-审"状态

**口径** ✓：每条列 **供（提供什么）** / **需（谁消费）** / **审（判据一状态）** / **位（是否在根 cone 内）**。
**"在根 cone 内"= 从根 `N11Formalization.lean` 传递可达 ⇒ 才有审计覆盖** ✓；**未进根者即便已绿也不加覆盖** ✗。

## 8.1 本段新增且**已在根 cone 内**（审计覆盖已生效 ✓✓）

| 承重件 | 供 | 需 | 审 | 位 |
|---|---|---|---|---|
| **`hasFDerivAt_fderiv_add` / `_sub`（T1）** | 二阶加减法则（`HasFDerivAt (fun z => fderiv ℝ (φ ± ψ) z) (φ2 ± ψ2) u0`，**保留 T2 的两条 `∀ᶠ DifferentiableAt`、未弱化** ✓） | H2 的 `ρ''` 装配（`ρ = cos∘a_k − √∘W_k` 的减法支 ✓） | **proved**（`ResidualDerivJTHess.lean` §6，指纹 **`CF73D2B362422415`** ✓） | **是** ✓（该件已接根） |
| **`hasDerivAt_deriv_sqrt`（`√` 的 1D 二阶基元）** | `HasDerivAt (fun t => deriv √ t) (-(2·(1/(2√x)))/(2√x)²) x`（**原始形态、不归一化** ✓） | T2 在 `u := Real.sqrt` 时的 `hu2` 前提 ✓ | **proved**（同上件 ✓） | **是** ✓ |
| **`sqrtLo_pos`（严格下界原语）** | `0 < q ⇒ 0 < sqrtLo q`（**不用任何非严格引理凑** ✓；附边界对照 `sqrtLo 0 = 0` ✓） | F1 球级那批 `sqrt` 侧严格正性 ✓ | **proved**（`Interval/Sqrt.lean`，指纹 **`D856D537759005A3`** ✓；公理画像标准三元组 ✓） | **是** ✓ |
| **`inWindow_abs_mul_halfPiLo_le`** | `inWindow A k ⇒ |(k:ℚ)| * halfPiLo ≤ |A.lo| + |A.hi| + 2`（**乘性形式** ✓） | 相位候选 `k` 的**有限性** ✓ | **proved**（`Interval/Range.lean`，指纹 **`8D875E4F6D7EC366`** ✓；配 `inWindow_width_le_two` ✓） | **是** ✓ |
| **`IntervalZ`（5 条：`int_cast_toNat`/`int_cast_negToNat`/`sin_cos_shift_halfPi_four`/`sin_shift_halfPi_mem`/`cos_shift_halfPi_mem`）** | `k : ℤ` 平移的四态表封装（**解除 `interval-core` 报的 cast 归一化障碍** ✓） | `Interval/Phase` 一族 ✓ | **画像两独立测量一致 = 5/5 标准三元组** ✓✓（**归属如实记"来源不明"** ✓；来源不明与画像干净**可同时成立** ✓） | **是** ✓（根 `L32` 直接 import ✓） |

## 8.2 本段新增但**尚未进根 cone**（已绿、零审计覆盖 ✗）

| 承重件 | 供 | 需 | 审 | 位 |
|---|---|---|---|---|
| **`hasFDerivAt_fderiv_mul_scalar`（T3 二阶乘积法则）** | `HasFDerivAt (fun z => fderiv ℝ (fun y => φ y * ψ y) z) (φ u0 • ψ2 + φ1.smulRight ψ1 + ψ u0 • φ2 + ψ1.smulRight φ1) u0`（**Lead R156 核过型别与数学** ✓） | `RingC = ρ·trig` 的四项装配 ✓ | **实跑绿**（`evidence/jt-build/Leaf2Dev.lean` = **`7E116C0F381EB45E`**，**Lead 独立复跑 exit 0/0/0** ✓） | **否** ✗（待搬进 `srcDir`） |
| **`hasFDerivAt_fderiv_Wfun`（(a)）** | = T2 的 `g2`（`A' − B'`，**Lead R154 逐项核过符号** ✓） | T2 特化 ✓ | 同上 ✓ | **否** ✗ |
| **`hasFDerivAt_deriv_sqrt`（(b)）** | = T2 的 `hu2` 前提 ✓ | T2 特化 ✓ | 同上 ✓ | **否** ✗ |
| **`F1-BallWk.lean` 四定理**（`ndWk_pos`/`ndWkBox_mem`/`ndSqrtWk_pos`/`ndWk_ball`） | 盒版严格正性 + **球上 `Mem`** + `sqrt` 侧严格正性 + 参数化打包（**不铺格** ✓） | F1 第 2 步（`compIv` 盒版）✓ | **实跑绿**（`52251896BF5CBAED`，**四定理画像全标准三元组** ✓） | **否** ✗ |

## 8.3 交付 (2) 的切片（**它的承重已全审** ✓✓）

| 承重件 | 内容 | 审 | 位 |
|---|---|---|---|
| **`Rstar_lt_R0_via_cert`**（`Conditional/RootSpec.lean:79` ✓） | **端到端切片本体**：证书数据 → checker 通过 → `Rstar` 落入证书包络 ⇒ **`Rstar S < 19/50`** ✓ | 画像 `[propext, Classical.choice, Quot.sound]` ✓ | **是** ✓ |
| `RootBoxCert.check_sound_lt_R0` / `check_sound` | 已证 checker ✓ | 同上 ✓ | **是** ✓ |
| **`rootBoxCert_check := by decide`** | **内核核查具体证书** ✓ | 画像 **`[propext]`** ✓✓（**比标准三元组更小** ✓） | **是** ✓ |
| `rootBoxCert`（数据） | 证书常量 ✓ | `[propext]` ✓ | **是** ✓ |
| `n11_main_conditional` | 条件主定理，**两侧同一 `Rstar`** ✓ | 标准三元组 ✓ | **是** ✓ |
**⇒ 唯一未实例化的是几何前提 `hlo`/`hhi`** ✗（C891 的 Krawczyk 包含义务 ✓）。

## 8.4 本段新立的两条**工程口径**（与承重映射直接相关）

1. **`lake build` 静默报绿 + 模块 olean 被外部删除** ✗✓：见 `object file … does not exist`（**即使根刚绿**）⇒ **先 `lake build <那个模块>`，别去改代码** ✓✓（修法实测：`lake build N11Formalization.Interval.Range` ⇒ exit 0 ✓）；
2. **形状类残差用形状工具**（`rfl`/`Pi.add_apply`/`one_div`/`ac_rfl`/`ext`/`show`/**同形书写**）✓；**不用大 `simp`、绝不用"改命题"让门变绿** ✗✓（**改书写形态允许 ✓；改结论强度不允许** ✗）。

**边界（不变）** ✓：**判据一满足且全闭** ✓✓；**判据二未满足** ✗；根 **exit 0 / 0 error / 0 warning / jobs 8782**（两次连续串行 ✓✓）；盒心列 **95/144 独立** ✓；球级列 **25/144 有付 / 119 未付** ✓；`hsum` 35 格仍 numeric ✗；**未放宽端点** ✓。

---

# §9 承重接口映射更新（**R186–R256 末**，Lead）—— 覆盖本会话新增的 17 片件与两条依赖图事实
**基线（Lead 于本段开头两次连续串行实测）**：`lean/N11Formalization.lean = **`DB887FE5E0D327E3`  / 75 imports / exit=0 / 0 error / 0 warning / jobs=8799`** ✓✓
**⇒ 本文件此前止于 §8（R166–R183），对本会话新增件**零覆盖**** ✗ —— §9 补上。

## 9.1 连接线 ③（F1：球级 hJ）—— 供-需-审 链（**每一环都已在根 cone 内** ✓✓）
```
件（根内哈希前缀 / 画像条数）        供应什么                                      消费什么
F1.BallD35Hrad  E489F3CB0713B6D8/19  球级 35 格区间层（compIvBox_mem_all，**无条件**）+ 4 个球盒 Mem + 无条件化 radIvBox_pos
F1.BallD35C1    03612F77381259BF/6   角层**点无关**（fderiv_angleVec/thetaOf_any_single）       ← Hrad
F1.BallD35C2    D55D39E29AB82F2A/7   ringCenter 层（真缺口）+ arc 层接合两条                    ← C1/Hrad/ResidualDerivJT
F1.BallD35C4    FF7E3AA53A83F063/4   Uvec 层（残差节点直接输入）+ arcC0/1_any                  ← C2/ResidualDerivJT
F1.BallD35C5    E9D9C54D36DD9F08/6   最后四层：hub0/1、WpAt、wPoint 两坐标、dist 链、fderiv_residualComp_any  ← C4/JT/Dist
F1.BallD35C6    C27CC1D5F15CFABB/5   残差五分量**任意点显式 fderiv 读数**（fderiv_residual_{0..4}_CLM）  ← C5/C4/C2/Hrad/JT/D
F1.BallD35C7    4BFC2F105EA9EABB/7   五条桥 + fderiv_residual_k_any + **收口 ndJT_res_z_box（条件式）**  ← C5/C2/Hrad/JT
F1.BallD35C8    D971BC28788CEE15/7   **收口无条件化 ndJT_res_z_box_uncond**（前提只剩球成员 hz）★      ← C5/JT/D/NondegProof(C891侧)
⇒ **链的终点**：`(compIvBox k i).Mem ((fderiv ℝ residualFun z (Pi.single i 1)) k)` —— **区间层与真 fderiv 已**无条件**连通** ✓✓✓✓
⇒ **仍缺**：与 `compIvBox_mem_all` 并成**一条 ∀ k i 合取**、并接 `hJ` 在 F1 判据里的**消费点**（f1-step2 本轮执行）✗
```
## 9.2 G3（全局下界主体）—— 片与其中的承重分工
```
件                            画像  供应什么
G3.SliceL0   73E7CE4D1DCF68B5   19   叶义务骨架 + 精确有理叶数据 + 阈值（T*T=T2 / leaf 3、4348 的 stored 界）
G3.SliceL1   8E1E6DD47395AB18   10   cos 的 Taylor 窗口扩到 Icc 0 (39/25)（**后经 §9.4 降级为过程件**）
G3.SliceL2   E8DB60AEA89A924C   12   π-平移恒等式 + 偶奇搬移 + **可判定有理平移判据 fitsWindow(+sound)**
G3.SliceL3   4D32FCA3B9893C39    6   叶义务的**精确归约**（两端 ∧ 临界条件）+ 临界条件代数化（cos 消去）
G3.SliceL4   (根内)              6   arcsin 夹逼框架（arcsin_bracket 等）
G3.SliceL5   53D62087DA761F5B   19(名) 记录数据上**第一条完整 per-line minorant**（minorant4348）+ 一般引理（假设过强、sound）
G3.SliceL6   0BE6E7E7ABB6039   5/**8** **两条方向正确的一般端点引理**（cos≤0⇒凸；φ'常号）⇒ 覆盖 78139/124130 = **62.9%**
Interval.ArcsinBracket  E8238398AE807939  4  **G3/G5 共享的缺失内核**（见 9.3 事实①）；**宽度恰 1e-12**（见 DEAD）
LeafAgg      4A051E47745147B7   4   **叶级聚合的无字面量 checker + 两条 soundness**（leafCheck_sound(_unscaled)）
```
## 9.3 **依赖图级事实（本会话新增，且现已在根 cone 内显式化）** ✓✓
```
事实① **G3 与 G5 共享同一缺失内核**（"由核 sin/cos 界产生有理括号"） —— 此前仅记在台账；
      **现由独立受审模块 `Interval/ArcsinBracket`（画像全标准三元组、只 import Mathlib+根核、**无 G3 依赖**）承载** ✓✓
      ⇒ **接续者改动它时，G3 的叶聚合与 G5 的 acos/atan 两侧同时受影响**（承重面扩大 ⇒ 改动须双验）✓
事实② **F1 的 hJ 链已无条件连通**（9.1 的终点）⇒ 消费点一旦接上，**球级列的"落格"路径就完整**（但**计数仍需消费接口明说**）✓
```
## 9.4 本会话新增但**未进根 cone**（**不计已付** ✗）
```
G3.SliceL7（1b5a6e96…，范例 + 成本探针，故意不接根）｜ G3.SliceL8（ee263b42…，checkA + checkA_sound，**缺 *_rejected 伴生件**）
LeafAggPartial（22c5a999…，玩具级 (a) 设计 + 对抗证明 ms3LIE_rejected）｜ BlockCert（(4) 骨架 runSum_concat 画像 [propext]）
PartialBig（真实叶 791 心跳墙 ✗）｜ LeafShard0..3（8.3 MB，**已生成但未过门** ✗）
F1-BallD35-C3（在途带 1 错 ✗）｜ F1-BallD35-A（15 画像，被 Hrad 取代）
```
## 9.5 边界（口径，任一接续者必读）✗✓
```
**受审 ≠ 落格**：**球级列 25/144 有付 / 119 未付** ✗（C6/C7/C8 使"区间层↔真导数"连通，**不自动改计数**）｜盒心列 95/144 独立 ✓
**checker + 证书 ≠ 叶级已付**：三条缺口随件件头记录 ①`leafCheck_sound_unscaled` 假设未逐叶落地 ②真实叶未验 ③叶恒等式仍以记录 `energy_lower` 为输入 ✗
**`hsum` 35 格宽度仍 numeric、kernel 内不可消费** ✗ ｜ **端点从未放宽** ✓（全程）
**每个 checker 必带 `*_rejected` 伴生定理**（新通用要求 ✓；范例：`chainOK_sound`+`ms3LIE_rejected`、`runSum_append`+`blkLIE_rejected` ⇒ 后者画像 **[propext]** ✓）
```
## 9.6 §9 新立的两条工程口径（与承重映射直接相关）✓✓
```
① **"宽度是消费者的属性"**：括号/区间宽度由**消费方的放大因子**定，不由被逼近量的精度定（实证：4e-4 宽版对叶级消费者不足 ⇒ 1e-12 版）；
   ⇒ **共享件（如 ArcsinBracket）的"够不够"，必须按**每一类消费者**分别验** ✓✓
② **"用定义代替证明"（三级）**：**切规模 → 消除规模 → 使之为定义**（`rfl` 级 ⇒ 零 elaboration）；
   与 (I) 路线的判据配对 ⇒ **凡装配步，先问"能否定义化"，再问"能否切小"** ✓✓
```

## 9.3bis **事实③（Lead，新目标 R3 —— 由 f1-step2 的测量式普查给出，Lead 实测复核）** ✗✓✓
```
结论: **`Hess` 的义务与 `hsum`/`hlo`/`hhi` **不是同一未付块**；缺口**叠加**，不是一处共享义务** ✗✓
依据（对象/量词/位置，均实测）:
  链 = **Hess → Jt → krawczykMat → hsum/hlo/hhi**
  Hess: 对象 = residualFun 的**二阶偏导**（hessEntry i j mm = ((fderiv (fun z => fderiv residualFun z) u0) (Pi.single j 1)) (Pi.single i 1) mm）
        量词 = **7×7×5 格、仅盒心 u0**；位置 = **Jt 的**上游原料**（Jt 定义里 Hess 是显式参数）**
  hsum/hlo/hhi: 对象 = krawczykMat Y Jt / incrMatVec Y Fm 的**矩阵/向量区间包含**；
        量词 = **12×12 / 12、球上或全**；位置 = **Jt 的**下游消费者**（hJ: Jt 的 Mem → hsum → hres）**
⇒ **唯一共享的是"有理区间 Mem"这一**字符**（口径同族 ✓），不是同一个未付块** ✗
⇒ **纠正**乐观口径****: **线 ③ 不是"接消费点即可"**，而是**多出三项**:
   (a) 残差×λ 球级 ｜ **(b) KKT×z ⇒ 需 Hess 球级包络 ← 主项** ｜ (c) KKT×λ 球级
```
**Hess 义务的**工具组覆盖**（`ResidualDerivJTHess.lean`，**已受审、在根内** ✓✓）**：
`secondPartial` 三件（★**装配层↔叶子层的唯一接口**）＋ `secondPartial_const/coord` ＋
`hessEntry_eq_fderiv_gFun` / `hH_of_gfun` / `HessOfGfun` / `mem_Jt_at_center_of_gfun` ＋
二阶 β 运算组（`add`/`sub`/`comp_scalar`/`mul_scalar`/`sqrt_comp`、`hasDerivAt_sqrt'`/`hasDerivAt_deriv_sqrt`）✓
**⇒ 尚缺 4 条（附"新数学/装配"判断）** ✗：
**(1)** `gFun` 的 `HasFDerivAt` CLM 一般点版 ⇒ **装配**；
**(2)** 二阶展开的具体化（α 层一阶 + √/商二阶 β）⇒ **装配 + 少量新数学**；
**(3)** **球级二阶包络 ⇒ 份量最大（新数学）**；
**(4)** **二阶求值口径（表示选择）** —— **Lead 已裁：目标 = 球级一致包络（`∀ x ∈ ball` 的 `Mem` 形状）；
且先量 (i) 二阶格是否非空泛、(ii) 是否需**三阶层**** ✓✓


---

## ⚠ **头条计数更正（Lead 自查，R261）**：球级列不是 25/144，而是 **60/144**

**原写法（错/过期）** ✗：**"球级列 25/144 有付 / 119 未付"** —— 我在 4 本台账与几乎每份报告里重复过它。
**更正后（根内实测）** ✓✓：
```
球级 `Jt` 格 = `∀ x ∈ closedBall certCR rhoCertR`（或 `pad12 z ∈ ball`）下的 `(Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k)`，**共 12×12 = 144 格**
**已证** ✓：`mem_Jt_res_z_ball`（C9 L90；(k : Fin 5)(j : Fin 7) ⇒ 残差行 × z 列 = **35 格**）＋ `JT_lam_res_ball`（C10 L82；(k m : Fin 5) ⇒ 残差行 × λ 列 = **25 格**）＝ **60 格**
**未付** ✗：`Jt` 的 **KKT 行**（r ≥ 5）= 7 行 × 12 列 = **84 格** = **KKT×z 49 格（需 `Hess`）** ＋ **KKT×λ 35 格（= (c)）**
⇒ **⇒ 更正：60/144 有付 / 84 未付**；**且 84 = 49 + 35 恰好等于两条流手上的两半** ✓✓（**一致性核对** ✓）
```
**错因（记我头上）** ✗：**"25" 是 λ 列那一半的数**（C10），我把它当成了球级总计数 —— **即把"某一子块"的数当"全列"的数** ✓
**⇒ 口径**：**计数类头条数字必须**每次引用时重算**（或至少标明它是哪个子块的数）** ✓✓ —— 与"被引用的状态串必须是与当下绑定的读数"同族（**这是它在我身上第 N 次生效** ✗✓）
**⇒ 影响范围**：`STATUS` ／ `TRUST §7.3bis/§4bis` ／ `SOURCE-MAP §9.5` ／ `HANDOFF §10` 中的该数字**均以本更正为准** ✓

---

## ⚠⚠ **头条计数的第二次更正（Lead 自查，R261b）—— 上一次更正本身过宽** ✗✓

**第一次更正（R261）** 我写成 "**球级列 60/144 有付**" —— **仍不准确** ✗：
```
`hJ`（`BoxRstar` L375）的量词是 **∀ x ∈ closedBall certCR rhoCertR** ⇒ **一般 12 维点（λ 可 ≠ 0）** ✓
而 C9/C10 的两条已证件都是 **`pad12 z` 形状**（我只核了签名 ✓）：
  `mem_Jt_res_z_ball (k : Fin 5) (j : Fin 7) (z : Fin 7 → ℝ)`（C9 L90）—— **λ=0 切片**上的残差行 × z 列 = 35 格
  `JT_lam_res_ball (z : Fin 7 → ℝ)`（C10 L82）—— **λ=0 切片**上的残差行 × λ 列 = 25 格
⇒ **它们只覆盖 λ=0 那一层切片** ✗ —— 而 `x ∈ ball` **不蕴含** `pad12 (first7 x) ∈ ball` ✗（压 λ 到 0 会移动点 ⇒ 范数变）
**⇒ 正确写法（双计数，按消费方参数化）** ✓✓：
  · **λ=0 切片（`pad12 z ∈ ball`）**：**60/144 已证** ✓（C9+C10）
  · **一般 `x ∈ ball`（= `hJ` 的消费方形状）**：**待判** ✗ —— 由 `f1-step2` 判 **(甲) 够 / (乙) 需一般化重述**（已派，附 λ-无关线索）
```
**错因（记我头上，第 2 次同一族）** ✗：**我第一次更正时只改了数、没核**参数化是否覆盖消费方的自由度**** ——
**而这正是 `f1-step2` 刚教我的那条口径**（"参数化必须对着消费方检查" ✓✓）⇒ **我把它写进口径却没先用在计数上** ✗✓
**⇒ 口径强化**：**凡"计数/覆盖"类断言，必须先写清**消费方的参数化**，再数 —— 否则数本身无意义** ✓✓
**⇒ 影响**：`STATUS` / `TRUST` / `SOURCE-MAP` / `HANDOFF` 中一切"球级 X/144"字样**以本双计数为准** ✓；
**并撤回 R261 的单值 "60/144" 表述**（**不是撤回更正本身** —— 更正"25 是子块数"那部分仍成立 ✓）

---

## ⚠⚠⚠ **头条计数的第三次更正（Lead，R262）—— 这次是向下的、也是唯一诚实的方向**：消费方形状 = **0 / 144**

**事实（`f1-step2` 判决 + **Lead 独立核过源文**）** ✓✓✗
```
**球的 λ=0 切片在球内是**空集**** ✗✗：`BoxRstar.lean` L91–103 `def certC` 的 λ 分量（coord 7..11）=
  `-2050658785296173/2^54`、`-7385064427961529/2^58`、`-7661580961047613/2^60`、`-2860603688525993/2^57`、`-7612361213708557/2^58`
   ⇒ ≈ **−0.11383, −0.02562, −0.00665, −0.01985, −0.02641** ⇒ **max|λ_cert| ≈ 0.1138** vs **ρ = rhoCertR = 1e-9** ⇒ **差 ~8 个数量级** ✓
⇒ 球内任何点都有 `|λ_i − λ_cert,i| ≤ ρ`（某 i）⇒ **λ 全为 0 的点不存在** ⇒ **`pad12 z ∈ ball` **零实例**** ✓✓
```
**⇒ 正确的消费方形状计数** ✗：
```
**`∀ x ∈ closedBall certCR rhoCertR`（= `hJ` 的消费方形状）下：0 / 144 有付 ／ 144 未付** ✗
（**不是 25**（那是 λ 列子块）✗；**不是 60**（那是 λ=0 薄片上的格数，而该薄片在球内为空 ✗））
```
**⇒ 对 C9/C10 的准确刻画** ✗✓：**它们**不是假****，而是**对消费方**空泛（vacuously true）**** ——
`pad12 z ∈ ball` **不可满足** ⇒ 两条定理的真假无碍，但**对 `hJ` 的贡献 = 0** ✗（**"真空真" ≠ "已付"** ✓）
**⇒ 三次更正的教训（Lead 自记）** ✗：**25**（子块的数当全列）→ **60**（空切片上的数当全列）→ **0**（正确）——
**两次都把"某一参数化层上的数"当成了消费方的数** ✗ ⇒ **强化口径（第 3 版）**：
> **计数类断言必须**三件齐备**：①消费方参数化 ②**该参数化在定义域内是否可满足**（空域 ⇒ 计数为 0）③计数** ✓✓
**⇒ 修法（便宜、近逐字）** ✓✓：所有区间 `Mem` 供给件本吃**任意** 12 维 `x ∈ ball`（`ndBox_mem hx`／`wkBox_mem hx`／`WpIvBox_mem hx`／`radIvBox_mem k hx` ✓），
**C8 的三条非退化供给本就是一般 `x` 陈述** ✓ ⇒ 只需 `pad12 z ∈ ball` → **`x ∈ ball`**、`z` → **`first7 x`** ⇒ **60 格一次搬到消费方形状**（计数 0 → 60 ✓）
⇒ **三段账**：**重述 60** ＋ **(c) 35** ＋ **`Hess` 49** = **144** ✓✓（已批准 `f1-step2` 先做重述——它是计数上单笔最大增益 ✓）
**⇒ 并记一条**几何事实**（`f1-step2` 给的，我已采信）** ✓：**"球在 z 方向的投影 ⊂ `ndBox` 的前 7 维"是真的**（`ndBox_mem` 对任意 `x ∈ ball` 成立 ✓）⇒
**包络从不是卡点** —— **(甲) 所需的几何引理是**假的**** ✗（**这才是 (甲)/(乙) 判决的实质** ✓）

---

## §G.9 口径（Lead，R264 —— 由 `g3-recon` 的三件实测得出，**与 §G 早先"大 def 不入语句"合并**）
```
**"凡由 elaborator 逐项处理的**体量**（大 `def` ／ 大**字面量**）都不得出现在**语句**里；放进 `def` 名，语句只提名字"** ✓✓
**实测依据**（`g3-recon`，三件，含单因子对照）：
  · 语句含 `= (<60 位大整数>)` ⇒ **~4 s/条定理** ✗
  · 语句只含 `def` 名（`bs_i`/`ss_i`）⇒ **0.055 s/条** ✓（**差 ~70×**）
  · **对照 ①**：空定理 100 条 = 22.5 s（基线 ≈17 s）⇒ **定理条数不是驱动** ✗✓
  · **对照 ②**：同 20 叶，"1 条定理 25.7 s" vs "2 条定理 23.1 s" ⇒ **无差** ✓✓
  · **对照 ③**：该件**未用** `@[irreducible]` ⇒ **密封不是驱动** ✗✓
⇒ **⇒ 直接 refute 了"每叶定理条数 ~4 s"这一先前假设** ✗✓（**并解释了 (f) 形状为何失败**：它把大整数放进了**语句** ✗）
```
