import N11Formalization

open N11Formalization

-- ============================================================================
-- n11-formalization 人读审计打印件（GUIDE §6：打印最终完整类型，确认对象未漂移）
-- ============================================================================

-- ===== 一、主定理类型与覆盖对象（GUIDE §2 的数学接口） =====
#print Point
#print unitDisk
#print Covers
#print feasibleRadii
#print StrongInterface
#print N11MainStatement
#print Rstar

-- ===== 二、源构型的显式构造（TCSystem.lean —— 防止对象漂移的核心） =====
#print angleVec
#print thetaOf
#print rhoK
#print ringCenter
#print arcEnd
#print Uvec
#print hub0
#print hub1
#print wPoint
#print residual
#print centersOfRoot
#print first7
#print last5
#print residualFun
#print adjointBlock
#print TCSystem
#print C892Attainment
#print tcRootSpec

-- ===== 三、装配接口对象 =====
#print MeetsCircle
#print BoundaryIdx

-- ===== 四、可信基础：所有承重条目的 #print axioms =====

-- 抽象层（无条件）
#print axioms isLeast_iff_strongInterface
#print axioms sInf_feasibleRadii_eq
#print axioms feasibleRadii_nonempty
#print axioms feasibleRadii_bddBelow
#print axioms no_cover_below
#print axioms n11_main_of_strongInterface
#print axioms n11_attainment
#print axioms n11_optimality
#print axioms n11_no_smaller

-- 达到性（无条件）
#print axioms Covers.localize
#print axioms exists_minimizing_sequence
#print axioms exists_covers_sInf
#print axioms sInf_mem_feasibleRadii
#print axioms strongInterface_sInf
#print axioms feasibleRadii_eq_Ici
#print axioms feasibleRadii_closed

-- 锐化与反漂移
#print axioms strongInterface_iff_eq_sInf
#print axioms n11MainStatement_iff_eq_sInf
#print axioms n11MainStatement_iff_two_bounds
#print axioms n11MainStatement_at_sInf_is_free

-- 证书切片
#print axioms hexNatVal_lt_pow
#print axioms hexDigitVal_lt
#print axioms RootBoxCert.check_sound
#print axioms RootBoxCert.check_sound_lt_R0
#print axioms rootBoxCert_check
#print axioms rootBoxCert_encHi_lt_R0
#print axioms decRadiusHex_toQ
#print axioms decCenterHex_six_toQ
#print axioms src_parse_binding
#print axioms rootBoxCert_box_containment

-- 源构型定义层的性质
#print axioms thetaOf_four
#print axioms thetaOf_rec
#print axioms sum_angleVec
#print axioms centersOfRoot_ring
#print axioms centersOfRoot_nine
#print axioms centersOfRoot_ten

-- 几何桥（cap-arc 交付）
#print axioms arcsin_R0_lt_pi_div_eight
#print axioms eight_mul_arcsin_R0_lt_pi
#print axioms cap_subset_arc
#print axioms card_mul_two_arcsin_ge_two_pi
#print axioms card_mul_two_arcsin_ge_two_pi_of_covers_disk
#print axioms nine_le_card_of_covers_circle_of_lt_R0
#print axioms nine_le_card_of_covers_disk_of_lt_R0
#print axioms not_eight_ball_covers_disk_of_lt_R0
#print axioms dist_inner_root_le
#print axioms dist_inner_root_le_sqrt
#print axioms inner_root_pos
#print axioms capHalfWidth_le_arcsin
#print axioms cap_eq_of_meets
#print axioms innerRoot_replacement_of_disk

-- 装配接口
#print axioms nine_le_card_boundary
#print axioms one_sub_le_norm_of_meetsCircle
#print axioms not_meetsCircle_of_norm_le
#print axioms card_boundaryIdx_le_ten
#print axioms card_boundaryIdx_eq_nine_or_ten
#print axioms not_eight_covers
#print axioms dist_innerRoot_le_of_dist_le
#print axioms covers_of_innerRoot_replace

-- 区间算术内核（interval-core 交付）
#print axioms RatInterval.mem_iff
#print axioms RatInterval.add_mem
#print axioms RatInterval.sub_mem
#print axioms RatInterval.neg_mem
#print axioms RatInterval.mul_mem
#print axioms RatInterval.inv_mem
#print axioms RatInterval.div_mem
#print axioms RatInterval.mul_valid
#print axioms RatInterval.add_valid
#print axioms IExpr.eval_sound

-- 条件模块（带显式前提，**不是**主定理）
#print axioms Rstar_mem_box
#print axioms Rstar_lt_R0_of_bound
#print axioms Rstar_lt_R0_via_cert
#print axioms certBoxHi_six_lt_R0
#print axioms Rstar_lt_R0_of_cert_box
#print axioms Rstar_mem_cert_box
#print axioms n11_main_conditional
#print axioms n11_sInf_conditional
#print axioms n11_main_of_cert_box
#print axioms n11_main_of_C892

-- 源构型：指标绑定（防转写漂移）
#print axioms TCSystem_eR_at_eleven
#print axioms TCSystem_six_no_eR
#print axioms TCSystem_first

-- Krawczyk 的 Banach 收缩步（不依赖区间库）
#print axioms krawczyk_banach


-- 解析桥：导数算子界 ⇒ Krawczyk 前提（不依赖区间库）
#print axioms lipschitzOn_ball_of_deriv_bound
#print axioms krawczyk_banach_of_deriv_bound

-- Krawczyk × TCSystem × 证书盒（G1 的命名化形式）
#print axioms closedBall_eq_pi_Icc
#print axioms mem_closedBall_iff_box
#print axioms mem_certBox_iff
#print axioms exists_unique_TCSystem_of_krawczyk
#print axioms exists_unique_TCSystem_of_cert_box

-- G1 完全组装：逐元素包络 ⇒ 算子界 ⇒ Lipschitz ⇒ 唯一根
#print axioms abs_le_max_abs
#print axioms opNorm_le_rowSum
#print axioms opNorm_le_of_entry_bounds
#print axioms krawczyk_unique_root_of_entry_bounds
#print axioms TCSystem_unique_root_of_entry_bounds

-- 源同一性（G0 的可核验部分）
#print axioms dist_point_eq_sqrt
#print axioms fin9_succ_val
#print axioms angleVec_eq_list
#print axioms residual_eq_list
#print axioms wPoint_coord1

-- G1 前提的区间内核对象化
#print axioms opNorm_le_of_interval_matrix
#print axioms TCSystem_unique_root_of_interval_data

-- 平滑性（G1 义务 (2) 的一阶半）
#print axioms contDiffAt_rhoK
#print axioms contDiffAt_UvecX
#print axioms contDiffAt_UvecY
#print axioms contDiffAt_dist_Uvec_hubOf

-- 供给导数版 Krawczyk（导数义务显式化）
#print axioms lipschitzOn_ball_of_hasFDeriv
#print axioms krawczyk_banach_of_hasFDeriv
#print axioms TCSystem_unique_root_of_hasFDeriv

-- R3 的 ℤ 封装（解除 interval-core 报的 cast 写法障碍）
#print axioms RatInterval.int_cast_toNat
#print axioms RatInterval.int_cast_negToNat
#print axioms RatInterval.sin_cos_shift_halfPi_four
#print axioms RatInterval.sin_shift_halfPi_mem
#print axioms RatInterval.cos_shift_halfPi_mem

-- residual 层级平滑性（G1 义务 (2) 一阶半完整）
#print axioms contDiffAt_WX
#print axioms contDiffAt_WY
#print axioms contDiffAt_ringCenterX
#print axioms contDiffAt_ringCenterY
#print axioms contDiffAt_dist_wPoint_ringCenter
#print axioms contDiffAt_residual_4
#print axioms contDiffAt_residual

-- C² 构件（G1 义务 (2) 的二阶）
#print axioms contDiffAt_pad12
#print axioms contDiffAt_residualFun
#print axioms contDiffAt_fderiv_residualFun

-- TCSystem 可微性 = G1 义务 (2) 收口
#print axioms differentiableAt_first7
#print axioms differentiableAt_last5
#print axioms differentiableAt_adjointBlock
#print axioms differentiableAt_TCSystem

-- 搬运引理（义务 (2) 单条件收口）+ G1 最终形态
#print axioms residual_transport
#print axioms contDiffAt_residualFun_first7
#print axioms differentiableAt_TCSystem_of_conditions
#print axioms TCSystem_unique_root_of_final_data

-- 矩阵桥（Jacobian 包络 + 有理预条件子 ⇒ 义务 (1) 可算形式）
#print axioms dotR_eq_sum
#print axioms ratMatCLM_apply
#print axioms ratMatCLM_single
#print axioms mem_incrMat
#print axioms mem_krawczykMat
#print axioms opNorm_le_of_jacobian_enclosure
#print axioms TCSystem_unique_root_of_jacobian_enclosure

-- 预条件子与残差界的有限有理化
#print axioms ratMatCLM_comp_of_leftInverse
#print axioms injective_ratMatCLM_of_leftInverse
#print axioms dist_sub_eq_norm
#print axioms mem_incrMatVec
#print axioms norm_ratMatCLM_le
#print axioms TCSystem_unique_root_of_full_data

-- 预条件子单射性：另一侧收缩（R10 发现：源 Y 是 binary64 近似逆）
#print axioms injective_of_norm_id_sub_lt_one
#print axioms injective_of_comp_injective
#print axioms ratMatCLM_single_col
#print axioms comp_ratMatCLM_single
#print axioms mem_krawczykMatR
#print axioms injective_ratMatCLM_of_right_contraction
#print axioms injective_ratMatCLM_of_right_enclosure

-- 高阶 sin 有理端点（Lead，R15）
#print axioms N11Formalization.hasDerivAt_sinT
#print axioms N11Formalization.hasDerivAt_cosT_succ
#print axioms N11Formalization.norm_sub_zero_le_of_deriv_bound
#print axioms N11Formalization.sin_cos_remainder
#print axioms N11Formalization.sinLoN_le_sin
#print axioms N11Formalization.sin_le_sinHiN
#print axioms N11Formalization.sinHiN_sub_sinLoN_at_3843_lt_threshold

-- 积分管道（Lagrange 余项装配，Lead R17）
#print axioms N11Formalization.continuous_sinT
#print axioms N11Formalization.continuous_cosT
#print axioms N11Formalization.sin_sub_sinT_eq_integral
#print axioms N11Formalization.cos_sub_cosT_eq_integral

-- Lagrange 余项装配（Lead R18）
#print axioms N11Formalization.integral_pow_div
#print axioms N11Formalization.sin_cos_remainder_lagrange

-- 阶乘版（Lagrange）三角端点（Lead R19）
#print axioms N11Formalization.sin_bound_abs
#print axioms N11Formalization.cos_bound_abs
#print axioms N11Formalization.sinLoNLag_le_sin
#print axioms N11Formalization.sin_le_sinHiNLag
#print axioms N11Formalization.sinHiNLag_sub_sinLoNLag_at_one

-- Fm 的 Fin 12 拼装（box-rstar R20）
#print axioms N11Formalization.hLam_rfl
#print axioms N11Formalization.mem_fmCert_cert

-- 窗口算子可靠性（阶乘版，Lead R22）
#print axioms N11Formalization.sinIHighLag_mem
#print axioms N11Formalization.cosIHighLag_mem

-- Uvec 标量步取值引理（Lead R51）
#print axioms N11Formalization.drhoCLM_single
#print axioms N11Formalization.dring0CLM_single
#print axioms N11Formalization.darc0CLM_single

-- R51/R52 其余引理（Lead）
#print axioms N11Formalization.dring1CLM_single
#print axioms N11Formalization.darc1CLM_single
#print axioms N11Formalization.fderiv_Uvec0
#print axioms N11Formalization.fderiv_Uvec1

-- dist 节点化归（Lead R55）
#print axioms N11Formalization.residualFun_eq_dist

-- 通用 dist 引理（Lead R57）
#print axioms N11Formalization.dist_eq_sqrt_norm_sq
#print axioms N11Formalization.hasFDerivAt_dist_sqrt
