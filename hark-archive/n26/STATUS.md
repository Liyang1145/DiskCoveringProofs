# n=26 (Liyang1145/DiskCoveringProofs) — status after sandbox session 2026-10-14

**n=26 is NOT proved.** Nothing was pushed, and no issues or comments were opened.
Everything below is arithmetic inside the archive's 134-rod energy model of the
candidate type. It is **not** a formal geometry payment. The counts "16 candidate
roots" and "344 root25 OPEN subdomains" are different levels. I never subtract one
from the other.

## 1. Map of what remains

### 1a. Formal layer
Sources: the committed formal head `n26-mixed-after-six-midarc-supplemental-current-v1.json`
(SHA256 `ba52dbb5…a81a1`, freshly downloaded and hash-matched), plus v80 obligations.

* **16 unresolved whole candidate-angle roots** (closed boxes of the candidate
  type's 15-dim anchor-turn domain). Indices: 1, 5, 9, 13, 17, 21, 25, 29, 28, 24, 20, 16, 12, 8, 959, 1023.
  * Each one closes only when its *entire* closed root box is covered by accepted
    leaves of these kinds: strict energy/force (`FULL134-CORRELATED-ENERGY`,
    `ALTERNATIVE-SIGNED-ENERGY`, origin-branch energy with **both** owners 16 and 25),
    `SHARP_EMPTY`, or LOCAL/pinning (the 52-coordinate LOCAL allowance 7/800000 plus
    anchor pinning).
  * Every leaf then needs current-source geometry admission and an independent final.
  * Nine roots (37, 41, 45, 48, 44, 40, 33, 36, 32) closed on 2026-10-13 using
    mixed-curvature hulls, integrated Taylor bounds, and the original LOCAL.
  * Roots 25 and 28 have partial arithmetic forests:
    * root25: 344 OPEN.
    * root28 grown v9: 1551 OPEN (historical).
* **Same-root (R\*) conditional combinatorial frontier: 4957 pending source prefixes**,
  down from 5637 after midarc removed 680. By family:
  * B14: 296
  * B15: 647
  * B16: 2164 (includes 2 unresolved terminals)
  * B17: 1850
* The original-U frontier of 3922 is unchanged.
* Earlier tools that closed similar items:
  * six-core filled-ear capacity: 5546 prefixes
  * midarc filled patch: 680
  * area (single and multi slope), integer force forests, and complete angular trees
    (staged force forests v1–v11)
  * correlated or sharp force leaves, SHARP_HULL_LOCAL pinning, and mixed-curvature hulls
    (the 9 roots)

### 1b. Arithmetic branch root25
Source: committed `n26-root25-current346-refit2-origin-append-composition-v1.json`. I rebuilt it
from its 6 gzip parts. SHA256 `c1675552…87c9` matches the README.

* The tree has 2999 nodes and **344 OPEN closed boxes**.
* Paid leaves: 624 FULL134-CORRELATED, 488 ALTERNATIVE-SIGNED, and 44 origin-branch leaves.
* There are 29 full134 physical supports and 16 fresh origin supports.
* What closing a box needs (archive rule): either
  * one positive weight vector w on the 134 rods, with Schur energy
    Φ_w(θ) > W·R\*² on the whole closed box, or
  * both origin-owner branches strict, Φ_w + μ/(1+μR_v)|Σh_v a|² > (W+μ)R\*², for v=16 and v=25.

### 1c. Global obligations still open
These hold no matter what the counts above are.
1. A complete four-family catalogue (B,I) = (14,12), (15,11), (16,10), (17,9) at R\*. That means exhausting all 4957 prefixes, including the B16 terminals.
2. Final joint acceptance of the reduction from an arbitrary cover to the triangulated disk. This is written (`n26-geometric-bridge-v1.md`, interface review v2) but still *pending*.
3. Lower bounds for every competitor type, plus all 16 candidate roots.
4. Same-root composition with the upper bound, evidence closure, and an independent joint final.
5. The external dependency: the Fejes Tóth 8-disk theorem is used but not re-proved.
6. Replay blocker: **1035 dependency files of the root25 chain are missing from the public repo.** These include SYSTEM.json, the old92 reference, and checkpoints (see `verification/reproducibility/n26-public-content-audit-20261014.json`). So the archived chain cannot be replayed from the repo alone.

## 2. What I attempted

1. **Rebuilt the rod model from committed bytes.**
   * The 134-rod edge list is not committed. I recovered it from a committed kernel: K_FF = D·N⁻¹ mod (2⁵²¹−1), then checked it by the exact integer identity N·K_FF = D·I.
   * All **29 committed full134 kernels pass** the archive's exact gates on my edge list: inverse identity, convex harmonic rows, zero-row-sum symmetric Schur matrix with nonpositive off-diagonals.
   * W·R\*²_up reproduces the ledger's `NEW_full134rod_energy_upper_at_same_root` exactly.
   * Files: `reconstruct_model.py`, `n26model.py`, `model134.json` (34 faces, 134 edges).
2. **Numerical diagnostic of all 344 OPEN boxes** (`diag_open.py`, results in `diag_merged.json`; not a proof).
   * Computed: min over the box of the 134-rod model radius, with no origin constraint.
   * Result: **every box has a model minimum > R\*, except box 1669.**
   * Box 1669 has minimum = R\* to 1e-14, at θ = the D2 candidate itself (θ_{k+8} = θ_k + ½, θ_8 = ½). So box 1669 contains the exact candidate. It can never be closed by a strict energy bound and needs a LOCAL/pinning carve-out.
   * Margins above R\*: median 7.2e-4, 5th percentile 1.9e-4, smallest non-candidate 7.3e-5.
   * Conclusion: the energy route is **not stuck** on root25. Earlier failures came from reusing a fixed table of supports instead of fitting fresh ones.
3. **New certificates: fresh per-sub-box fitted weights with rigorous branch-and-bound** (`certify_box.py`, `bnb.py`).
   * Floats only *propose*:
     * weights: dual of the min-max rod SOCP at the worst point
     * evaluation centre
     * QP minimiser
   * Rigorous verdict path:
     * weights rationalised and made positive (denominator 1e12);
     * exact Schur complement in python-flint fmpq; G positive definite by exact LDL;
     * arb-ball 2nd-order Taylor at the box centre, with cubic remainder (8/3)π³Σc(r_i+r_j)³;
     * exact-LDL PSD split with a negative-curvature penalty;
     * convex-QP supporting-hyperplane lower bound;
     * strict test against W·R\*_up².
   * It uses the **no-origin** model, so one certificate excludes both owner branches at once.
4. **Independent re-checker** (`verify_certs.py`). It imports neither of the above. It uses:
   * Kron/star-mesh elimination in pure Fractions;
   * mpmath interval arithmetic at 160 bits;
   * a different QP proposer (projected gradient);
   * exact replay of the closed split partition;
   * root boxes compared verbatim with the committed OPEN boxes.

## 3. Newly closed (arithmetic only, unadmitted)

* **root25 OPEN: 344 → 219.**
* **125 whole OPEN boxes** are covered by **329 leaf certificates**. All 125 were re-verified CLOSED by `verify_certs.py`.
* Smallest rigorous margin: (Φ−W·R\*²)/W ≥ 1.64e-6, at box 2343.
* Lists: `ROOT25-FRESH-RESULT.json` (closed indices, the 219 remaining, partial boxes). Certificates: `certs/<index>.json`.
* 13 more boxes are partly certified, with OPEN sub-boxes left by the time budget: 1685, 1686, 1978, 2007, 2010, 2209, 2211, 2289, 2295, 2296, 2339, 2340, 2342. These count as OPEN.
* Unchanged:
  * **16 candidate roots: still 16.** root25 is not closed.
  * Formal payments: 0.
  * 4957 frontier unchanged.
  * Global lower bound not proved.

## 4. What failed or limits this

* I **stopped the branch-and-bound at 138 of 344 boxes** under the loop rule. Repeated runs stopped making progress: the sandbox ran my commands concurrently in several containers with inconsistent views of the files, so results vanished or were recomputed. This was not a mathematical failure.
* The working directory `/workspace/work` briefly disappeared once. Python packages had to be reinstalled (`pip install --user numpy scipy python-flint cvxpy mpmath`).
* Soundness scope:
  * I check arithmetic only.
  * The facts that the 134 rods are necessary, the labels/owners, the B16 34-face type, the use of original-26 cardinality, and root25 being a correct root box all come from the archive's interface proofs. I did not re-prove them.
  * The difference polytope is not used. Using the whole box is conservative.
  * The model edge list is inferred. The exact kernel gates support it strongly, but it is not checked against the missing SYSTEM.json.

## 5. Recommended next attack

1. **Finish root25 with the same method.**
   * Scope: 218 non-candidate boxes plus the 13 partial ones.
   * Compute: about 4–25 CPU-hours (hard boxes need 50–300 leaves at about 1–1.5 s per leaf). That is about 2–12 h on 2 cores, or under 1 h on a 16–32 core workstation.
   * Speed-up: fit weights robustly over several sample points of a sub-box (concave max-min SOCP). This should cut the leaf count a lot.
2. **Box 1669.**
   * Put the exact candidate turns inside an explicit tiny closed box. Pay it with the existing LOCAL + refined-anchor-pinning certificates.
   * Cover the rest with energy branch-and-bound. Near the candidate the margin grows quadratically, and my bound keeps the PSD Hessian, so the leaf count should stay manageable.
   * Doing both 1 and 2 would give a complete arithmetic forest for **root25**, which can then go to source-geometry admission.
3. **Apply the same diagnostic and fitted B&B to root28** (1551 OPEN) and the other 13 roots.
   * Check first with `diag_open.py` that no box's model minimum falls below R\*.
   * Any box whose minimum does fall below R\* is a genuine model counterexample. It needs a new geometric constraint (for example |c_i| ≥ 1−ρ for boundary centres, or core-coverage), not more fitting.
4. Commit the 134-rod edge list or SYSTEM.json and the other 1035 missing inputs (user approval needed), so third parties can replay the chain.

## Artifacts (all under /workspace/work/dcp-n26/)
* Scripts: `reconstruct_model.py`, `n26model.py`, `validate1.py`, `diag_open.py`, `certify_box.py`, `bnb.py`, `verify_certs.py`.
* Model: `model134.json`. Pending boxes: `pending.json` (copied verbatim from the committed root25 file).
* Results:
  * `diag_merged.json`
  * `certs/*.json` (138 files)
  * `ver*.jsonl` (independent check output)
  * `ROOT25-FRESH-RESULT.json`
  * `certs_summary.json`
* Downloads: `dl/root25.json(.gz)` (480 MB, hash-checked), `dl/midarc.json`, `repo/` (sparse clone).

## 2026-10-15 update
- root25 OPEN 344 -> 1 (box 1669). ROOT25-FOREST-INDEX.json: 343 CLOSED-ENERGY, 549 energy leaves, min margin/W 6.16e-8, all re-verified by verify_certs.py.
- 1669: everything outside Q_6 (half-width 6.4e-6) certified (165 leaves). Pinning (float estimate) fits 7/800000 only up to Q_1 (2e-7). Gap Q_1..Q_6 needs exact pinning rerun (non-public sources) + high-precision energy, or larger LOCAL allowance, or 2nd-order local cert.
- root28: real 1551 OPEN boxes not public; screen on inferred root box (512 sub-boxes) found no model min <= R* (closest = candidate near-touch).
- Model still the reconstructed 134-rod list; not checked vs SYSTEM.json.

## 2026-10-15 晚 会话 b（结果文件已丢失，仅存结论，需重做）
子代理在 21:30 左右遭遇持久盘掉挂，所有产物写在 /tmp/n26 和 UNMERGED 目录，容器重建后全部丢失。以下结论**未保留证书，不算闭合**，需按此思路重做并复核：
1. 用已提交 outputs/n26-candidate-full134rod-minimax-relaxation-diagnosis-v1.json 的 NEW_distinct_full134rod_edges，80 位求解最优性方程复现 60 位 R*；候选精确 D2 对称（θ8=½）。
2. 候选处单一权重 Hessian 有负特征值（−0.044）；10 个见证三元组在 R* 处乘子为 0，5 个方向半径线性增长，其余 10 维 Hessian 正（最小约 0.009）。故用「有限组权重取最大」的局部证书：10 组非负有理权重 + 10 方向扇区覆盖，覆盖 ∞-距离 1e-26 到 1.2e-5 的环（双复核器 A=flint/arb、B=Fraction/mpmath 均通过，最小 bound/W≈1.9e-55）。此叶型尚非存档接受类型，需写成接口引理。
3. 盒 1669 并不包含候选：候选在轴 6、7 上越出盒上界 2.945e-10。旧树唯一 OPEN 节点 Q6∩1669 用局部证书闭合（bound/W≈3.6e-22）；与 certs1669/ 旧 165 叶合并即 root25 344/344（算术层），合并待做。
4. 重放已提交 work/n26-sharp-candidate-angles-proposal-v3.json（用 n26_force.tighten）：38 OPEN + 1 LOCAL（节点 59，含候选的 7e-10 立方）。曾闭合 14 个 OPEN 节点（97,98,99,100,135,136,175,176,289,290,296,308,295,304），均不在 16 根名单。
5. root28：旧 inferred box 与重放树节点 28 在轴 6–13 不符，应改用重放盒。其余根数值分诊未见低于 R* 的点，远场估计需 1e6+ 叶。959/1023 不在 v3 树中。
环境：shell 每条 120s 上限，后台进程随命令返回被杀，必须 ≤110s 分块且结果直接写 /workspace/work/dcp-n26 下。

## 2026-10-16 00:45–01:40 CST 看护轮：盒 1669 的 Q6 用局部切片森林闭合 → root25 344/344（算术层）
- 方法（产物全在 local/，未用 /tmp）：c* = kkt2_122.json 的 58 位 θ*；hp.py 复现 Φ_λ0(θ*)−R*² = −4.4e-61、H0 最小特征 −0.0444（与会话 b 一致）。
- 关键事实：零乘子三元组加权有线性亏损，不可用；改为在 92 根正乘子杆上扰动 w = λ0 + κ τ0，τ0 = D⁺G u0（u0 = H0 负特征向量）。二阶模型 sup_τ = ½uᵀ(H0+GᵀD⁺G)u，最小特征 0.081（浮点提议）。
- 覆盖：R = Q6∩1669 绕 c* 在轴 6–14 分 15 层壳 ρ_m = 6.6e-6/2^m（Q(15) 为空，因盒在轴 6、7 上界 = θ*−2.945e-10），每壳 ≤15 片，每片按 b = v·d（v = N u0）切成长 0.3ρ 的段；每段一组权重 κ = b_mid/a，S-引理项 −μ(b−ba)(bb−b)（μ = 11/200）使 H+2μvvᵀ PSD。
- 复核：certA.py（flint arb 320 位 + 精确 LDL + 有限 ν LP）与 certB.py（mpmath iv 420 位、星网 Kron 消元、Fraction 消元、全断点 LP、SLSQP 提议、从 certs/1669.json 树重新推出 R 与全部壳片并检查段连续覆盖）均 211/211 片、2452 叶通过；最小界 A 3.5e-21，B 3.6e-21（W≈1）。
- 合并：certs/1669.json 的 OPEN 节点换成 LOCAL-SLAB-FOREST → local/FOREST-Q6.json（sha256 612d8d6a…）；旧版在 certs_old/1669.pre-local.json。ROOT25-FOREST-INDEX：343 CLOSED-ENERGY + 1 CLOSED-ENERGY+LOCAL-SLAB-FOREST，OPEN 0。
- 未用 pinning；165 个外层叶沿用 ver1669.json 的 verify_certs.py 结论（未重跑）。
- 口径：仅 134 杆重建模型算术层；内层权重是非负（部分杆权重为 0），不是存档接受的严格正权叶型，需接口引理；不是几何付款；16 个候选根仍是 16（root25 还需源几何准入）；n=26 未证。
- 2026-10-16 09:50 看护轮：v3replay bstep B 复核块推进（见输出），未闭合新批次

## 2026-10-16 11:45–12:35 CST 子代理 n26-open23b（接管崩溃前任）：v3 树剩余 23 个 OPEN 节点全部算术层闭合（A+B）
- 崩溃原因（推断）：容器重建后 numpy/scipy/python-flint/mpmath 丢失（已 pip 重装）；另外 B 全树单进程 ~1.45 GB，在外部内存压力下被 OOM 杀。
- 树：v3replay/V3-REPLAY-TREE.json sha256 beab24c5…aa07，184655 节点（SPLIT 92327 / FORCE 86025 / LOCAL-SLAB 6302 / 存档 LOCAL 1 = 节点 59），OPEN 0。
- 复核器 A（replayA_t.py，存档 n26_force.tighten + force_check；LOCAL-SLAB 由 certA 界）：23/23 complete（verA_open23.json）。
- 复核器 B（certB_v3.py 自有 domain/tight/force_B + local/certB 能量）：新增 certB_walk.py（可续跑全树遍历 → verB_walkcache.pkl）、certB_prep.py + certB_lite.py（低内存、逐片检查点，检查逻辑同 certB_v3）；全树 92328 叶全部通过（verB_v3_0/1.json）。节点 1 的 B 结论沿用 49d546 树：已用 assemble_recon49.py 逐字节重建出 49d546，其 42777 节点除 22 个 OPEN 占位外为当前树精确前缀。另做的节点 1 独立 B 重跑（verB_v3_*_n1.json）完成 12455/20222 叶，全过，未跑完（冗余，不影响结论）。
- 23 节点 1,5,9,13,17,21,25,29,33,37,41,45,48,44,40,36,32,24,20,16,12,8,4 全部 A+B 通过：共 85341 FORCE 叶 + 5842 LOCAL-SLAB 叶。最小余量：FORCE A 1.397e-14 / B 1.397e-14（节点 4）；能量界 A 6.87e-24 / B 8.50e-24（节点 13、45）。明细 v3replay/open23_AB_summary.json；V3-REPLAY-RESULT.json 已更新（remaining_open_v3_nodes = []）。
- 口径：仅算术层（134 杆重建模型 / 存档 direct-arc force，半径比 RSTAR_UP）；LOCAL-SLAB 非存档接受叶型，需接口引理；节点 59 仍是存档 LOCAL 钉扎格（未在此复核）；不是几何付款；n=26 未证。未推送任何仓库。

## 2026-10-16 12:47–12:55 看护轮：节点 59 局部切片 pilot（A 侧）
壳 m0..m7 共 205 片全部 certA 闭合（0 OPEN，最小 bound/ρ²=3.76e-4），中心立方仍为存档 LOCAL；未做独立 B，不算闭合；仅算术层，n=26 未证。

## 2026-10-16 13:15–13:30 看护轮：节点 59 pilot
A 侧 12 层壳 341 片全闭合（最小 bound/ρ²=3.76e-4）；新写独立 B 复核器 certB59.py（自行重推壳几何+覆盖连续性，调 certB.check_leaf），116/341 通过，余下续跑。仅算术层，中心立方仍 LOCAL；n=26 未证。

## 看护轮 2026-10-16 14:05 CST — 节点59 pilot 双复核
节点59 局部切片 pilot：A 341 片 + 独立 B（certB59.py）341/341 通过，0 OPEN；壳 m0..m11，B 最小 bound/ρ²=5.76e-4（A 3.76e-4）。中心立方 m≥12 仍为存档 LOCAL。仅算术层，不称 n=26 已证。

## 看护轮 2026-10-16 14:45 CST — verify_certs 加固 + 节点 1 B 重跑
- verify_certs.py 现识别 LOCAL-SLAB-FOREST（forest 文件 sha、区域=叶盒、输入哈希、211 片体积精确平铺且内部不相交、certB 211/211 状态、片数/叶数一致）；整盒 1669：165/165 外层叶重算通过（min margin/W 1.278e-11），CLOSED_WITH_LOCAL_SLAB_FOREST=true（备份 verify_certs_v3_pre_slabforest.py）。
- v3 树节点 1 的第二次独立 B 重跑完成：19819 FORCE + 403 LOCAL-SLAB 全通过（min FORCE margin 2.47e-14）。
- 队列 1–5 已全部完成；剩余：节点 59 中心立方（存档 LOCAL）、959/1023（盒不可重建）。仅算术层；不是几何付款；n=26 未证。

## 看护轮 2026-10-16 14:55 CST — root25 全量回归
加固后 verify_certs.py 对 certs/ 344 盒全量重跑：343 CLOSED + 1669 CLOSED_WITH_LOCAL_SLAB_FOREST，无 OPEN/FAIL（regress_v3.json）。仅算术层；不是几何付款；n=26 未证。

## 看护轮 2026-10-16 15:20–15:45 CST — 节点59 局部切片壳扩到 m0..m15
pilot59.py 补算 m12..m15（120 片），A 461/461 闭合（最小 bound/ρ²=3.76e-4）；独立 B（certB59.py 16）461/461 通过（B 最小 5.76e-4）。存档 LOCAL 中心立方半径由 R0/2^12 缩到 R0/2^16（R0=6.716e-10，故≈1.0e-14）。仅算术层；中心小立方仍为存档 LOCAL；非几何付款；n=26 未证。
- 看护轮 16:15：节点59 pilot A 壳到 m20 完成，B 续跑中（≥508 片通过）。仅算术层，n=26 未证。
- 看护轮 17:25：节点59 pilot A 壳到 m24 完成（~700 片）；certB59.py 24 续跑中（628 已验，余下待续，预算 100–104 轮换，勿并行跑）。仅算术层，n=26 未证。
- 看护轮 18:25：节点59 壳 m0..m24 A+B 701/701 全通过（B 最小 5.76e-4）；中心立方 m≥25 仍存档 LOCAL。仅算术层，n=26 未证。下一步：LOCAL-SLAB 接口引理草案或继续 m>24。
- 看护轮 18:55：节点59 pilot A 续跑到 m=28（重装依赖后，进行中，B 未做）。仅算术层，n=26 未证。
- 看护轮 19:58：节点59 壳 m0..m27 A+B 821/821 全通过（B 最小 5.76e-4）；中心立方 m≥28 仍存档 LOCAL。仅算术层，n=26 未证。
- 看护轮 20:35：节点59 壳 m0..m31 A+B 941/941 全通过（B 最小 5.76e-4）；中心立方 m≥32 仍存档 LOCAL（半径≈R0/2^32≈1.6e-19）。仅算术层，n=26 未证。

## 看护轮 21:05 CST
节点59 壳 m0..m39 A+B 1181/1181 通过（算术层；中心立方 m>=40 仍存档 LOCAL；未称 n=26 已证）。
- 看护轮 21:55：节点59 pilot A 续跑 m=48（重装依赖；约1285 文件，未完成，B 未做）。下一步：pilot59.py 100 48 续跑后 certB59.py 48。
- 看护轮 00:25：重装依赖，pilot59.py 续跑 3 块（A 侧，lleaves/59pilot 1533 文件，m=52 未完成，B 未做）。下一步：pilot59.py 104 52 直至完成，再 certB59.py 52。
- 看护轮 02:50：pilot59.py 到 m=60 续跑3块（A 侧，lleaves/59pilot 文件数增长，未完成，B 未做）。下一步：pilot59.py 103 60 直至完成，再 certB59.py 60。
- 看护轮 07:25：重装依赖；pilot59 A 到 m=68 已完成(1982 文件)；certB59.py 68 续跑，已验≥1805（预算100–110轮换）。n=26 未证。
- 看护轮 13:20：重装依赖，certB59.py 67 回归复核一块，全通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 13:50：重装依赖，certB59.py 105 67 回归一块，1997 项全通过，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 16:25：certB59.py 106 67 回归一块，1991/1997 已验无失败，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 16:50：重装依赖，certB59.py 107 67 回归一块，1991/1997 无失败，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 18:50：重装依赖，certB59.py 108 67 回归一块，1991/1997 无失败，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。
- 看护轮 21:20：重装依赖，certB59.py 109 67 回归一块，无新增闭合。下一步：LOCAL-SLAB 接口引理草案。

## 2026-10-18 05:55
节点28 218 LOCAL-SLAB 叶 2654 片 certA+certB 双复核通过(算术层)。
- 11:55 非28 LOCAL-SLAB 叶(884叶/11257片) certA 全通过；待 certB。
