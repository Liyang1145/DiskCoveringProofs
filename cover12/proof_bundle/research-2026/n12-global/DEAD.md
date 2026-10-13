# n=12 DEAD — 建档时风险索引

2026-09-26。本目录尚无新数学反例或判死。以下从 [旧n1314 DEAD](../session2/n1314/DEAD.md) 与 [根DEAD](../../DEAD.md) 提取，不扩大原scope。

## Final verification repairs (not mathematical disproof)

- Lead whole-content audit rejected final cache/provenance byte mismatch: binding witnesses after provenance changed cache bytes; a synthetic N8192 control also appended into production cache. Finite-reduction quarantined the polluted cache, rebuilt only registered production ledgers, added append guards and provenance-after-bind ordering. All6723 actual fresh source rows were independently joined after repair; final frozen hashes match. No global claim uses the rejected states.
- Stress kernel audit F1 found old producer boxes/leaves differ from frozen replay; only source-bound fresh replays bear the proof. F2 depth diagnostics were already excluded. F3 screen=False can invalidate hub-atom necessity; all accepted fresh calls use hash-fixed screen=True default, audited in SOURCE-CALL-CONTRACT.md. No frozen arithmetic changed.

## Latest interface findings (implementation/diagnostic, not mathematical disproof)

- Final-wave b0/b1 dense HiGHS proposal generation crashed `MemoryError: std::bad_alloc`; saved frontiers preserved. Explicit HiGHS threads=1 plus a max4 hidden pool completed every remaining branch in corrected wave4fix. This successful retry does not isolate the cause of the original resource error; proposal failure was never a mathematical disproof.
- Independent original-root prefix verifier rejected bad wave4-base counters: merge hardcoded `shard_splits=3` despite deep0 plan, so processed/split were +3. No gap in geometric frontier was found. Bad base/plan remain quarantined with `members/structure/parallel-domain/wave4-REJECTION-NOTE.md`; replacement wave4fix derives Σ(roots_per_pending−1), checks source and total tree identities, and passes independent prefix validation. Completed-domain-base then passed with6723 atomic318prune0pending. No claim depended on bad wave4.

- `integer_kernel.certify(max_depth=23)` only echoes max_depth on an unresolved return; actual stop is max ring-box width≤16 integer units. At scale 2^26/2^28 the maximum per-coordinate bisection counts are 23/25, and binary path counts 46/50. Certified outcomes do not use the misleading diagnostic field; frozen kernel left unchanged. See `members/upper-audit/integer-atomic/audit-scale28.md`.
- First generic reshard worker launch failed before creating leaves because plan.source.path was relative to plan directory but executed from workspace root. Worker and merger now resolve that path with explicit plan-parent fallback and still compare source bytes hash. Re-launched successfully; prior stderr retained. No coverage inference arose from the failure.
- Unsupported claim that the isolated root is irrational was removed from the member closure audit: algebraic root isolation alone does not establish irrationality. Root-below-U comparison uses the closed original rational box upper endpoint only.
- Cache provenance audit found old builder/migration paths could stamp current kernel keys without sufficiently checking original row sources, and compaction can obscure fresh execution ancestry. Repair in progress in finite-reduction scope; final replay acceptance requires a chain to archived fresh rows with identical content and source hashes, not merely self-consistent cache keys or positive status text. No unrestricted global n12 claim has been issued.

## 输入与实现错误

- 旧D4：12位截断坐标改变n12半径约4.3e-13，不能用于重放17位字面证书。使用 centers_dec17 原字符串和精确有理解释。
- 旧D5：`float(Fraction)`打印会吞掉承重差值。阈值必须精确向外舍入，R_float仅诊断。
- D3装置的字符串→Number→17位固化须核对字面差异；不同有理构型即便数值接近，也必须重新建立对象同一或转移界。
- 旧cover_n_uncovered与REPORT口径差异已解决：36个失败盒均为D外外心；0/328为域过滤版本。同一cert_all.json共存flat36与nested0/328。证据members/upper-audit/REPORT.md及logs/。这是诊断口径差异，不是覆盖反例；历史中间源码修改顺序只能作证据推断。
- candidate_coverage的min距离下界未超阈值只是必要条件，不能推出整个候选盒被覆盖；REPORT已标诊断非证明。D1使用距离上界、D2及新的精确符号判据不受此错误说明影响。

## 不接受的推理

- 未搜到更好 ⇒ 最优；求解器失败 ⇒ 分支不存在。
- 特定图/9+3/D3族内证书 ⇒ 任意12盘全局最优。
- 有限候选见证被覆盖 ⇒ 整个单位盘被覆盖（除非已证候选完整性与退化覆盖）。
- 很小残差 ⇒ 精确根；很小奇异值 ⇒ 精确秩亏；独立成员同样输出 ⇒ 数学独立认证。
- 原n1314对n13–18的结构搜索失败 ⇒ n12对应族不可能。
- 旧公开对照比较 ⇒ 2026年的最好已知或新颖性。

## 方法边界

旧D1–D3是指定种子/结构变换/时间预算下的搜索表现，不是对所有此类方法的否证，也不证明“强局部极小”。旧公式归一化问题（D6）和低分辨率图反演（D7）应先校准再使用。

后续每条失败要分清 mathematical disproof / retraction / implementation failure / method limit / budget stop，注明对象、作用域、证据与影响；不为增加条目而判死。

## 本次研究新增边界

- **method diagnostic（不是判死）**：Lead同心双圆常权有界probe在r=U，对k9/10/11最佳采样残差仍为+.11624/+.26913/+.13025；未找到可认证排除权。证据 `evidence/concentric-capacity-probe.json`，复现 `py -3 -B research-2026/n12-global/lead/concentric_capacity_probe.py`。采样既不证明所有此类权失败，也不证明任何覆盖存在；不扩大同型网格，转偏心方向权/耦合几何。
- **source/provenance correction**：新抓取Math.SE Q2651575发现Pegg更新位于问题正文，关系写≈不是等号；原lit2关于精确代数最好已知构型的强解读未获几何证明支持。见 `lead/LITERATURE-CHECK.md`。不影响C182原有理构型D1覆盖上界；影响历史比较/新颖性措辞，勿混同。
- **implementation（已修复新脚本，不改旧证据）**：初次replay子Python默认GBK stdout导致日志不可作为UTF-8读取；新runner显式PYTHONIOENCODING=utf-8后重放成功。算术对象/阈值未改变。

- **numeric overclaim corrected (structure member)**: 17-place rational candidate has no proved exact D3 or exact boundary tiling merely from printed norms/angles summing360. Numeric structured-family grid R is a lower bound on that fixed configuration radius, not an upper or proof of family optimality. Member redirected to k11 dual capacity; no accepted claim depends on these diagnostics.
- **radial-domain interface correction**: an eccentric hub does NOT exempt exactly all points with norm≤r−e on every ray and require all points above that norm; r−e is the minimum outward radial endpoint, whereas actual endpoint depends on direction. Use S(h,q), q↓r, or exact ray roots.
- **exact checker safety repaired**: legal-domain assertions and s>0 radical guard now fail loudly; main exits nonzero on errors. Previous C182 input was within domain, so its value was not retracted. New Lead replay accepts exactU.

- **two-hub angular kernel bug (Lead audit)**: first dual_lp.py arc intersection used only one wrapped lift. For an exposed arc of halfwidth>π/2, intersections with a ring arc can have2 components; e.g. halfwidths3 and1, relative centerπ. Missing second component undercounts capture and can produce false margins. Old dual_scan results are not valid exclusion evidence. Member tasked with three-lift repair and direct angular quadrature controls before further scans. Mathematical capacity method not disproved.

## Candidate coverage wrong-object implementation (not mathematical disproof)
Lead inspection found members/candidate/coverage_and_stress.py rebuilt rotated original17-digit literal, NOT the ideal F,G,H,T root configuration, then scanned4 million boundary samples with mpmath and claimed equality with root radius. Invalid both by input object and continuum inference. Interrupted member and requested stop its exact scan job; no such coverage output is accepted. Lead independently certified F,G,H,T root via rational-grid Banach map (lead/root_t_certificate.py); root existence survives because separate kernel/input. Ideal-configuration coverage remains pending.

## Original-dual m2 trivalence error (repaired)
Original m2 quad cocircular faces were incorrectly excluded by asserting all spoke faces shared one hub. They need not. Removed from member topology proof; correct reduction is fan-triangulate each dual polygon and duplicate its original common witness. The actual diagram need not be trivalent, only the relaxed metric network does.

## Two-hub interval prototype withdrawn
C953 withdrawn by producer: non-directed float endpoints plus unbounded1e−9 padding was not interval certification. Repaired version C959 still under lead audit (polar-angle corner enclosure and exact domain mesh endpoints). No k10 exclusion accepted from either point experiment.

## Two-hub repeated kernel audit (pending producer resolution)
Lead inspection flagged certify_ring2.py intersection endpoints using exposed arc center without halfwidth, which would undercount cap; notified producer to retract dependent fixed-point/box certifications and independently calibrate against single-point arc integration. Also unwrap used nondirected mp additions of2π, needs integer lifts applied with interval2π and branch verification. Even after four-corner angle argument repaired, radial edges are monotone, not generally constant. No k10 mathematical disproof follows; no accepted global inference depends on this kernel. Upper-audit assigned independent representation/calibration before scaling.

## k11 numpy interval prototype invalid (implementation, replaced)
Member certify_segments.py reversed acos endpoints, used incorrect signed multiplication/division bounds, and nondirected np transcendentals/float domain endpoints. No certified exclusion accepted from it. Lead replaced entire bearing kernel with exact rational parameter boxes + mpmath.iv scalar arithmetic in lead/onehub_interval_certificate.py; all12 segments pass and independent calibration assigned. Mathematical Fourier measure remains valid; only scout proposed weights reused and explicitly rechecked.

## Additional implementation/method boundaries
- **Independent audit kernel error, not Lead-kernel error**: onehub-audit originally inserted sin/cos extrema only when the entire rational pi enclosure was contained in the input interval. Lead identified missing extrema when the enclosure straddles endpoints; must insert extrema on nonempty intersection. Custom independent replay is pending correction/impact audit. Lead mpmath.iv k11/nearmerge certificates are unaffected.
- **Method limits, not disproof**: continuous hub interval Fourier cap at epsilon=.005 and atomic N512 at epsilon=.001 did not certify. Exact rational atom N2048 at epsilon=.001 succeeded; changing the finite measure is legitimate, no convergence/quadrature inference. Wider box remains unresolved until split.
- **Numeric proposal scope correction**: member twohub sampled point/joint LP success does not imply every point in a layer has a weight; first probe also had illegal domain points, saved INVALID. Only exact/interval hub pruning and atomic capture bounds delete boxes.

## Integer verification interfaces (implementation corrections)
- Independent integer-manifest draft incorrectly inferred disjoint cover from containment plus equal total volume. This is false (overlap can compensate holes); Lead caught it before acceptance. Replaced by exact recursive tiling, all frontier boxes visited exactly once, explicit duplicate checks. Draft resume also failed hash binding and combined counts, and periodic summary did not write; repaired before full run. No global claim depended on draft.
- Integer kernel calibration helper used negative modulo at depth0 and produced an out-of-domain box. Core distance kernel unaffected; class domain assertions exposed it. Helper now uses -S+k*width with legal integer index. Frozen kernel SHA256 0115c3f3660382cc5bcc53c1faf287ff624ca2f2c649a02035b7494759c0fc50.
- Independent core-net draft missed multiplying the antipodal vector(-1,0) by core radius; this incorrectly preempted13 bisector prune records. Producer repaired before full replay; exact core membership required. All13 bisector records now verified separately.
- Custom onehub trig repair completed: old replay rescinded, new intersection-based kernel replayed all12 segments. Lead k11 evidence unaffected; supplementary corrected independent replay now available.

## Run3 proposal obstruction (method, not disproof)
At processed11226 the default order4/24x120 proposal plus2048 atoms reached width<1e-5 near(s,x,y)=(.1712255,.0407643,.0215010). Ring rectangle capture still violates10M<T. Unresolved box requeued, all16 pending retained; no global certificate. This is a failure of the proposed witness, not a feasible disk cover. Independent experiment: dense order6/96x720 plus8192 atoms certifies a larger neighboring ancestor; pure-int64 check accepts with gap4100547. Both denser proposal and atom count needed in this test. Run4 therefore adds that exact-integer fallback only on small boxes (maxwidth<.002) after default failure. Original snapshot archived hubline-domain-run3-stuck.json; processed count corrected by−1 because tiny-stop requeued item was not a leaf/split. No geometry/leaf/queue change.

## Parallel/cache interface corrections (implementation; no theorem reversal)
Lead source inspection found merge summary computed pending from counts although worker counts has no pending key; zero default could falsely label partial branch assembly full. No global result adopted; actual pending list retained. Also merge comment claimed plan revalidation but only volume/disjointness performed, omitted source hash/containment checks; delegated repair with exact parent tree validation and single-read byte hashes. N-generalized cache importer similarly lost snapshot/content-key checks in refactor; fix and negative controls requested, existing cache provenance must be audited before downstream adoption. These are implementation failures, not mathematical disproofs. Hidden execution required after visible-terminal launch error; pool now3 workers plus1 verifier.
