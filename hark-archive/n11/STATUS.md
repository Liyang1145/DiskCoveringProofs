# n = 11 Lean 4 formalization — STATUS (second pass, 2026-10-15, Asia/Shanghai)

GitHub: since 2026-10-15 16:19 CST the WIP build runs in GitHub Actions on branch `ci/n11-build` of
Liyang1145/DiskCoveringProofs (user-approved; branch only, `main` untouched, no PR/issue/comment). See §9 and `ci/README.md`.

## 0. Bottom line

* The team's WIP (`wip/lean/`, restored from release `proof-assets-core-20261014`,
  `n11-wip-0001.zip`) is **the** n=11 formalization. Our 2026-10-14 skeleton (`lean/DCPN11/`,
  12 sorry, never compiled) is **superseded and frozen**: it re-states pieces the WIP has
  already paid. Do not develop it further; new work targets WIP names.
* WIP main theorem (conditional, no sorry):
  `N11Formalization.ActualMainRoute.main_of_remaining (h450) (henergy) (h33) :
   N11MainStatement SourceExactRoot.sourceRadius`.
  `sourceRadius := sourceRoot 6` is the SAME C891 boxed TC/KKT12 root, coordinate 6.
  **The full n=11 statement is NOT proved.** Three named Props are unpaid (§2).
* This pass added, **compiled in core Lean 4.35.0 (no Mathlib)**: an independent kernel
  replay of every exact-rational premise of the WIP C450 packet certificates for
  **segments Source23..Source36 (14 segments, 6,956 packets, 448 cells)**, with a soundness
  lemma into a field-for-field restatement of the WIP `Valid`, plus negative controls. All
  pass. Axiom audit: 61/61 reports `[propext, Classical.choice, Quot.sound]`.
  An exact-`Fraction` Python replay covers all 26 segments Source11..36 (13,262 packets):
  all pass, 0 issues. **This is pre-validation evidence, not C450 credit**: the
  real-analytic step (`cell_of_packet`, Mathlib) and the root build of Source14..36 remain.
* Mathlib still could not be compiled here (§4). Stopped after the allowed attempts.

## 1. Restore (step 1)

| Item | Value |
|---|---|
| Package index | repo `assets/replay/n11-wip/PACKAGES.json` (complete=true, mathematical_verification=not_performed) |
| Downloaded | `proof-assets-core-20261014/n11-wip-FILES.jsonl.gz` sha256 `2aa324a3…ba15d` ✓; `n11-wip-0001.zip` 47,133,937 B sha256 `378b6501…45367` ✓ |
| Per-file check | 2383/2383 members match ledger (sha256 + length), 0 mismatches |
| Location | `hark-archive/n11/wip/` (= `build/n11-wip/assets/` layout; `wip/lean` = asset `lean/`). Ledger copy: `wip-LEDGER.jsonl.gz` |
| Not fetched | Lean v4.33.1 / Mathlib `0df444a3…` caches (not shipped; see §4); `n11-supplement` (636 MB generator inputs + 680 receipts) — not needed, the emitted Lean is self-contained |

Repo files read via API (copies under `src/`): `assets/replay/n11-wip/HANDOFF.json`,
`PACKAGES.json`, `PROJECT_STATE.json`, `docs/FROZEN_REPLAY_ASSETS.md`, `Makefile`,
`tools/restore_frozen_assets.py`. Note: `make restore-n11-wip` points to the **core** release
tag, `restore-n11-supplement` to the **replay** tag.

## 2. WIP map (step 2; static, from `wip-analysis/graph.py` → `wip-analysis/wip-map.json`)

**Toolchain** `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474`.
Allowed axioms (HANDOFF): propext, Classical.choice, Quot.sound; no sorry / native_decide /
ofReduceBool / research axioms.

| | count |
|---|---|
| owned `.lean` files | 2,348 (2,066 under `N11Formalization/`) |
| import closure of current root `lean/N11Formalization.lean` (sha `f6e3419a…`) | 1,202 modules, ~57,955 theorem/lemma decls, 118 MB |
| closure of last ACCEPTED root A25 (`N11Formalization.lean.pre-c450pilot-20261014`, sha `4f470af5…`) | 1,134 modules |
| current − accepted | 68 modules = C450Source12/13 Data + 32 GroupedC + Segment each (pilot; **in verification, not paid**) |
| emitted but not root-imported | 782 modules (C450Source14..36 Data/GroupedC/Segment) |
| `sorry` in root closure (comments/strings stripped) | **0**; outside closure 1 (`Probe37.lean`, scratch) |
| `axiom` declarations / `native_decide` / `ofReduceBool` in closure | 0 / 0 / 0 |

Static counts are not a build. The HANDOFF itself says the current root was **not** rebuilt.

**Statement layer (paid, A25-accepted):** `Definitions.lean` (`Point`, `unitDisk`,
`Covers c r := ∀ x, ‖x‖≤1 → ∃ i, dist x (c i) ≤ r`, `feasibleRadii`), `Statement.lean`
(`N11MainStatement R := IsLeast feasibleRadii R ∧ sInf feasibleRadii = R`),
`Sharpening.lean` (`n11MainStatement_iff_two_bounds`), attainment of `sInf`.

**Root / upper bound (paid):** `SourceExactRoot.exists_unique`, `sourceRoot_mem`,
`sourceRadius_mem_box`, `sourceRadius_lt_threshold`, and
`source_attainment : Covers (centersOfRoot sourceRoot) sourceRadius` (C891 + C892).
`SourceExactRoot.main_of_lower_bound` reduces everything to the lower bound.

**Lower bound — two consumer routes, both with h450 and henergy explicit:**
1. `ActualMainRoute.lower_bound_of_remaining h450 henergy h33`.
2. `CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables h450 henergy (T : SevenFiniteTables)`.

**Paid vs pending (HANDOFF `accepted_credits`, A25 2026-10-13):**

| Obligation | Paid (by team) | Remaining | Lean name |
|---|---|---|---|
| C450 segments | 11/36 accepted; Source12,13 in root but **unaccepted**; Source14..36 emitted, team serial gate GREEN for keys k=13..22 (=Source14..23) per `evidence/c450-emit-20261014/batchv2-progress-*.txt` (that file also logs k=23 = Source24 GREEN at 20:11, but HANDOFF excludes the Source24 run from evidence) | 25 | `C450Source11Segment.RemainingSourceObligation` |
| Energy terminals (C921) | 310/2386 + all 120 sharp patches | 2076 (1687 candidate routes, 389 need genuine certificates) | `EnergyTerminalBatchB11.RemainingTerminalRadius` |
| Canonical33 / class exclusions (C923) | framework only | `Canonical33Obligation` (route 1) or all **7** Q0/Q1 class tables (route 2); 2 q1-balanced representative tables uninstantiated | `ActualMainRoute.Canonical33Obligation`, `SevenFiniteTables` |
| Nine-switch batch | 9 `start0_switchK_full_angle_upper` proved (7,923 node thms) | aggregation + `SwitchCertificate` bridge; 0 class credit | `SharedMomentConcreteSwitchBatch` |

**Our skeleton vs WIP (decision: adapt, don't compete).**
Our 12 sorry map onto WIP as: 1 `exists_optimal_cover` → paid (`exists_covers_sInf`);
2 `rD_eq_inf_coverRadius` → unnecessary; 3 `C891_exists_unique`, 4 `Rstar_enclosure` → paid
(`SourceExactRoot.exists_unique`, `sourceRadius_mem_box`); 5–8 (upper bound) → paid
(`source_attainment`); 9–12 (lower bound) → the WIP's h450 / henergy / h33 (+7 tables).
Our `rD`/`Rstar` duplicate `feasibleRadii`/`sourceRadius`. **Port of the 34 lean-core lemmas:
none ported.** They are index bookkeeping (faces, oracle edge lists, degree ledger) and
root-box bounds; the WIP already has root-box certificates (`RootBoxCert`) and its own
graph objects, and none of its named open Props is an index fact. Porting them would not
reduce any obligation, so I did not.

## 3. What this pass added (step 4) — all compiled unless marked DRAFT

Chosen obligation: **C450** (HANDOFF next_step #1), the only open item that is pure exact
rational arithmetic once the WIP's (accepted, Mathlib) soundness lemma
`C450GroupedPacketKernel.packet_bound`/`C450GroupedClosedAssembly.cell_of_packet` is taken
as given.

### 3a. Core-Lean C450 packet replay (`lean-core/DCPN11Core/C450Replay/`)
* `Kernel.lean` — core-`Rat` transcription of `RatInterval` ops, `minimumQ`, `clipUnit`,
  `p2Q/p3Q`, `range2Q/3Q`, `squareThird`, `amplitudeInterval`, `sinTQ/cosTQ` (14 terms),
  `sin/cosHiNLag` Lagrange remainders, `sineProductUpper`, `arcUpper`, `piLo`, `cap`,
  `packetUpper`; `ValidQ` = the 29 fields of WIP `Valid` verbatim over `Rat`;
  `validB` (Bool) with **`validB_sound : validB s p = true → ValidQ s p`** (proved);
  `chainB` (radial chain 31/50→69/50), `tileB` (Qcells tile [−1,1]), `cellB`, `segHeadB`
  (`nn0`, `nn1`, `eHi_le`), `TenSeg.beq`; `cellB_packet` (proved).
* `Split.lean` — `cellB_intro` (memory-bounded split check; needed for the 128-packet cell
  Source36 C31).
* `SegK/Data.lean`, `SegK/CellsJ.lean`, `SegK/All.lean` for K = 11..36 generated by
  `c450-replay/gen_lean.py` from the WIP files. Per segment, compiled for **K = 23..36**:
  `head_ok`, `listed_ok` (segment = independently transcribed `c450Segs[K−1]`),
  `cellNN_ok` for all 32 cells, `tiling_ok`, `count_ok`, and
  **`all_valid : ∀ c ∈ cells, ∀ p ∈ c.packets, ValidQ seg p ∧ p.Q = c.q`**.
* `Controls.lean` — `good_ok`; `badAmp_rejected` (p0 −1e−6), `badHi_rejected`
  (hi +1/100), `gapCell_rejected`, `tile_gap_rejected`: the checker does reject.
* `C450ReplayAudit.lean` — `#print axioms`: 61/61 = `[propext, Classical.choice, Quot.sound]`
  (`c450-replay/logs/axioms-audit.out`).
* Build: manual `lean -o` per module (script `c450-replay/build.sh`, oleans in RAM
  `$DCP_TMP/lc`, not persisted), append-only log `c450-replay/logs/build.jsonl`
  (117 rows, 109 rc=0; the 8 non-zero rows are a path bug before the first real build and
  SIGKILL/OOM of the oversized Source36 chunk, fixed by re-chunking; every module in the
  final set has an rc=0 row with its source sha256). `lake build` of the original
  `DCPN11Core` target was not re-run this pass (34 theorems unchanged).
* **Not compiled in Lean: K = 11..22** (only `Data` for 11..22 and nothing else). CPU was
  shared with other jobs (load ≈ 10 on 2 cores); I stopped after 23..36 because Source14..23
  already have team Lean gate receipts. K = 11 (accepted) would be the positive control.

### 3b. Python exact replay (`c450-replay/parse.py`, `replay.py`)
Fractions only. For K = 11..36: every packet's 29 `Valid` fields, packet-Q = Qcell,
leaf `(lo,hi)` = packet, radial chain, every `cell_join` node's interval, `bound` covers
[31/50,69/50], Qcell tiling, nvalid = #packets, `nn0/nn1`, `source_eq` vs `c450Segs`.
Result: **26/26 segments, 13,262 packets, 0 failures, 0 issues**
(`c450-replay/replay-py-results.json`). Smallest numeric slack `cap − packetUpper`:
5.7e−7 (Source36), 1.2e−6 (Source14), 1.5e−6 (Source35) — thin but positive.

### 3c. DRAFT, NOT COMPILED: `wip-additions/C450FullTelescope.lean`
`tail36` (vacuous `drop 36`) → `tail35` … `tail12` via each
`C450SourceKSegment.source{K−1}_remaining_of_remaining` → **`h450 :
C450Source11Segment.RemainingSourceObligation`** → `main_of_energy_and_33 henergy h33`.
Names were checked statically against all 25 Segment files (each consumes its own
`sourceK_paid`). The team's `evidence/c450-emit-20261014/verify_telescope.py` checks the
same shape. It pays nothing until Source12..36 build green in the root and pass the audit.

### 3d. Nine-switch arithmetic (`lean-core/DCPN11Core/SwitchArith.lean`, compiled)
`sum_eq_total`: the nine `start0_switchK_bound` sum to **exactly** `22523/250000`
(= `start0_switch_total_bound`). `leafControls_pattern`: only switches 0,1,2,3,6,7 are
≤ 1/2000; **switches 4 (51029/1e6), 5 (4839/2e5), 8 (14023/1e6) exceed the LeafControls
1/2000 bound**, so that "qualify 1/2000 vs 141/1e6" step cannot be done uniformly.
Arithmetic only; the aggregation/bridge theorem itself is still missing.

## 4. Build attempts (step 3)

* RAM 7.9 GB total; available fluctuated 1.2–6.3 GB (shared with other agents). No local
  disk (original sandbox): root fs was a RAM-backed overlay, the persistent workspace was JuiceFS FUSE. CPU arch is
  **aarch64**.
* Attempt 1: Lean v4.33.1 toolchain unpacked to RAM (2.1 GB trimmed). Wrong architecture
  (x86-64 asset), and available RAM fell to 1.4 GB. Deleted.
* Attempt 2 not made for Mathlib: toolchain (~2.1 GB) + Mathlib closure (~2–2.5 GB) + one
  elaborating Lean process (one 79-packet core-only check already peaked at 1.95 GB RSS)
  does not fit in what was left. Stopped per rule. WIP Mathlib build needs a normal machine
  (≥16 GB RAM, local disk, aarch64/x86 matching `lean-toolchain` v4.33.1).
* What works: a slim **core-only** v4.35.0 toolchain copied to `$DCP_TMP/slim` (use `C450_LEAN_TOOLCHAIN` now) (Init only,
  ~620 MB): about 0.36 s per small file, about 0.19 s CPU per packet check.

## 5. Remaining obligations, ranked (value ÷ effort, for the next agent or the team)

1. **C450 root integration (25 → 0).** On a Mathlib machine: serial-build Source14..36
   (team gate receipts cover Source14..23; our replay pre-validates the rational premises of
   Source23..36 and Python covers all), add `C450FullTelescope` (above), root-import,
   fresh root build, then audit and acceptance. Mechanical, high value.
2. **Nine-switch aggregation + `SwitchCertificate` bridge.** Designed and drafted (§7): per-switch maxima,
   no 1/2000 qualification; batch = rep7 (`q1Faces 7 4`) switches at index K−1. Needs the build-line gate.
3. **Instantiate the two q1-balanced representative tables, then the other six class
   tables** (`SevenFiniteTables`). Finite data plus existing consumers.
4. **Energy: 1687 candidate routes.** Generate certificates in the existing
   `Paid16General*`/`EnergyTerminalBatch*` pattern. A core-Lean pre-replay like §3a is
   possible if their premises are rational.
5. **Energy: 389 needing genuine certificates/refinement.** Real mathematics.
6. **`Canonical33Obligation` / `CanonicalNearest33Obligation`** (C923 geometry,
   alternative to item 3). Hardest; Voronoi/dual-graph topology.

## 6. Files (this pass)
* `wip/` — restored WIP sources (2,383 files, hash-verified); `wip-LEDGER.jsonl.gz`.
* `src/` — repo copies (HANDOFF.json, PACKAGES.json, PROJECT_STATE.json, FROZEN_REPLAY_ASSETS.md, Makefile, restore_frozen_assets.py).
* `wip-analysis/graph.py`, `wip-analysis/wip-map.json` — static import or sorry map.
* `c450-replay/` — `parse.py`, `replay.py`, `gen_lean.py`, `build.sh`, `drive.py`, `bg.sh`,
  `c450-parsed.json`, `replay-py-results.json`, `logs/` (build.jsonl, per-module .out, axioms-audit.out).
* `lean-core/DCPN11Core/C450Replay/` (Kernel, Split, Controls, Seg11..Seg36/*),
  `lean-core/DCPN11Core/SwitchArith.lean`, `lean-core/DCPN11Core/C450ReplayAudit.lean`.
* `wip-additions/C450FullTelescope.lean` — DRAFT, uncompiled, for the WIP tree.
* `lean/DCPN11/` — superseded first-pass skeleton (kept, frozen).

To rebuild the replay elsewhere, use core Lean v4.35.0 (or any 4.2x with `Rat` in core).
From `lean-core/`, compile `Kernel`, `Split`, `SegK/Data`, `SegK/CellsJ`, `SegK/All` in
import order with `lean -o`. Keep each chunk at 60 packets or fewer, or use about 2 GB RAM per process.

## 7. Build line, third pass (2026-10-15 13:27–14:05 CST): toolchain OK, Mathlib import does not fit

**Result: no WIP module compiled; h450 not paid; nothing new paid.**

What now exists (reusable):
* **Correct aarch64 Lean v4.33.1** (`lean-4.33.1-linux_aarch64.tar.zst`, commit 819816b2): hot part
  (bin, .so, `.olean`, `.olean.server`) in RAM at `$LEAN_TOOLCHAIN` (sandbox: lean-4.33.1-linux_aarch64) (675 MB);
  `.olean.private`, `.ir`, `.a`, libLLVM on JuiceFS `wip-build/tc-cold/` and symlinked back.
  Core-only control `import Lean` + `decide` + `#print axioms` (`$DCP_TMP/t1.lean`): OK, 2.1 s warm.
  (The class line is currently using this toolchain too.)
* **Exact Mathlib cache hashes** for rev 0df444a3, computed by `wip-build/hashes.lean` (a port of
  `Cache/Hashing.lean`, run with `lean --run`): 8,690 modules (Mathlib + Batteries, Aesop, Qq,
  ProofWidgets, Plausible, LeanSearchClient, ImportGraph, Cli), all found in
  `lakecache.blob.core.windows.net/mathlib4-master/f/<hash>.ltar` (`wip-build/mathlib-ltar-hashes.txt`,
  `mathlib-ltar-sizes.json`; 443.4 MB compressed). `lake exe cache get` was not needed.
* **Unpacked Mathlib import set on JuiceFS**: `wip-build/mlib/` (flat LEAN_PATH dir), `.olean` 1.883 GB,
  `.olean.private` 3.714 GB, `.olean.server` 0.105 GB, `.ir` 0.275 GB = **5.978 GB** (8,690 modules × 4 files;
  `.c`/`.ilean`/`.hash` dropped). Script `wip-build/fetch_mathlib.py` (resumable).
* `wip-build/plan.json`: topological build order: A25 closure 1,134 modules; pilot Source12/13 = 68;
  Source14..36 = 782. `wip-build/build.py`: resumable serial `lean -j1 -M 3500 -o` builder writing
  `wip-build/ledger.jsonl` (module, sha256, rc, seconds, peak RSS). Never run on a WIP module (see below).

Why it stops (two genuinely different attempts):
1. **Everything on the overlay**: `/` is tmpfs-backed (it counts as RAM shmem; `df` 6.3 GB, ~3.7 GB free).
   Every WIP closure module needs the **whole** Mathlib: 232 WIP files `import Mathlib`. Only 2 of the 1,134
   A25 modules avoid it, and those import `Mathlib.Tactic`, whose closure is also all 8,690 modules. WIP files are
   non-`module` files, so Lean opens `.olean`, `.olean.server` and `.olean.private` of every imported module.
   Bytes that must be mapped: Mathlib 5.98 GB + core 2.10 GB (olean 0.354, private 1.347, server 0.032,
   ir 0.371) = **≈8.1 GB**. That is more than the box's **7.9 GB total RAM**. MemAvailable during the run
   was 0.2–2.5 GB, because other agents' processes plus the 2.2 GB container-server are resident. No swap, no local disk.
2. **Mathlib on JuiceFS, mmapped through the page cache** (`wip-build/t2.lean` = `import Mathlib` + `norm_num`):
   functionally loads, but cold import progressed at only 2.5–5 modules/s (4,835 of 11,173 core+Mathlib
   modules mapped after 13.9 min; projected ≥40 min per cold process). The juicefs daemon RSS grew
   0.64 → 1.14 GB from the ~14.5k open mapped files (≈30 KB each; ~1 GB more expected at 33.5k).
   MemAvailable fell to **166 MB**, so I killed it to avoid OOM-ing other lines (`logs/import-mathlib-juicefs.mon`).
   Even if a warm import fitted, the h450 chain is ~1,990 separate Lean processes (A25 closure + 850 C450 modules),
   each re-importing Mathlib. The team needed 10–26 min per C450 segment on their machine. That is days here.

What would unblock: a machine with ≥16 GB RAM and a real local disk (≥10 GB free), aarch64 or x86-64.
There, run `lake exe cache get` (or reuse `mathlib-ltar-hashes.txt`) and then
`build.py all`, followed by `wip-additions/C450FullTelescope.lean` and `#print axioms`. Or cut the WIP's
`import Mathlib` down to minimal imports. That edits team sources, so it needs team acceptance, and the
closure is probably still >2,000 Mathlib modules.

## 8. Class line (class33/) — status 2026-10-15 (Asia/Shanghai)

**Nothing in this section is paid.** No Mathlib/WIP-toolchain build ran in this sandbox (the class line
does not own the Mathlib process; the build line's v4.33.1 toolchain was lost in a container restart at
~14:03 CST). Everything below is either (a) core-Lean **pre-validation** compiled with the v4.33.1 *core*
toolchain (Init only, no Mathlib), (b) exact-`Fraction` Python **pre-validation**, or (c) WIP-style Mathlib
**DRAFT** source (59 modules, 0 sorry) (uncompiled) for the build line to gate.

### 1. Route choice: route 2 (SevenFiniteTables), not route 1 (Canonical33Obligation)

* Route 1 `ActualMainRoute.Canonical33Obligation` quantifies over every representative cover and asks for a
  cyclic cut, a hub permutation and 11 witness points within `r` of all three face sites — i.e. the
  C923 nearest-site / clipped-Voronoi / dual-disk topology (§§1–6). No Mathlib support; months.
* Route 2 `CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables h450 henergy T`
  needs only finite rational data + interval trees: for each class a `CanonicalCoeffQ`, `kap`, `eta` and a
  `FiniteCanonicalCertificate` = balance + signs + 11 face trees + 9 switch trees + 9 sector trees + one
  strict rational total `< piLo`. With the proved 8→2 orbit transport
  (`CanonicalBalancedFiniteClassCertificate.SixAndBalancedFiniteTables`) the count is
  3 (Q0 m=1,2,3) + 3×8 (Q1 m=1,2,3, all cuts) + 2 (Q1 balanced representatives k=7,1) = **29 certificates**.
  Every remaining step is mechanical given proposals. **Route 2 chosen.**

### 2. Key finding: the A25 "refutation" of the concrete batches was a labelling error

The A25 lead record (C1804/C1806/C1811/C1812) tested `start0_face1`/`start0_switch*` against **`q0Faces 1` with
identity labels** and correctly found them incompatible — but those data are the historical **balanced-Q1
start0** proposal (`cover11/.../lead/shared_moment_dense_certificate_0_4.json`), whose labels are
ear (0,1,2), core [0,2,…,8]. Relabelling ring h ↦ h−1 (mod 9), hubs fixed:

* historical start0 ↦ Lean **`q1Faces 7 4`** and start2 ↦ **`q1Faces 1 4`** — exactly the two
  representatives of `BalancedTwoFiniteTables` (checked by recomputing `q1Faces` from the Lean definitions).
* All nine batch tuples are **exactly** `canonicalSwitch{P,Q,B,D2,D1}` of the instantiated rep7 table at
  Lean index **j = K−1 (mod 9)** (45 exact rational identities).
* `start0_face1_{p,q,b}` = canonical coefficients of rep7 face {1,8,9} with slots reversed
  (canonical slot s = data slot 2−s); the proved `start0_face1_full_domain_upper` therefore bounds that face
  via `SharedMomentFactorPermutation.face_upper_of_permuted_coefficients`.

So G1/G2 are closable and the 7,923 switch nodes + 1,239 Face1 nodes are **on** the critical path.

### 3. Nine-switch aggregation (G1) and bridge (G2)

* The "qualify 1/2000 vs 141/1e6" step is unnecessary: `canonicalTotalUpperQ` takes per-switch maxima
  additively. `rep7SwitchMax j := start0_switch{j+1 mod 9}_bound`; Σ = **22523/250000 exactly**
  (= `start0_switch_total_bound`). Switches K=4,5,8 simply contribute 51029/1e6, 4839/2e5, 14023/1e6.
  `SharedMomentConcreteLeafControls.start0_switch0_bound = 1/2000` is a different-namespace control (G4);
  the bridge never opens it.
* Structure bridge: `certificate_mono` + `switchCertificate_of_direct` (direct leaf ↦ `GradientSwitchLeaf`
  via `Or.inl (Or.inr (Or.inl h))`; root `switchCell 0 (1571/1000)` contains `switchRoot` since
  piHi/2 ≤ 1571/1000).
* Budget with these maxima (rep7): sharp constant −3.464894…, faces 3.440353 (hist uppers ↑1e-6),
  switches 0.090092, sectors 3.070858 → total 3.136409 < piLo, **slack 0.00518**.

### 4. Instantiated tables (pre-validated)

| table | Lean class | source | balance | graph | strict with proposed maxima |
|---|---|---|---|---|---|
| rep7 | `q1Faces 7 4` (balanced rep) | dense_certificate_0_4 (σ: h↦h−1) | ✓ | ✓ | slack 0.00518 |
| rep1 | `q1Faces 1 4` (balanced rep) | dense_certificate_2_4 (σ) | ✓ | ✓ | slack 0.00176 (tight) |
| q0m2 | `q0Faces 2` = `q0_degree4` (hub degrees 4,9) | q0_moment_dual_certificate_0_2 (identity, eta=0) | ✓ | ✓ | slack 0.163 |

All three: kap ≥ 0, eta ≥ 0, exact sharp constant computed; Python cross-check against the historical
generator formulas; core-Lean `Class33Core.{Rep7,Rep1,Q0M2}` + `Audit` compiled, **34/34 `#print axioms`
⊆ {propext, Classical.choice, Quot.sound}**, with negative controls (flipped mask unbalanced, wrong cut /
wrong m rejected, unshifted switch index mismatches, inflated maxima break strict).

### 5. Trees generated (exact leaf kernels transcribed from WIP, validated on Lean-green leaves)

Kernels: `py/switch_kernel.py` (switchDirectUpperQ) — positive control 3,966/3,966 SwitchBatch accept leaves
pass, tiling ✓, M−1e-3 rejects; `py/face_kernel.py` (planeDirectUpperQ, PlaneOutside, planeGradientUpperQ) —
80 direct + 21 outside + 519 gradient Face1 leaves all pass.

| item | trees | leaves | status |
|---|---|---|---|
| rep7 switches | 9 (A25 batch) | 3,966 | Lean-green (A25); bridge DRAFT |
| rep7 face {1,8,9} | A25 Face1 | 620 | Lean-green (A25); permutation bridge DRAFT |
| rep7 faces | 11 (M = hist+1e-4; {1,8,9} also = A25 Face1) | 10,349 | Python-exact |
| rep1 faces | 11 (M = hist+5e-5) | 11,585 | Python-exact |
| rep1 switches | 9 | 8,008 | Python-exact all; core-Lean S0,S1 compiled (S2.. pending) |
| q0m2 switches | 9 (M = hist+0.002) | 795 | Python-exact; core-Lean pending |
| q0m2 faces | 11 (M = hist+0.004, gradient leaves) | 4,867 | Python-exact |
| sectors (all tables) | 0 | — | **not started**: needs transcription of `MetricSectorLocalGradientCertificate.PositiveCertificate` + NodeBounds witnesses |

Actual budgets with the generated face/switch maxima (room left for the 9 sector maxima vs historical sector sum):
q0m2 room 1.425498 vs 1.324628 → **0.0112 per sector**; rep7 room 3.074942 vs 3.070853 → **4.5e-4 per sector**;
rep1 room 5.526456 vs 5.525418 → **1.15e-4 per sector** (tight). (data/*_budget_actual.json)

### 6. DRAFT Mathlib modules (class33/lean/N11Formalization/, uncompiled)

`Class33Labels` (canonicalLabel lemmas, A25 C1812 technique) · `Class33RepData` (rep7D/rep1D/q0m2D,
`*_balance` via `sum_slots` reindexing + ℤ `decide`, kap/eta signs) · `Class33SwitchBridge`
(certificate_mono, switchCertificate_of_direct, 9 batch SwitchCertificates, `rep7_switch_aggregate`,
45 identities, `rep7Switches`) · `Class33SwitchFields` + 18 `Class33SwitchTree{Rep1,Q0M2}S*` (batch-style trees)
· 33 `Class33FaceTree{Q0M2,Rep7,Rep1}F*` (Face1-style trees + `EfficientFaceCertificate`) ·
`Class33{Q0M2,Rep7,Rep1}Assembly` (`*Faces` fields; `q0m2_table_of_sectors : … → Q0FiniteTable 2`,
`rep7/rep1_table_of_sectors : … → RepresentativeFiniteTable 7/1`, i.e. each class reduced to 9 sector certificates + strict) · `Class33BalancedAssembly`
(`balanced_exclusion_of_two_canonical`, `rep7_certificate`, `rep7_face189_upper`).
No `sorry`. Expect compile iterations (simp/norm_num normal forms written without a compiler).

### 7. Inventory of the other classes (from historical docs; not verified)

* Q0 m=1 (3,10): historical DEGREE3-AREA-EXCLUSION (area argument, not shared-moment form) → needs a new
  canonical proposal (LP) before trees.
* Q0 m=3 (5,8): historical exclusion used C820 cyclic closure multipliers, which `FiniteCanonicalCertificate`
  cannot express → risk the canonical form is infeasible for this class; test by LP first.
* Q1 m=1 (3,9): area exclusion (DEGREE3); Q1 m=2: cluster-capacity + area (DEGREE4-TRIPLE, has eta);
  Q1 m=3 (5,7): shared-factor dual, starts 0–3 certified historically, start 7 by C815 — all need 8 cuts each
  in canonical form (no orbit reduction proved for m=1,2,3).

### 8. Next steps (class line)
1. Build line: gate the DRAFT modules (RepData → SwitchBridge → SwitchTrees/Fields → FaceTrees → Assemblies).
2. Transcribe the sector leaf (direct `sectorDirectUpperQ` with NodeBounds witnesses + gradient
   `PositiveCertificate`), validate on any Lean-green sector tree, generate q0m2 sectors (margin 0.011) →
   **first payable class `q0_degree4`**.
3. rep7 and rep1: 9 sectors each (margins 4.5e-4 and 1.15e-4 per sector); then `balanced_exclusion_of_two_canonical`/`BalancedTwoFiniteTables` pays q1_balanced.
4. Generate canonical LP proposals for Q0 m=1,3 and Q1 m=1,2,3 (24 cuts).

## 7. Energy line (n11-energy, 2026-10-15 CST) — PRE-VALIDATED ONLY, NOTHING PAID

Obligation `EnergyTerminalBatchB11.RemainingTerminalRadius`. All files under `energy/` (see `energy/README.md`, `energy/RESULTS.json`, `energy/classification.csv`).

* **Inventory.** 2506 terminals in `DBMSourceTreeData` = 2386 energy + 120 sharp; paid 310; remaining **2076** (matches HANDOFF). 274/310 paid use the uniform `Paid16CellCertificate` packet (G01..G12 = 252, Batch22 = 22); 36 are bespoke consumers. The "1687 candidate routes" are HOST proposals that are **not shipped** in n11-wip-0001 or in the `n11-supplement` release (that release is C450 logs/inputs only; FILES manifest sha256 e7fca1ae… verified). So I regenerated certificates in the Paid16 format: the same 16 paid fields and rounded weights, ≤7 DBM dual rows, and the exact strict T² check.
* **Exact replay** (`energy/checker.py`, Fraction transcription of `Paid16CellCertificate.Valid` and every helper): positive control **274/274** paid packets pass (min numeric margin 2.8e−6); **10/10** negative controls rejected (beta sum, beta<0, λ<0, rmin up, line intercept +1e−6, wrong arc shift, endpoint, wrong node, non-terminal node, zero dual).
* **Single-cell certificates** (`gen.py`: float LP in (β,λ,rmin) with damped tangent-point iteration, then rational rounding, rmin computed exactly, exact check): **1734/2076 pass** (min exact margin 1.1e−9). WIP-format Lean emitted: `energy/lean-wip/N11Formalization/Paid16GeneralH001..H083` (21 cases each, G03 template), `Paid16GeneralHAgg01..09`, `Paid16GeneralHAll`, `EnergyTerminalBatchB12` (`paidIDs` = B11 ∪ H, new explicit `RemainingTerminalRadius`, bridge `remaining11_of_remaining12`). The emitted text was re-parsed and re-checked: 1734/1734. **Not compiled** (no Mathlib here); B12 adds no paid credit until the build line compiles and audits it.
* **Core-Lean kernel sample** (`energy/lean-core/EnergyReplay/`, Lean 4.33.1 core, no Mathlib): `Kernel.lean` defines `ValidQ` as a field-for-field restatement over `Rat` and proves `validB_sound`. Compiled green: 2 paid G01 packets (positive), the **4 new packets with the smallest margins** (nodes 4670, 4931, 4038, 3453), and `Controls` (2 mutated packets evaluate to `false`). The bulk run (248 chunks, about 10 s and 0.9 GB per packet chunk) was stopped: two chunks were OOM-killed (rc −9) and the sandbox restarted. Axiom audit **not run** for these modules. The sandbox toolchain copy (now `$LEAN_TOOLCHAIN`) disappeared at the restart.
* **342 failures → refinement.** The long-iteration and Kelley upper bound (`refine.py`, 203 nodes, float) show **194/203 have no single-cell Paid16 certificate at all** (V_up < T²). `split.py` subdivides the cell by the `DBMTreeKernel.Valid` split rule at scale 4096·2⁸ (depth ≤ 12, ≤ 64 leaves) and checks each leaf packet exactly. Result: **57 nodes certified, 496 leaves**; **285 still open**. DRAFT Lean: `Paid16MatrixCellCertificate.lean` (explicit-matrix packet, generic copies of the rows/angles/dual lemmas, `node_radius_of_refinement` via `DBMTreeKernel.terminal_cover`), `EnergyRefineNxxxx` (57 modules), `EnergyRefineAgg01..06`, `EnergyRefineAll`, `EnergyTerminalBatchB13` (`remaining11_of_remaining13`). The generic proofs and `pk_ok` were written blind and will need repair at first compile.
* **Count if the build line compiles everything green:** energy remaining would drop from 2076 to **285** (1734 single-cell + 57 refined). The 285 open nodes sit at node ids ≥ 3000, mostly 3500–5010, near the sharp-patch region. Depth-12 leaves fail by 2e−8…1e−5 below T². This needs genuinely new mathematics (more paid fields, sharp-patch-style certificates, or another oracle), not more search.

---
# Appendix — first pass (2026-10-14), SUPERSEDED by §2

# n = 11 Lean 4 formalization — STATUS (first pass, 2026-10-14)

Target: `r_D(11) = R*` (C924), with `R*` = coordinate 6 of the unique C891 root
in the exact dyadic box (`math_data/n11/root_input.json`).
Nothing has been pushed to GitHub.

## Bottom line

| Layer | Location | Built? | sorry | Theorems |
|---|---|---|---|---|
| Core Lean (no Mathlib): finite combinatorics + exact box arithmetic | `lean-core/` | **Yes. `lake build` succeeds (5 jobs).** | 0 | 34 proved. 23 use no axioms; 11 use only `propext`. Log: `lean-core/axioms.log` |
| Mathlib: statement, skeleton, elementary lemmas | `lean/DCPN11/` | **No. Never compiled** (see "Why not compiled") | 12 | 66 stated; 54 have full proofs written as drafts that have not been machine-checked |

**The main theorem `DCP.N11.rD_eleven : rD 11 = Rstar` is stated and assembled, but it has
not been compiled.** Once it builds, `#print axioms` will list `sorryAx` until all 12
obligations below are discharged. This is a skeleton, not a proof.

## Why the Mathlib layer was not compiled (environment, not mathematics)

The sandbox had about 8 GB of RAM, shared by all agents. `/` and `$HOME` are RAM-backed. The only large
disk is a JuiceFS FUSE mount.
- Lean mmaps `.olean`, `.olean.private` and `.olean.server`. Doing that from JuiceFS stalls in
  page-fault waits. A cold `import Init` took about 60 s. A cold `import Lean` did not finish within
  110 s. Module-system files also read `.olean.private`, so those files cannot be left on FUSE.
- The core toolchain alone needs about 2.4 GB in RAM including privates. The Mathlib closure the
  statement needs (2274 modules, 1994 of them Mathlib) is roughly 2–2.5 GB more. Free memory
  moved between 1.1 and 4.6 GB. The container restarted twice during the attempt, which looks like
  memory pressure.
- An interrupted first `lake update` also left a half-linked `cache` executable. That was fixed;
  after it, `lake exe cache get` stalled on FUSE.
Following the "stop if a step loops more than twice" rule, I stopped the install attempts.

**To build on a normal machine** (16 GB or more of RAM, local disk): `cd lean && lake update &&
lake exe cache get && lake build`. Mathlib is pinned to tag `v4.35.0`, toolchain
`leanprover/lean4:v4.35.0`. Expect a few rounds of fixing the draft proofs: lemma names and
`simp` sets were written without a compiler.

## Files
- `lean/lakefile.toml`, `lean/lean-toolchain`, `lean/lake-manifest.json` (Mathlib v4.35.0, rev 56a00585…).
- `lean/DCPN11/Problem.lean`: `D`, `Covers`, `admissibleRadii`, `rD := sInf …`, `coverRadius`,
  and basic facts.
- `lean/DCPN11/Candidate.lean`: exact model (`halfAngle`, `theta`, `rho`, `ringSite`, hubs,
  `switchPt`, `pin`, `waist`), constraints `con`, `kkt` (12 equations, with `Df` as `fderiv`),
  `boxCenter`/`boxRad` as exact rationals, `InBox`, and
  `Rstar := sInf {R | ∃ p, InBox p ∧ kkt p = 0 ∧ p 6 = R}`. The definition does not depend on
  any `sorry`.
- `lean/DCPN11/Identities.lean`: the items in N11_CHECK_SCOPE.md.
- `lean/DCPN11/UpperBound.lean`: C892.
- `lean/DCPN11/LowerBound.lean`: C450, C923, C921, C922, the oracle, the simplex chart.
- `lean/DCPN11/Main.lean`: `rD_eleven`, followed by `#print axioms`.
- `lean-core/DCPN11Core/Combinatorics.lean`, `lean-core/DCPN11Core/RootBox.lean`: verified.
- `src/`: source files read from the repo through the GitHub API (read-only copies).

## Lemma map (source chain → Lean)

Key: ✅ machine-checked · 📝 draft proof, not compiled · ❌ `sorry`.

**Problem layer**
- 📝 `Covers.mono`, `Covers.nonneg`, `covers_one`, `rD_le`, `le_rD`, `rD_nonneg`, `rD_le_one`,
  `rD_antitone` (monotone in n), `rD_eq_of_bounds`.
- ❌ `exists_optimal_cover`: the infimum is attained. A compactness proof plan is written in the comment.
- ❌ `rD_eq_inf_coverRadius`: equivalence with the max-min formulation.

**Candidate / C891 / C922**
- ❌ `C891_exists_unique` (Krawczyk existence and uniqueness in the box).
- 📝 `Rstar_spec`, `box_R_bounds`, `Rstar_lt_19_50` (the coarse part of C922), `Rstar_pos`.
- ❌ `Rstar_enclosure` (the 30-digit enclosure; needs the refined Krawczyk boxes).
- ✅ `RootBox.*`: exact facts on the box, all checked with integers over 2^82:
  - R ∈ (0.379983852, 0.379983855) and R < 19/50;
  - a0..a3 > 0 and each < 0.39;
  - 1.376 < Σa < 1.57 (so a4 ∈ (0, 0.4) once π bounds are added);
  - hubs interior; y1 < 0 < y0; waist branch d < R;
  - multiplier signs;
  - the hex strings are re-derived from their digits.

**Identities (N11_CHECK_SCOPE.md items 1–4)**: all 📝, with no sorry.
- `rho_identity` (ρ² − 2ρ cos a + 1 = R²);
- `sq_dist_site_switch` / `'`; `theta_switch`, `theta_switch_wrap`, `halfAngle_sum`
  (arcs tile, Σa = π); `dist_site_switch`, `dist_next_site_switch`;
- `pin_sub_site`, `pin_dist_sites` (U_k = C_k + C_{k+1} − B_k is at distance R from both sites);
- `conj_ringSite`, `conj_switchPt`, `conj_pin` (x-axis reflection);
- `waist_dist_hub0/1`; `con_zero_iff`; `reflected_fan`; `mirror_waist`.
- ✅ The index bookkeeping behind these is machine-checked:
  - `reflPin_matches_reflSite`;
  - `activeFan_edges` (seven fan faces with edges 1, 2, 3, 4, 5, 6, 8);
  - `activeFan_are_faces`, `central_faces`, `slack_faces`, `face_partition`.

**C892 upper bound**
- ❌ `legal_of_box` (interval trigonometry).
- ❌ `boundary_covered` (arc tiling; elementary).
- ❌ `voronoi_critical_point` (a general lemma).
- ❌ `delaunay_certificate` (interval geometry).
- 📝 `root_covers` and `upper_bound` (assembly).
- ✅ Face incidence: `faces_length`, `distinctEdges_length` (21), `face_incidence` (hull edges ×1,
  interior edges ×2), `hull_edges_present`, `euler_disk`.

**Lower bound**
- 📝 `eight_arcsin_R0_lt_pi`, `D0_pos`, `boundary_disk_misses_origin`, `not_all_boundary`,
  `exactly_nine_boundary` (assembly).
- ❌ `at_least_nine_boundary` (arc-width bound).
- ❌ `C450_no_ten_boundary`.
- ❌ `C923_reduction` (§§1–6; the internal objects such as owned arcs, clipped cells, the dual
  disk and ears do not have Lean definitions yet).
- ❌ `C921_oracle_lower`.
- 📝 `lower_bound` (assembly).
- ✅ Combinatorial pieces of §§4–6:
  - `clique_consecutive` (every pairwise-local 3-clique in C9 is a consecutive triple);
  - `degreePairs_eq` (the complete degree ledger);
  - `only_q0_6_7_survives`;
  - `oracle_counts` (18 + 33 = 51 distinct edges);
  - `oracle_edges_literal` (identical to the checker's `oracle_edges()`);
  - `hub_degrees` (6 + 7 = 13);
  - `raw_to_canonical` and `missing_canonical_fans` (EXACT-ORACLE-INDEX-MAP: only fans 5 and 7 are absent).

**Main**: 📝 `rD_eleven` = `rD_eq_of_bounds` applied to `upper_bound` and `lower_bound`.

## Sorry count: 12 (Mathlib layer) + 0 (core layer)
1. `exists_optimal_cover`
2. `rD_eq_inf_coverRadius`
3. `C891_exists_unique`
4. `Rstar_enclosure`
5. `legal_of_box`
6. `boundary_covered`
7. `voronoi_critical_point`
8. `delaunay_certificate`
9. `at_least_nine_boundary`
10. `C450_no_ten_boundary`
11. `C923_reduction`
12. `C921_oracle_lower`

Items 1, 2 and 4 are not used by `rD_eleven`. The main theorem depends on items 3 and 5–12.

## What remains, honestly estimated
- **Easy to medium analysis, days to weeks**: items 1, 2, 6, 9; fixing the drafts once they compile;
  item 7 (a general nearest-site critical-point lemma, using convexity and a first-order argument).
- **Certified computation, medium**:
  - Items 3 and 5: Krawczyk on a 12×12 system with trig and sqrt.
  - Item 8: about 600 interval sign tests.
  - Item 4.
  - Route: a verified interval-arithmetic library in Lean. Rational endpoints, with sin/cos/sqrt
    through Taylor bounds that carry an explicit remainder (Mathlib has `Real.sin_bound` and
    `cos_bound`), run by `decide`/`norm_num` via proof by reflection over a certified checker. The
    alternative is to import the Python checker's interval certificates as data and verify them
    with a reflective Lean checker.
- **Large certified computation (the hard core)**:
  - Item 10, C450: 36 eccentricity intervals, about 198k kernel boxes.
  - Item 12, C921: 2505 DBM splits, 2386 energy leaves using 371 exact Schur fields with
    13,356 rational weights, and 120 local stress-ball leaves using full Taylor remainders.
  - The §5 metric exclusions inside item 11: area and moment certificates for 6 graph classes.
  - Realistic only as: (a) export every certificate as data; (b) write a small Lean checker,
    `def check : Cert → Bool`, with a soundness theorem; (c) run it by kernel reduction or
    `native_decide`. `native_decide` adds a trusted-compiler axiom; say so if it is used.
    Exact Schur fields can be checked in pure integer arithmetic, which Lean's GMP-accelerated
    kernel handles well.
- **The hardest mathematics to formalize (item 11, C923 §§1–6)**:
  - nearest-site ownership on S¹;
  - clipped Voronoi cells and their convexity;
  - existence of an embedded straight dual disk built from Delaunay polygons;
  - ear and fan topology.
  - None of this exists in Mathlib. Planar Voronoi/Delaunay theory would have to be built
    first, so expect months.

Overall estimate: about 5–10% of the full formal proof is done if the drafts compile. Every
large-computation and topology obligation is still open.


## Loop update 2026-10-15 14:44 CST (看护轮, class line)
Core-Lean (v4.33.1 Init-only) replay of all remaining switch trees compiled: Rep1S2..S8 + Q0M2S0..S8, 6,944 leaves, 110 modules rc=0, axiom audit 172/172 std (class33/logs/axioms-swtrees.out). Rep1 and Q0M2 switch trees now fully core-Lean replayed. **Pre-validation, not credit**; nothing Paid (Mathlib still unbuildable here).

## 9. Build line moved to GitHub Actions (2026-10-15 16:06– CST)

* Repo/branch: `Liyang1145/DiskCoveringProofs` @ `ci/n11-build` (base main `294f644`), all content under `ci-n11/`
  + `.github/workflows/n11-{main,energy,class,chunk}.yml`. (A new repo `dcp-n11-build` was the first plan; Hark's
  GitHub app has no repo-creation permission → 403; the user approved the branch instead.)
* `ci-n11/lean` = team WIP unmodified; drafts copied in by CI as added files. Toolchain v4.33.1 x86_64, Mathlib cache
  via `lake exe cache get` (8,690 files, OK in ~1 min).
* Runner: ubuntu-latest, 4 vCPU, 16 GB RAM (+12 GB swap we add), 105 GB free disk after cleanup.
* Run 1 (commit 8301bb9, `lake build`): class runner died at 17:06 ("runner has received a shutdown signal",
  memory exhaustion with 4 parallel Lean processes incl. `Ladder49_jt_kkt_z`); main/energy cancelled by us.
  Main had built 295 A25 modules in 50 min with 0 failures (lake log in ci/artifacts/38704871877).
* Run 2 (commit 92c4015): `tools/sched.py` — memory-aware scheduler, `lean -o` per module, stamps
  (sha of source + imports) for resume, kill-youngest + solo requeue under memory pressure, failure stamps.
  Heavy modules seen: `Ladder49_jt_kkt_z` (~40 min, RSS ~10 GB incl. mmapped Mathlib; olean ~1.16 GB per team notes),
  `DBMSourceTreeData` (~25 min), `FlashCosineLeaf284Bridge` (~20 min), `Leaf4348Bridge` (~11 min),
  `G3Batch_*` (3–6 min each).
* Results/credit: see §9 status lines below and `ci/ledger.jsonl`. Paid requires CI-green + clean axiom audit.
* Snapshot 2026-10-15 19:01 CST (run 2, chunk 1 still running; from commit statuses, no audit yet):
  main 581/1985 (A25 closure in progress), energy 487/659 (WIP deps done; draft Paid16GeneralH001..~H024 green so far),
  class 777/1115; **0 failed modules** in any track. Nothing paid yet (audit runs at chunk end).
  Team workflows (Delivery bytes, Scoped math replay) also ran on the branch: success.


## Loop update 2026-10-16 21:00 CST (看护轮, class line)
CI: class run 38874253879 c3 in progress (333 face/switch modules ok, SwitchBridge failed from a bad `local notation` — fixed locally, push pending). Local: sector kernel transcribed (class33/sector/kernel.py, exact); q0m2 all 9 sector trees generated (~47k leaves, Python exact, pre-validation); core-Lean replay in progress (class33/lean-core/Class33Core/SectorKernel.lean + SecTrees); reflective Mathlib checker drafted (Class33SectorReflect). Nothing Paid.
