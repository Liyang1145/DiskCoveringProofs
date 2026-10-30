EXPERT (2026-10-30, superseded by session 54):
- CI now reaches `EndpointChecks`; it is the sole real blocker, while all later lane-A exits are dependency-only.
- Split it now: `EndpointChecksTaylor` (generic Taylor/monotonicity), `EndpointChecksBins` (eight scalar bin lemmas), then assembly.
- First theorem: `sinT4_eq_quartic (a : ℝ) : sinT 4 a = a - a^3/6 + a^5/120 - a^7/5040`; use `simp [sinT, Finset.sum_range_succ]` then `ring_nf`.
- Replace repeated `![...] j` lookups with scalar `endpointU0..7 : ℚ`; close rational branches by `simp only [endpointUj, sinPoly4]; norm_num`.
- For `hj.val < 5` false branches use `norm_num at hj` before `omega`; do not leave bare `omega` after `fin_cases`.
- Build in order: EndpointChecks -> UpperReductionUnimodal -> both suffix modules -> EdgeShape; then prove `SectorValid` and instantiate `Q0Degree3AreaInput`.
- `edgeValid` or 42 drafted facts alone are not a class exclusion; `SevenClassExclusions` remains 0/7.

# Lane A notes

## Ledger

- C450 is closed at `495c970c`, CI-green, and transitively imported through
  `EnergyTerminalBatchB12Main`; stale `HARK-MISSING` comments are not a gap.
- Cos and Mono were CI-green at `e5875cf8`.
- Bins is **CI-green**: run `41082175973` exit 0. Its repaired API form is
  `Nat.mod_lt k.val (by norm_num : 0 < 256)`; no source change pending.
- EndpointChecks restricts lower Taylor premises to bins 0--4 and handles bins
  5--7 separately. Exact endpoint audit passed 8/8; minimum slack was
  `6.6940497252e-7` (bin 7).
- The full target chain, including 42 shape facts and `edgeValid`, is
  **CI-green** in run `41098508743` / job `124210423249` at `1b2fa7a8`.
- `SectorValid`, the strict total assembly, and `Q0Degree3AreaInput` remain
  unpaid. Seven-class exclusions are 0/7; no class theorem is claimed.

## 2026-10-30 (sessions 24--53, condensed)

The C450 chain, Cos/Mono/Bins, EndpointChecks, 21 peak checks, both edge
suffixes, and all 42 edge-shape facts were repaired in stages. Old CI reds
isolated these concrete API issues: `Nat.mod_lt` arguments, opaque `sinT 4`,
an incompatible composite derivative, `decide`-based rational table facts,
`norm_num` before `omega`, and `![...] j` index leaves. The repaired
EndpointChecks scalarizes endpoint values, uses an explicit polynomial
derivative, and rewrites table entries before `norm_num`. The C450 audit uses
`C450Source36Data.source36` and proves that source-36 is a member of the
nonempty `drop 11` tail consumed by `h450`.

## 2026-10-30 (session 54) -- lane chain kernel-green; next obligations isolated

**Did.** Read the live GitHub Actions run `41098508743` at merge commit
`1b2fa7a8`. Job `124210423249` completed **success** (17:24:14Z--18:10:59Z),
so every target in `TARGETS.txt` and the final root target built exit 0. This
is a kernel verdict, not a sample or receipt audit. The primary log's early
target exits are all 0; the job-level conclusion covers the remaining serial
targets. Current `HEAD` has no changes to the tested lane-A files.

**Files / SHA256 (all at tested bytes).**
`SevenClassQ0Deg3EndpointChecks.lean`
`c17381d16a30605b1335c9869cc498aafafec29e4173e73e254071e201fdc5fc`;
`SevenClassQ0Deg3EdgeShape.lean`
`fb48cf172b955c46aab2a969f2f29ee670da4456ff73f17620512da5a99260de`;
`C450ChainCompletionAudit.lean`
`21abc9089fbe611c26e4b5b59eeeea6253eb88287f4ac338f167d18dafcb3dfd`;
`C450ChainCompletionMain.lean`
`3f6088615e0a88e2a8927562c947c0c685e3e57bb15376ca3467fc7f6a33539c`.
`TARGETS.txt` received only a status-comment update.

**Checks (scope).** Exact-rational `audit_endpoint_low_denom.py`: 8/8 PASS,
minimum slack `6.6940497252e-7` (bin 7). `verify_q0_degree3_cos.py`: PASS on
all 2048 adjacent grid steps. `audit_q0_degree3_edge_unimodal.py`: PASS for
all 21 edges, with witnesses and maxima matching. New
`audit_q0_degree3_sector_grid.py` recomputes 21 edge maxima, all `9 x 2049`
sector values, and `totalUpper`; it also checks all 2049 node inequalities, reproduces the JSON exactly, with strict
slack `0.012092890370999008`. Sector witnesses are `1024,1024` then seven at
`1536`, suggesting a split at `pi/2` and `3*pi/4`. The seven-class inventory
audit passes on source data only. `git diff --check` passes. These arithmetic
audits are evidence, not substitutes for the cited Lean run.

**New audit files.** `audit_q0_degree3_sector_grid.py`
`7a90af9106664d85aa7ea7fe4b7fe11112af71cfa3880d5541aad30c2b567b9e`;
`q0-degree3-sector-grid-audit.json`
`bc0dd05c4dd7a38f08ae98d916a1eff5bbe8b7db98bdd53749278049215669b9`.

**Still unproved / unpaid.** `SectorValid` for the nine sector rows; the strict
`totalUpper < piLo` assembly; construction of `Q0Degree3AreaInput` for every
actual q0(3,10) refinement; and all seven `SevenClassExclusions` fields remain
unpaid. The 29 canonical finite tables are not emitted or connected to Lean.
The arbitrary-centre full-disk theorem remains unproved.

**Next concrete step.** Build `SevenClassQ0Deg3SectorUnimodal`: prove the
first two sector rows are nondecreasing to node 1024 (their only positive
multipliers), the remaining seven are nondecreasing to node 1536, and prove the
post-witness decreasing halves from `R2*cosHi/2 - mu`; then add the nine exact
peak checks and target `SectorValid` only after the module is written.

## 2026-10-30 (session 55) -- sector peaks and unimodal reducer drafted

**Did.** Added `SevenClassQ0Deg3SectorPeak.lean`, generated deterministically by
`emit_q0_degree3_sector_peak.py`. It copies the nine audited sector maxima into
`sectorPeakAt`, records witnesses `1024,1024,1536,...`, states exact separate
`sectorPeakValid_0..8` checks, and proves
`sectorValid_of_unimodal : SectorUnimodal -> (all peaks) -> SectorValid`.
Thus `SectorValid` now has only the two visible analytic shape halves plus nine
kernel-checkable exact peak comparisons; no all-grid scan is assumed.

**Files / SHA256.**
`emit_q0_degree3_sector_peak.py`
`76ba30d9e7a284bf9290af2acbaf1ccfccfd5d57b1ff2e22dc0edbf02504c1b0`;
`SevenClassQ0Deg3SectorPeak.lean`
`41c1b72dc544a6274b18f4c177896994e62ca3461c4eccaf6f86aa2dae4bb543`.

**Checks (scope).** Emitter self-checks the report's nine site rows, witness
pattern, and exact maxima. `python3 -m py_compile` passes on the emitter;
regeneration is deterministic at the recorded Lean hash; `git diff --check`
passes. Lean compilation is **CI pending** (no project oleans locally).

**Still unproved.** `SectorIncTo`/`SectorDecFrom` for all nine rows, the nine
peak-check builds, strict total assembly, `Q0Degree3AreaInput` construction, and
all seven class exclusions. The peak module alone does not prove `SectorValid`.

**Next concrete step.** Prove `SectorDecFrom` from the source suggestion: split
at the last bin and derive the suffix sign from `R2*cosHi/2 - mu`; independently
prove the shared node-segment increment is nonnegative on adjacent bins.

## 2026-10-30 (session 56) -- sector adjacent-step reduction

**Did.** Added `SevenClassQ0Deg3SectorShape.lean`, importing the session-55
peak module. It proves the exact bridge
`2*sectorUpper mu lam q a = edgeUpper (2*mu) q + (2*a - sinLoNLag (2*a)) + 4*lam*a`,
defines `SectorIncSteps`/`SectorDecSteps` as adjacent steps on the correct side
of each witness, proves generic finite prefix/suffix chain lemmas by
`Nat.le_induction`, and derives `SectorUnimodal` from
`SectorAdjacentUnimodal`. Endpoint truncation at grid index 2048 is explicit.
Added the module to `TARGETS.txt`.

**Files / SHA256.** `SevenClassQ0Deg3SectorShape.lean`
`90b7e764326eb056430ed99ee6a3567e13a8eb76f504b888b891ddc8958ad7dd`;
session-55 `SevenClassQ0Deg3SectorPeak.lean` remains
`41c1b72dc544a6274b18f4c177896994e62ca3461c4eccaf6f86aa2dae4bb543`.

**Checks (scope).** `git diff --check` PASS; `py_compile` of both sector scripts
PASS; forbidden-token scan found only `#print axioms` audit commands. Lean
kernel status for both sector modules is **CI pending**; no local project build
was attempted on the 2-core worker.

**Still unproved / unpaid.** `SectorAdjacentUnimodal` itself (all adjacent
steps), hence `SectorUnimodal`, `SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven class exclusions. The bridge and chain
reduction are reductions, not a proof of the sector inequalities.

**Next concrete step.** Prove the within-bin adjacent increment from the
bridge/derivative sign `(19/50)^2*cosHi(q)/2 - mu_i`; handle the eight
node-bin jumps as separate exact rational steps, then emit one peak module that
instantiates `SectorAdjacentUnimodal`.

## 2026-10-30 (sessions 57--59, condensed) -- sector calculus and cast adapters

`SevenClassQ0Deg3SectorCalculus.lean` now defines `sectorHiReal`, proves its
derivative `(19/50)^2*cosHiReal x/2 - mu`, and gives interval monotonicity
wrappers from derivative sign. `sectorUpper_cast_eq` and
`sectorValue_cast_eq_sectorHiReal` bridge the rational table to that real
bracket. `sectorValue_le_of_monotoneOn` and `..._of_antitoneOn` turn real
fixed-bin shape, interval membership, and equal `nodeBin` endpoints into
rational adjacent comparisons. No local project build was run; these are
**CI pending**, not kernel-green.

## 2026-10-30 (session 60) -- cosine-threshold adjacent-step adapters

**Did.** Extended the same module with `sectorValue_le_of_cos_ge` and
`sectorValue_le_of_cos_le`. These compose the cast/monotonicity adapters with
the exact derivative threshold `2*mu/A^2`, proving an increasing/decreasing
adjacent sector comparison directly from a pointwise lower/upper cosine bound.
Node-bin equality and interval membership remain explicit hypotheses; no
boundary jump is hidden in the derivative step.

**File / SHA256.** `SevenClassQ0Deg3SectorCalculus.lean`
`73c1c94aa4871a63c976f7a9ead0f9b2add9058abc95ae50e051d1d56f78de70`.
Already target-listed; no target-list change.

**Checks (scope).** `git diff --check` PASS. No local project build was run on
the 2-core worker. Lean kernel status of the new adapters is **CI pending**.

**Still unproved / unpaid.** Per-bin cosine bounds on all nine rows, all eight
node-bin jumps, `SectorAdjacentUnimodal`, `SectorUnimodal`, `SectorValid`,
strict total assembly, `Q0Degree3AreaInput`, and all seven class exclusions.

**Next concrete step.** Compute exact rational cosine crossing bins for the
nine `mu (nextSite i)` thresholds, then apply these two adapters within each
bin and prove the eight boundary comparisons separately with `norm_num`.
