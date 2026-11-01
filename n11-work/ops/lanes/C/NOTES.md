# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits, static scans, and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Preserve green `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapWideFieldWitnesses` unchanged.
- `ExcludedTree` is not a bridge to `RemainingTerminalRadius`. Public exclusion
  tree results are conditional on packet `f0Lo`/`g` and pay no residual id.
- Scan forbidden tokens without relying on `\b` under POSIX `rg`.

## Condensed history

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  `{1409,2337,2341,2356,2360,2368,2370}` have public tree payloads; the other
  382 payloads are absent. Row caps exclude those seven for any row count, so
  wider LP work cannot rescue them. Five-field payloads for 2356/2370 remain
  conditional. No residual id is paid.
- CI `41201323694` is green for `RefineFourteen` (`paid_count = 2011`) and
  `RefineFourteenMain`. `41217409382` is green for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`, leaving a
  373-id conditional residual. Those interfaces are equivalences, not payments.
- Earlier census failures were proof-encoding failures, not false ids. A
  one-goal 373-literal `decide +kernel` and 100-id `decide +kernel` blocks both
  exceeded kernel recursion/heartbeat limits. Part 219 split cardinality
  structurally and used four literal chunks.
- Missing throughout: radius certificates for the 373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit or byte check is kernel credit.

## 2026-10-31 to 2026-11-01 - parts 202-234 (condensed)

Repaired residual modules and censuses were CI-green, but literal census aliases
and the structural 54-line variant remain **CI pending** and pay no id. Exact
inventory: 773 files / 53,178,301 bytes, seven known payload ids, 382 missing
(missing-set SHA256 `f09a5bc4...5e90`); the C450 archive has no packet schema.
`PaidCellCertificateMCap` fixes the mixture through `hf0`/`hg`, not all `beta`.
After repairing the `sum beta = 1` row and omitted `endpoint_lo(g)` factors, the
seven public ids' best float regions have exact-negative vertex gaps (closest
2356, `-7.388363184123934e-07`); this is region-local arithmetic, not payment.
Checks were exit 0 with exact rechecks, `py_compile`, token scans, and
`git diff --check`. No host-storage/kernel credit or residual id is claimed.

## 2026-11-01 - part 235 (exact vertices for remaining six public ids)

Added `audit_beta_lp_exact_sweep.py` and ran one best-sign-region LP sweep plus
exact Fraction Gauss-Jordan/recheck for each remaining public record. All six
mask-selected active sets have rank 107, no free columns, exact reduced rows,
and exact-negative gaps: 1409 mask 15 `-3.121634442889577e-05`; 2337 mask 114
`-1.0365427694943543e-05`; 2341 mask 55 `-2.678143522094676e-05`; 2360 mask
247 `-1.7193773513727577e-05`; 2368 mask 98 `-4.965940403282977e-05`; 2370
mask 99 `-3.7366048306710155e-05`. With corrected 2356 this is 7/7 exact
negative at each id's best float sign region; no id is paid. This does not prove
infeasibility over all 512 regions. Files: `audit_beta_lp_exact_sweep.py`
SHA256 `c24bc4190302d488790878de77b78f5269b56a6625e9590768948777edb85536`;
`beta-lp-exact-sweep.json` SHA256
`b25b5f3e0c8d18731f8d10e5851bcd15fcc546ed7dd95201c172219b44b6da61`. Checks:
`py_compile` exit 0; full 512 masks/id and exact rechecks exit 0 (175 s); scans
and `git diff --check` clean. No Lean module/TARGET added.
Still unproved: 373 radius packets, 382 absent payloads, SevenClassExclusions
(0/7), arbitrary-centre theorem. Next: derive a region-independent exact
duality/Farkas certificate, or use the exact evaluator to test all masks for
one representative id rather than treating one negative region as decisive.

Condensed: `audit_beta_lp_all_regions.py` checked all 512 regions of 2356 and
`merge_beta_lp_region_reports.py` combined them: 448 exact-negative vertices,
64 float-infeasible, zero PASS. See `beta-lp-all-regions-combined.json`.

## 2026-11-01 - parts 238-241 (2356 threshold coverage, condensed)

Established the exact normalized-Farkas pattern and independent replay. The
generator appends `lower >= T2`, chooses an L1-vertex support by pivoted QR,
solves exactly over Q (FLINT fast path plus pure-Python fallback), and rechecks
signs/residuals/normalization. `verify_beta_lp_threshold_reports.py`
reconstructs rows from proposal/DBM and checks hashes, threshold, every
multiplier, 107 zero-residual columns, normalization, mask ordering, and
completeness without calling the constructor.

Id 2356: 512/512 `exact-l1-normalized-Farkas`; report SHA256
`E4EFBB9B...E46BA8A5`; independent replay passed, verification SHA256
`A071B85B...CF8F4D`. This proves only region-local LP infeasibility, **not
kernel credit, payment of id 2356, or the arbitrary-centre theorem**.

## 2026-11-01 - part 242 (checkpointed audit; full 1409 coverage)

Added atomic `--checkpoint-every` and exact `--resume` handling to
`audit_beta_lp_threshold_farkas.py`. A checkpoint validates the proposal hash,
id, and threshold before merging, skips already checked masks, preserves sorted
order, and replaces the report via a temporary file. Resume replay on the final
report skipped masks 0/1 and left its SHA256 byte-identical.

Completed and independently replayed all 512 sign regions for public id 1409:
every record is `exact-l1-normalized-Farkas`. Generator exit 0 in 133 s;
verifier exit 0 in 54 s with `--require-complete`. Report
`beta-lp-threshold-all-1409.json` SHA256
`D4DC22D79DF9EC555AE4243C746AAC59123B4E18309D0F11791AA8B563D902F7`;
verification `beta-lp-threshold-verification-1409.json` SHA256
`D6FC3DB0639D74DC1DAC884CE9BED1F811C4C7595BA932DBF6967409ECDE2037`.
Audit script SHA256 `F0A47F5AC6FD623FEBFDD5D1DCF0B4E93E1E092E8A4858F554900833ABAFFB3D`;
unchanged verifier SHA256 `09C653ED...9386DD`.

Checks: `py_compile` exit 0 for both scripts; resume/checkpoint test exit 0;
forbidden-token scan clean for the Python files; `git diff --check` clean.
Scope: exact region-local LP certificates for two ids (2356 and 1409), **not
kernel credit, payment, or a global infeasibility theorem**. Still unproved:
threshold coverage for five public ids, 373 radius packets, 382 absent
payloads, SevenClassExclusions (0/7), arbitrary-centre theorem. No Lean module
or TARGET was added.

Next concrete step: run the identical checkpointed 2337 sweep (observed cost
about 133 s generation plus 54 s replay), then replay with
`--require-complete` and record both SHA256 values.

## 2026-11-01 - part 243 (complete threshold coverage for three more ids)

Installed the missing local wheels (`numpy`, `scipy`, `python-flint`) after the
documented commands failed with `ModuleNotFoundError`. Ran the unchanged
checkpointed generator and independent verifier over all 512 sign regions for
ids 2337, 2341, and 2360. Every generated record is
`exact-l1-normalized-Farkas`; each `--require-complete` replay reports
`all-512-exact-rechecks-pass`, `complete: true`, masks `0..511`.

- 2337: generator `beta-lp-threshold-all-2337.json` (26,401,875 bytes) SHA256
  `D12DB47EC73D0907C5966C40600EE2CEAE8CF102F5978BE83E8CF47F169AD504`;
  verification `beta-lp-threshold-verification-2337.json` SHA256
  `5B5A1100D2E8ADEBDEF06AEF7936D62AA9F2029CBCC79FD97F4E4A399C2563EB`.
- 2341: generator `beta-lp-threshold-all-2341.json` (27,321,049 bytes) SHA256
  `60AE37A1296BA2370256FCDFB25D7F6C592CD74CA864640B3D6D4B195D2056EE`;
  verification `beta-lp-threshold-verification-2341.json` SHA256
  `41CC8531103E6A940F10A4D48E0917CD085CF6CF2B544F6C725BFF7FAC76BDD6`.
- 2360: generator `beta-lp-threshold-all-2360.json` (20,131,673 bytes) SHA256
  `2A4C37E49AE30DF26D5D6FB37F62B7F8A0BA135AE87710384134343D8F1B2D99`;
  verification `beta-lp-threshold-verification-2360.json` SHA256
  `A987420D5A27CAD96EAB67C70F364CE75CE7731B0747C51544589C2B0C39EAA0`.

Generator and verifier are unchanged: SHA256 `F0A47F5A...ABAFFB3D` and
`09C653ED...9386DD`. Checks: all three generation runs exited 0; all three
independent complete replays exited 0; `py_compile`, forbidden-token scan, and
`git diff --check` were clean. With prior reports, threshold-region coverage is
now 5/7 public ids (1409, 2337, 2341, 2356, 2360), all independently replayed.
Scope remains exact region-local LP infeasibility only: **not kernel credit,
residual payment, global infeasibility, or the arbitrary-centre theorem**.
Still unproved: ids 2368/2370 threshold coverage; all 373 radius packets; 382
absent payloads; SevenClassExclusions (0/7); arbitrary-centre theorem. No Lean
module/TARGET added.

Next concrete step: run the identical generator + complete replay for 2368,
then 2370, and hash both pairs. Do not describe 7/7 as a global theorem.

## 2026-11-01 - part 244 (complete 7/7 public-id threshold coverage)

Restored the missing session-local NumPy/SciPy/python-flint wheels, then ran the
unchanged checkpointed generator for the final two public ids. Each full report
has 512/512 records with status `exact-l1-normalized-Farkas`, masks exactly
`0..511`, and the same proposal SHA256
`F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16`.

- 2368 report `beta-lp-threshold-all-2368.json` (15 MB) SHA256
  `D8BD564CD6BE3DC0F2DEB53E2C5B00D0E93D587B6102ED1746C852D81EF8ED05`;
  verification `beta-lp-threshold-verification-2368.json` SHA256
  `230DE27290FA8A0E4DD2E552AC5021D4F2BD56FB911502AA7C56478E3F700688`.
- 2370 report `beta-lp-threshold-all-2370.json` (21 MB) SHA256
  `A423EEF78168128EEBB514567A3E343DAB7A727E5A688113ECC57BA4CE0E029D`;
  verification `beta-lp-threshold-verification-2370.json` SHA256
  `D8C69803D9B757355C08120641F7543BD76CAFF8D15268FA0D2CCD3E8DD837CA`.

Both independent `--require-complete` replays exited 0 with
`all-512-exact-rechecks-pass`, `complete: true`, certificates 512, masks
`0..511`. Generator SHA256 is unchanged
`F0A47F5AC6FD623FEBFDD5D1DCF0B4E93E1E092E8A4858F554900833ABAFFB3D`;
verifier SHA256 is unchanged
`09C653ED7EB38E18284F62B130741062E0529DE8EDD317897D0B9080CB9386DD`.
`py_compile` for both scripts exited 0 and `git diff --check` is clean.

Combined with parts 242-243, all seven public residual ids now have exact
512-region threshold-Farkas coverage, independently replayed. Scope: each sign
region has no LP point with `lower > T2` in this fixed model. This is **not
kernel credit, a residual-id payment, global infeasibility, or the
arbitrary-centre theorem**.

Still unproved: all 373 radius packets, the 382 absent payloads,
SevenClassExclusions (0/7), and the arbitrary-centre theorem. Next concrete
step: no further threshold sweep of these seven is informative; inspect the 354
non-public method-failure records for any complete proposal/DBM row set (versus
the 382 absent payloads), and if one exists run this same exact audit before
attempting a Lean consumer.
