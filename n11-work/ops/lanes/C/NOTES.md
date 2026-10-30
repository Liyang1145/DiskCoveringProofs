EXPERT (2026-10-30 07:19 UTC):
- No energy, residual, or class credit has moved; the seven public energy IDs are not the seven metric classes.
- The explicit-summand RowCaps repair targets the stale symbolic-sum failures, but the completed CI predates these bytes. Require one matching RowCaps exit 0, then stop this family.
- Even if green, row caps/strict gains duplicate `FrozenCapRationalCore` and have no consumer into `RemainingTerminalRadius`.
- `excluded_*_tree` remains conditional on `hf0`/`hg`; those equalities do not follow from `PaidCellCertificateM.Valid`. Its `db_eq_tree` also uses large `decide +kernel` terms, so do not target it without a paid consumer.
- The seven frozen-cap negatives are useful obstructions for any row count, not residual-radius payments.
- Highest leverage: freeze current bytes and mark C blocked on a positive consumer: either a public HOST payload for one of the 382 absent residual IDs, or a supervisor retask to a genuine class exclusion.
- If a payload appears, prove one `PaidCellCertificateM.Valid p` and feed `common_chart_radius` in a new bridge module; one paid ID reduces 389 to 388.
- More row-cap leaves, conditional wrappers, audits, or hash pins are not count progress.

# Lane C notes

## Standing constraints

- CI is the only kernel-verdict authority; local Lean startup is blocked/slow.
  Pay no energy/class credit until targeted modules are CI-green, wrappers are
  linked, and the 382 absent HOST records are supplied.
- `TARGETS.txt` gates Core, M, MCap, WideFieldWitnesses, WideFieldRowCaps.
  Do not target WideFieldExcludedTree until both wide modules are CI-green.
- Wrappers remain conditional on packet `hf0`/`hg`. Public residual payloads are
  exactly seven IDs; 382 HOST records are missing.

## Condensed history through part 88

- Core (`40861839784`), M (`40893868710`), and MCap (`40949277719`) are CI-green;
  axiom reports are clean. Exact HOST census/arithmetic found seven public residual
  records and no payload for the other 382 IDs.
- Earlier four/five-field sign reports were superseded by wide-support exclusion
  witnesses. The exact generator rechecks seven probability vectors, 700 ordered
  row caps, and seven strict `gain < T^2` margins with `Fraction` arithmetic.
- Run `40988698121` at `2fdf1a1c` made both wide modules red: seven old
  `strict_gain_*` declarations expanded `norm_num` directly and left unsolved
  goals. Parts 82-88 progressively replaced that expansion with core-theorem reuse;
  none of those bridges received a CI verdict.

## 2026-10-30 — parts 89-94 (condensed)

- Part 89 replaced seven huge `norm_num` witness `strict_gain_*` proofs with
  `simpa only [yW_node, endpoint_node] using
  FrozenCapRationalCore.strict_gain_node`. Current witness SHA256 is
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`;
  exact checks remain 7 probability vectors, 700 row caps, and 7 negative gains.
- Parts 90/93 split the 100-row proof into 700 single-pair leaves and 77
  dispatchers, but CI run `41001693009` still timed out at 200000 heartbeats on
  the first seven leaves. Part 94 confirmed the dispatcher structure and that a
  60 s Mathlib probe gave no verdict.
- Part 91 proved the sign trap: the seven public residuals are genuine
  arbitrary-row-cap exclusions, not rescue candidates. Part 92 scanned 732 local
  JSON files (2,222,361 bytes) plus both oversized C450 files and recovered zero
  of the 382 missing payloads; this is not evidence of external HOST absence.
- Current census: seven public residual IDs have exact exclusion witnesses; 382
  residual IDs still lack HOST payloads; no energy/class credit is paid.

## 2026-10-30 — part 90 (row-cap heartbeat split)

Did:
- Inspected run `40998371772` / job `123876728856` at `88918335` directly. The
  old `FrozenCapWideFieldWitnesses` has `=== EXIT ... 0`, but
  `FrozenCapWideFieldRowCaps` has exit 1. All seven failures are deterministic
  200000-heartbeat timeouts at the seven 100-case `row_cap_*` declarations; the
  run's workflow-level `success` is therefore **not** a green-row-cap verdict.
- Changed the generated row-cap proof from one `fin_cases i <;> fin_cases j`
  (100 cases under one declaration budget) to ten row lemmas of ten cases each,
  followed by a ten-branch dispatch. The exact caps, witness bytes, and theorem
  statements are unchanged. This gives each declaration a fresh 200k budget and
  an approximately 10x smaller tactic search.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `0b40b700c4f03a9e49cc029389a833bf8caf62a0b262696ae45f61d5de8cc052`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean`
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `375f66a83d43b9579cffc019d224e2976afcd46730e1fb2e0f1595c6cb014cee`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldExcludedTree.lean`
  `89f0bc8eb820b046dada09702e9d939a3b34fd90c212163e21eb8c76e5e4df37`.

Checks (scope): emitter exit 0 with 700/700 exact rational caps passing, minimum
slack 0 for all seven IDs, and seven strictly negative exact gain margins;
`py_compile`, hard-rule scan (clean), and `git diff --check` exit 0. No local
project build was run; the row-cap split and the part-89 canonical witness bridge
remain **CI pending**.

Still unproved/missing: CI exit 0 for the new row-cap bytes and for the canonical
part-89 witness bytes; WideFieldExcludedTree remains untargeted and conditional
on packet `hf0`/`hg`; 382 HOST payloads absent; no energy/class credit.

Next: on the next run require `=== EXIT 0` specifically for
`FrozenCapWideFieldWitnesses` and `FrozenCapWideFieldRowCaps`. If both are green,
add `N11Formalization.FrozenCapWideFieldExcludedTree` to `TARGETS.txt`. If a row
lemma still times out, split that row into five-case lemmas rather than raising
heartbeats.

## 2026-10-30 — part 91 (cap direction audit; no public rescue)

Did:
- Tested whether the four/five-field high-gain points in
  `residual-mixture-faces4.json` and
  `residual-mixture-faces5-float-2356-2360.json` could be lifted to generic-row
  packets by complementary slackness. The prototype was removed after the
  direction audit below showed that this is mathematically impossible.
- Re-ran `certify_next512_row_cap.py`: all 512 frozen next512 records checked,
  100 ordered-pair rows each, and 7/7 failing public records have an exact
  cap-feasible `y` with weighted gain strictly below the required gain. The
  smallest strict exclusion margin is `7.388363154221271e-07` (id 2356); the
  largest is `4.965940402992249e-05` (id 2368). These are exclusions for **any**
  number of DBM rows, not merely 10/12/16 rows.
- Clarified the sign trap: a cap-feasible high-gain point proves that one primal
  value is high, but `PaidCellCertificateMCap.weighted_reduced_le` gives
  `lower ≤ F0 + weighted_gain(y)` for every cap-feasible `y`. Hence the existing
  low-gain witness proves no packet with the same frozen `F0`/`g` can have
  `numeric` above `T^2`, regardless of row count. The seven local four/five-field
  `PASS` reports are therefore **not** rescue certificates.
- Re-ran `audit_pending_certificate_sources.py`: 7 records, 700/700 DBM entries
  match `DBMSourceTreeData.lean`, with the exact witness margins above.

Files / SHA256 (lowercase):
- `next512-row-cap-certificates.json`
  `0b50b075dbebc59bca5374fba604496f50660572c946ac6ce23f8f104027024b`.
- `pending-certificate-source-audit.json`
  `ab59708e14f177edee200468f51361073afbb69977a2b8433429c776d7da07f0`.

Checks (scope): both exact scripts exited 0; `py_compile` and `git diff --check`
exited 0. No Lean build or kernel verdict was run.

Still unproved/missing: the 7 public residual records are excluded, not paid;
the other 382 residual IDs still have no HOST packet payload, so no row-count
experiment can establish either a rescue or an exclusion for them. Wide-field CI
bytes remain uncredited.

Next: do not spend another session searching larger caps for the seven public
IDs. First audit the 382-ID census for any locally recoverable frozen payload;
otherwise record the missing-payload blocker and pursue CE/CI credit for the
wide-field modules.

## 2026-10-30 — part 92 (repository payload census)

Did:
- Added `audit_residual_repository_payloads.py`, which scans every JSON/JSONL
  under `n11-work` and `build` outside lane C, excluding files over 2 MB and
  recording those explicitly. A payload must carry `g`, `f0Lo`, and one of
  `beta`/`y`/`weights`/`support`; the script asserts zero recovered IDs.
- Exact run: 732 files / 2,222,361 bytes scanned, 0 residual-ID payload objects,
  0 recovered IDs. Two malformed JSON fragments under the vendored Mathlib
  devcontainer were reported, not parsed. Three files exceeded the bound: the
  two C450 HOST files under `build/n11-wip/assets/evidence/codex-handoff` and
  the already-audited 7.6 MB `paid16-general-next512.json`.
- Combined with the existing seven-directory exact audit, this removes the
  plausible local JSON route to the 382 missing IDs. A direct parse of both
  oversized C450 files found 0 residual-ID objects and 0 payloads. It does not
  prove HOST absence: external maintainer storage was not read.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_residual_repository_payloads.py`
  `9379b0c9bb7bcc8ecfd0e4541d8d5c2db27430f564eb5be55c43777d3ceef7bf`.
- `n11-work/ops/lanes/C/residual-repository-payload-audit.json`
  `ccdcf3fcbc6acf7f6587cc8348604728a9c3f014bb68ea7cd84db632b2629bb8`.

Checks (scope): `py_compile` exit 0; the bounded audit exited 0 with the counts
above. No Lean build or kernel verdict was run.

Still unproved/missing: 382 HOST energy payloads remain absent; the seven public
residuals remain excluded rather than paid; wide-field CI remains pending; no
energy/class credit.

Next: restore focus on a CI verdict for the wide targets; do not search local
JSON for the 382 payloads again unless new storage is mounted.

## 2026-10-30 — part 93 (row-cap declaration split to single cases)

Did:
- Diagnosed the seven deterministic 200000-heartbeat row-cap timeouts as a
  declaration-budget problem, not a failing cap: each generated row lemma still
  ran `fin_cases j` and `norm_num` over ten concrete sums in one theorem.
- Changed the emitter to produce 100 single-case lemmas per node (the statement
  has concrete `i` and `j`), ten lightweight row-dispatch lemmas, and the final
  100-pair dispatch. There are now 700 concrete cap lemmas and 77 dispatchers,
  with the same theorem names, exact caps, and witness bytes as before.
- Regenerated all wide outputs. Exact checks remain seven probability vectors,
  700/700 ordered row caps, seven strictly negative gain margins, and zero
  minimum cap slack for every public ID.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `546f116be7a9605993b06d82ba0746412f110f7829312b4c17645b59bb03959e`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `952b7f1a8c44dd36e62e9c45e124c8df8cb5df6343ab3c05922c727e1d67ab3a`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldWitnesses.lean` unchanged,
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`.

Checks (scope): generator exit 0 with the exact counts/margins above;
`py_compile`, hard-rule scan (clean), and `git diff --check` exit 0. No local
project build or kernel verdict was run; the split is **CI pending**.

Still unproved/missing: CI exit 0 for this row-cap split; the canonical
part-89 witnesses are also still CI pending; WideFieldExcludedTree remains
untargeted and conditional on packet `hf0`/`hg`; 382 HOST payloads absent; no
energy/class credit.

Next: require `=== EXIT 0` for `FrozenCapWideFieldWitnesses` and
`FrozenCapWideFieldRowCaps`. If a single-case leaf times out, replace its
`norm_num` list theorem with an explicitly computed rational equality/inequality
for that `(i,j)`; do not raise heartbeats.

## 2026-10-30 — part 95 (row-cap tactic budget fix)

Did:
- Read CI `41001693009`: `FrozenCapWideFieldWitnesses` is exit 0, but
  `FrozenCapWideFieldRowCaps` still times out at 200000 heartbeats on the first
  seven single-pair leaves. The failures occur every 21 source lines, so the
  remaining problem is per-leaf `norm_num` work, not dispatch.
- Changed generated leaves from one `norm_num [yW, rowA, db,
  Fin.sum_univ_succ]` call to `simp only [Fin.sum_univ_succ,
  Fin.sum_univ_one, Finset.sum_empty]`, followed by `norm_num [yW, rowA, db]`. This exposes nine
  concrete summands before rational normalization and avoids unfolding `rowA`
  under a variable `q`. Public theorem statements and `TARGETS.txt` are unchanged.
- Regenerated all three wide outputs. Exact checks: seven probability vectors,
  700/700 row caps, zero minimum cap slack for all seven IDs, and seven strict
  negative gain margins.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `16afedb4663e7a7681ac5532f0ffb04ae39b17f9e8797169c6ce94e728543132`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `2fe8f3f06a6df75994a7d282a156a727449418fd728126849d046383ad6acd92`.
- Witnesses and tree unchanged: `90a5c86e...b7cc6` and `89f0bc8e...4df37`.

Checks (scope): emitter exit 0 with the counts above; `py_compile` exit 0;
hard-rule scan and `git diff --check` clean. No local Lean build or kernel
verdict was run. This tactic split is **CI pending**.

Still unproved/missing: CI exit 0 for RowCaps; ExcludedTree remains conditional
on packet `hf0`/`hg`; 382 HOST payloads absent; no energy/class credit.

Next: request CI for `FrozenCapWideFieldRowCaps`. If a leaf still times out,
replace that leaf with a closed rational `have`/`norm_num` using its exact nine
summands; do not raise heartbeats. If green, target ExcludedTree.

## 2026-10-30 — part 96 (explicit row-cap summands)

Did: changed the 700 per-pair leaves from a symbolic `Finset.sum` followed by
`norm_num` to nine explicit summands; `norm_num` checks the sum, database entry, and final
constant inequality in separate `have` steps. Row dispatch uses
`simpa` with the established `Fin.sum_univ_succ`/`sum_univ_one` chain. A bounded
core-`Rat` probe showed plain `decide` cannot reduce `Rat`'s comparison
instance, so no `decide` proof was retained. Local project Lean remains
unavailable; this tactic change is **CI pending**, not a kernel verdict.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/emit_wide_field_exclusions.py`
  `2a373cacd905b2da72666bc7f232dd532e4dd7106a639cc66c0816c607d1d023`.
- `n11-work/lean/N11Formalization/FrozenCapWideFieldRowCaps.lean`
  `c6ef5004d63dfa50ec6f7dfe54a56e62399ff5be715ddc0f433002b8385cc34d`.
- Witnesses/tree unchanged: `90a5c86e...b7cc6`, `89f0bc8e...4df37`.

Checks: emitter exit 0; 700/700 exact caps, seven minimum slacks 0, seven strict
negative gains. Hard-rule scan and `git diff --check` clean.

Unproved/missing: CI exit 0 for RowCaps; ExcludedTree conditional on `hf0`/`hg`;
382 HOST payloads absent; no energy/class credit.

Next: require targeted CI for RowCaps. If red, read the exact failing leaf before
changing tactics; do not raise heartbeats. If green, target ExcludedTree.
