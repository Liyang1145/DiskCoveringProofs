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

## Condensed status through 2026-10-31 part 179

- Exact residual census remains 389 ids. Seven public exclusions
  `{1409,2337,2341,2356,2360,2368,2370}` are the only ones with public tree
  payloads; the other 382 remain absent from public evidence.
- Live run `41182882564`, source `7f7e6f3b`, proves the public row-cap path is
  kernel-green: smoke and all seven `FrozenCapRowCap*` modules exited 0. Scope:
  those module declarations only, not a packet/payment theorem.
- Same run: `FrozenCapFourFieldWitnesses`, five-field modules, public tree, and
  aggregate exited 1. Public tree was blocked by the syntax failure in
  `FrozenCapRowCapTreeBridges.lean:49`, not by its seven row-cap dependencies.
- Earlier conditional singleton/refinement payloads and B13 aggregates remain
  CI-green where `ci/LATEST.md` or the fresh run says exit 0. No root import was
  changed.
- Missing: exclusion-to-`RemainingTerminalRadius`; packet existence/`Valid`;
  382 residual payloads; MPacket validity; energy and seven-class premises.

## 2026-10-31 - part 179 (fresh CI triage and corrected four-field search)

Fresh live-log triage of run `41182882564` (`7f7e6f3b`) confirmed public path
exit 0 for smoke and nodes 1409/2337/2341/2356/2360/2368/2370. The working-tree
tactic experiments were reverted to those tested source hashes:
`FrozenCapRowCap1409.lean` `9652ecf3...`, smoke `0065e3b0...`.

Fixed `FrozenCapRowCapTreeBridges.lean` by deleting the stray unnamed `end`
before the namespace close. New SHA256
`ee62bc4b023b6590d52bbdebad3ed012804c60a620e982a2fe09a09a4284ac94`.
This addresses the exact first CI error at former line 49, but the fixed file is
**CI pending**; no local kernel claim.

Found and corrected a sign inversion in `residual_mixture_faces4.py`: the Lean
obligation is `F0 + gain < T^2`, so valid witnesses minimize `gain` and require
`gain < T^2 - F0`, not `gain > T^2 - F0`. Re-ran the exact vertex search.
Only three of the five previously reported four-field rescues survive:
`1409`, `2337`, `2341`. Modules `2368` and `2370` fail the true criterion;
`2356` and `2360` still have no <=4-field rescue. The old five-record
`FrozenCapFourFieldWitnesses.lean` is therefore mathematically invalid and
remains unpaid/CI-red.

Emitted `FrozenCapFourFieldWitnessesCorrected.lean` for the three survivors,
with exact 300/300 row-cap checks and strict-gain assertions in the deterministic
emitter. SHA256:
`9fb19402705c20e3eed9db278c5a73f4903017c5342bfdc8168502a27698f19c`.
No row-cap/tree consumer yet, so this is **CI pending**, not payment.

Other files/SHA256 (lowercase): corrected search
`fb1725acd8266dc21bad539b56eb9e5e217c078d6311e551a21f411ed637556d`;
search report `f34e2b9e70d44c0a82f0ad248337c1e0afac8d726e2b312b305b6a1ab8c4549c`;
corrected emitter `41c58d9a61248d942790db9b7bc6ae7267e95ae4ac48b097a3025f67d590082b`;
`TARGETS.txt` `759efd2e340b3708d90c7fcb6dda12d44f4b4c532e1951a0f899675cdfc903c0`.

Checks/scope: corrected exact search exited 0 and emitted three strict witnesses;
`py_compile` passed for the five touched Python tools; `git diff --check` and
forbidden-token scans over the two new/fixed Lean modules passed. A 90 s Mathlib
probe timed out before diagnostics, so there is **no local Lean syntax/kernel
claim**.

Next concrete step: commit and run serial CI in this order: smoke, seven public
caps, `FrozenCapRowCapTreeBridges`, `FrozenCapPublicExcludedTree`,
`FrozenCapPublicExcludedAggregate`, then
`FrozenCapFourFieldWitnessesCorrected`. If the aggregate is green, build a
consumer theorem from its conditional exclusions; do not count it as residual
payment. Then search five or more fields for the four remaining failing ids
(`2356`, `2360`, `2368`, `2370`) using the corrected minimum criterion.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 183 (gain-direction error; extended rescue withdrawn)

While adding the owed deterministic witness emitter, its exact assertion failed.
The search reports for 2356/2360/2368/2370 maximize the affine endpoint gain,
but `PaidCellCertificateMCap.not_valid_of_frozen_cap` needs
`F0 + gain < T^2`, so a valid witness minimizes gain. Exact recomputation from
the frozen proposal gives `lhs - T^2` equal to
`-224116996675606852438149751746580829014815599688286686936434284034546291 / 879609302219040781395558400000000000000000000000000000000000000000000000000`
for the best vertex of 2356 and similarly strictly negative for 2360, 2368,
2370. Thus the new "Extended" witnesses' claimed strict inequalities are false;
`FrozenCapFiveFieldWitnessesExtended`, its row caps, exclusions and aggregate
are mathematically invalid and must not be built or consumed. The temporary
deterministic emitter enforced the true `<` criterion and correctly refused the
bad report; it was deleted with the invalid artifacts.

This does not block the public seven: green `FrozenCapRationalCore` already
contains valid `strict_gain_*` proofs for all seven ids, and the green
`FrozenCapRowCap*` modules use those same `y_*` vectors. Removed all invalid and
redundant four/five-field rescue modules from `TARGETS.txt`; retained the green
public row-cap/tree path. Scope: exact rational audit over the frozen proposal
and cap reports; all seven existing `y_*` vectors independently recompute as
strictly passing (`lhs < T^2`, supports of size 5/6). Static target/text checks
also passed; no new Lean kernel claim.

Still unproved: conditional exclusions to packet payment, packet existence and
`Valid`, the `RemainingTerminalRadius` bridge, and 382 payloads absent publicly.
Next concrete step: audit whether `FrozenCapPublicExcludedAggregate` can be
consumed by any existing residual-membership theorem without inventing packet
hypotheses; otherwise target the 382 absent payloads.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 184 (corrected-witness emitter validation and CI queue)

Confirmed the withdrawn five-field artifacts are absent from the worktree and
`TARGETS.txt`; old parts 180-182 are condensed out because part 183 invalidates
them. Re-ran the deterministic corrected-witness emitter with a 60 s bound. It
exited 0, regenerated `FrozenCapFourFieldWitnessesCorrected.lean` byte-for-byte
(SHA256 `9fb19402705c20e3eed9db278c5a73f4903017c5342bfdc8168502a27698f19c`),
and rechecked all 300 ordered-pair rational row-cap inequalities for its three
witnesses. `py_compile` exited 0. Forbidden-token scans over the corrected
module and fixed `FrozenCapRowCapTreeBridges.lean` found no matches;
`git diff --check` exited 0.

Added `N11Formalization.FrozenCapFourFieldWitnessesCorrected` to `TARGETS.txt`
so CI checks it independently. This is **CI pending**, has no row-cap or
exclusion consumer, and pays no residual id. The fixed tree bridge remains
**CI pending**. `TARGETS.txt` SHA256 is
`4bb2c506b96990f7b2c38a36078972ab13df1db34d79453e33dbb961771e4326`.

Still unproved: corrected witnesses -> row caps/exclusions; conditional
exclusions -> packet payment; packet existence/`Valid`; the
`RemainingTerminalRadius` bridge; 382 payloads absent from public evidence.
Very next concrete step: read the next serial CI summary in target order. If the
tree bridge is green, inspect the aggregate's condition and seek a real
residual-membership consumer without adding packet hypotheses; if the corrected
module is red, fix its first local declaration error only.

ROOT-IMPORT REQUEST: none.
