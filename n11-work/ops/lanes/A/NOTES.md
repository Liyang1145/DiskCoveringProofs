EXPERT (2026-10-30):
- Do not add suffix theory until Bins exits 0 on `dab6f41b...`; current red is dependency-level, not a verdict on `1bad1980...`.
- If Bins red, fix only `Nat.mod_lt k.val (y := 256)` first; then build EndpointChecks, UpperReductionUnimodal, both suffix modules in order.
- Sound next proof: add `edgeDecFrom_of_antitoneOn_from_next` with an exact step at witness `w`, then antitone on `Icc (nodeQ ... (w+1)) piHi`; edges 9/10 have `w=1489`.
- Split at `k=1489`; use `cosHiReal_le_neg_131_over_200_of_narrow` on `[1490,3*pi/4]` and the existing `-2/3` tail.
- Prove `-131/200 ≤ edgeCoeff 9/(19/50)^2` and the edge-10 analogue by `norm_num`; never claim `-2/3` on the whole narrow interval.
- Close only `EdgeDecFrom 9/10`: 2/42 shape facts. SevenClassExclusions remains 0/7 until sectors, strict total, and `Q0Degree3AreaInput`.

# Lane A notes

## Ledger

- C450 is closed at `495c970c`, CI-green and transitively imported through
  `EnergyTerminalBatchB12Main`; stale `HARK-MISSING` comments are not a gap.
- Cos and Mono were CI-green at `e5875cf8`.
- Bins repairs: replaced unavailable `le_or_lt` by `by_cases`; removed the
  redundant inner split after outer `h7`; rewrote `binHi` with `simp`; and on
  2026-10-30 fixed the remaining modulus with explicit `n := 256`.
- EndpointChecks restricts lower Taylor premises to bins 0--4 and handles bins
  5, 6, 7 separately. Exact endpoint audit passed 8/8 with minimum slack
  `6.6940497252e-7` (bin 7).
- UpperReductionUnimodal contains 21 separate exact peak checks and the
  single-peak reduction. The 42 prefix/suffix shape facts remain unproved.
- `SevenClassQ0Deg3EdgeSuffixHigh` drafts decreasing suffixes for zero-peak
  edges 12/13 using coefficient above `(19/50)^2`; it was not previously a CI
  target.
- `SevenClassQ0Deg3EdgeSuffixNonpos` drafts decreasing suffixes for negative
  coefficient edges 9/10 using `x >= 2*pi/3 => cosHiReal x <= 0`.
- Seven-class exclusions: 0/7 paid. No kernel-green all-node degree-three
  certificate yet.

## 2026-10-30 (sessions 24--25, condensed)

Bins modulus diagnostics were repaired through `(y := 256)`. The attempted
edge-9/10 derivative criterion `cosHiReal <= 0` was invalid and was replaced
by the exact threshold `cosHiReal <= b / (19/50)^2`; unsupported wrappers were
removed. Cos and Mono were CI-green at `e5875cf8`. Seven exclusions remain 0/7.

## 2026-10-30 (session 26, condensed) — upper-tail cosine bound

Added `cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le`: on `[3*pi/4, piHi]`
the degree-28 upper cosine bracket is at most `-2/3`, below both edge-9/10
thresholds. Exact-rational comparisons and `git diff --check` passed; no Lean
build, so the lemma remained drafted/CI-pending. Later sessions supplied the
narrow interval and exact witness step. Still unproved at that point: all 42
shape facts, seven exclusions, strict total, and the full-disk theorem.

## 2026-10-30 (session 27) — exact Bins CI diagnostic; modulus binder repaired

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3Bins.lean`
  `dab6f41be4b788f686847f86d1ac8c91ce1b10597ec32ee94f8370dcd2bfc9dc`.
- `n11-work/ops/lanes/A/audit_q0_degree3_narrow_cos.py`
  `34b7220dab4ec47c098c24cbc013f8c29e8f1bb7a89861af8dd8765903f20c32`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `b532fb08e16550a05b5c8608026f7e8927995a11db2896f3aac9e9114ad88406`.

**CI evidence recovered.** Public job log for run `41017279843`, job
`123936372524`, gives the precise first Bins failure at line 95:
`unsolved goals ... |- 0 < ?m.223`, after the relevant hypotheses and before
any endpoint leaf.  This shows that the previous `(n := 256)` annotation did
not instantiate `Nat.mod_lt`'s divisor.  Lean core declares the binder as
`{y : Nat}`, so replaced the annotation by `(y := 256)`.  The same log shows
Cos and Mono exit 0 at that revision; Bins then causes
EndpointChecks and UpperReductionUnimodal to exit 1 transitively.
A newer branch build, run `41023888165`, is in progress at `83710e22`; this
repair is newer than that revision and has not yet been seen by CI.

**Checks (scope).** `project_status.py --check` passed (manifest/index scope),
`git diff --check` passed, and the forbidden-token scan over Bins passed.  No
Lean build was run locally: the project has no local `.lake/build`, and this
worktree must not start a full build.  The binder repair is **drafted, CI
pending**.

**Correction to the previous next step.** The proposed bound
`cosHiReal x <= -2/3` throughout `[nodeQ piHi 2048 1490, 3*pi/4]` is false.
Exact rational evaluation of the degree-28 upper bracket at node 1490 is
`-0.6554928529996153`; this is above `-2/3` by about `0.011173813667`.
The useful sufficient threshold is `-131/200 = -0.655`, which is below both
edge-9/10 coefficient ratios (about `-0.654606`) and just below the node-1490
value.  `audit_q0_degree3_narrow_cos.py` verifies all of these comparisons with
exact `Fraction` arithmetic and asserts that the `-2/3` check fails.  Do not
state the `-2/3` narrow-interval lemma.

**Still unproved.** Kernel acceptance of the Bins binder repair and every
downstream target; all 42 edge-shape facts; the narrow cosine-tail bound; all
seven exclusions; strict total; and the arbitrary-center full-disk theorem.

**Next concrete step.** Read the next CI Bins diagnostic.  If green, read
EndpointChecks first.  For edge 9/10, prove the narrow `-131/200` tail as a
split argument: exact node-1490 endpoint, decreasing degree-28 bracket on
`[pi/2, 3*pi/4]`, and the existing `-2/3` theorem above `3*pi/4`; repair the
one discrete witness-1489 step separately.

## 2026-10-30 (session 28) — narrow cosine tail proof drafted

**File / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeSuffixNonpos.lean`
  `1bad1980d1d74acaf2db29d8d6255c90b1ed62f87eec38e65617681790c6e02e`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `b532fb08e16550a05b5c8608026f7e8927995a11db2896f3aac9e9114ad88406`.

**Mathematical progress.** Added the analytic narrow-arc proof rather than the
disproved global `-2/3` claim.  `sinT14_nonneg_of_two_le_of_le_three_pi_div_four`
shows the degree-27 sine bracket is nonnegative on `[2, 3*pi/4]`: use
`sin x >= sqrt(2)/2 >= 2/3` on this arc and the Lagrange remainder
`|sin x - sinT 14 x| <= x^29/29! <= 3^29/29! <= 1/100`.  Hence the derivative
`-sinT 14 x` of `cosHiReal` is nonpositive, giving
`cosHiReal_antitoneOn_narrow` on
`[nodeQ piHi 2048 1490, 3*pi/4]`.  The endpoint is isolated as
`cosHiNLag_nodeQ_1490_le_neg_131_over_200`; casting it through
`cosHiNLag_cast` yields `cosHiReal_le_neg_131_over_200_of_narrow`.  No C450
files were edited.

**Checks (scope).** `python tools/project_status.py --check` passed
(declaration/manifest scope only); `git diff --check` and the forbidden-token
scan over the edited module passed.  The exact `Fraction` audit passed all five
assertions, including node-1490 value `-0.6554928529996153 <= -131/200`, both
edge-9/10 coefficient thresholds, and the intentional failure of `<= -2/3`.
The cached Mathlib probe exceeded its 180 s import/elaboration budget without a
diagnostic, so no Lean verdict exists.  This module remains **drafted, CI
pending**.

**Still unproved.** Kernel acceptance of the modified suffix module and all
registered targets; the one discrete witness-1489-to-1490 comparison and the
actual `edgeDecFrom_nine`/`edgeDecFrom_ten` wrappers; all other edge-shape
facts; all seven exclusions; strict total; and the arbitrary-center full-disk
theorem.

**Next concrete step.** Read the next CI diagnostic for this module first.  If
the narrow proof is green, instantiate it for edges 9/10 on
`[node 1490, 3*pi/4]`, combine with the existing `-2/3` theorem on
`[3*pi/4, piHi]`, and separately repair the witness-1489 step.  If red, fix
only the first diagnostic under a bounded command.

## 2026-10-30 (session 29) — edge-9/10 suffix bridge drafted

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `3063440ec59ca726e336c7b1137daaed7463b0732caf40c64c4bfad54facb177`.
- `n11-work/ops/lanes/A/TARGETS.txt`
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.
- `n11-work/ops/lanes/A/audit_q0_degree3_narrow_cos.py`
  `ace4e57bf3e37266eb65b80cc0b31b78a5a1e9caa46ac226558d0848b341f9e6`;
  report `audit-q0-degree3-narrow-cos-20261030.json`
  `dc78f86dc2542e1fb848af87267264ec7d784e0f9c2e2c7268ded4ac4091e807`.

**Progress.** Added the missing witness-to-tail bridge for edges 9/10. Their
witness is 1489 but the proved cosine tail starts at 1490, so the new helper
takes the exact one-grid-step inequality explicitly. Added threshold comparisons
for both edges, narrow/tail composition through `-131/200` and `-2/3`, the two
analytic antitone tails, exact 1489-to-1490 steps, and `edgeDecFrom_nine` /
`edgeDecFrom_ten`. No frozen module or C450 file was edited.

**Checks (scope).** `project_status.py --check` passed (index/manifest only);
`git diff --check` and forbidden-token scan passed. Exact `Fraction` audit
passed: both edge thresholds, node-1490 `-131/200`, and both step differences
strictly negative (edge 9 `-6.803164649171186e-08`, edge 10
`-6.8016306683833e-08`). This audit is rational table arithmetic, not Lean.
No local project build was run, so the new module is **drafted, CI pending**.

**Still unproved.** Kernel acceptance of `SevenClassQ0Deg3EdgeShape`; all edge
prefix (`EdgeIncTo`) facts; the remaining negative-edge suffixes 2--7/11; all
other shape credits; nine sectors; strict total; seven exclusions; and the
arbitrary-center full-disk theorem.

**Next concrete step.** Read the first CI diagnostic for EdgeShape (after its
imports, especially Bins, are green). If it compiles, extend the same exact
endpoint/threshold pattern to edge 11 and then a positive-coefficient prefix.

## 2026-10-30 (session 30) — edge-11 suffix proof drafted

**File / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean`
  `a69bccf854c23daa87827583f9aaa747085db6556341fe8a70cccf62f5589899`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Progress.** Edge 11 has coefficient about `-0.0206432`, witness 1118, and
ratio `b/A` about `-0.1429584`. Added `sinT14_nonneg_of_half_pi_le_of_le_two`
on the previously missing `[pi/2, 2]` arc, using `sin x >= 1/2` and the
degree-29 remainder below `1/4`. Combined it with the existing quarter-circle
and `[2, 3*pi/4]` sine lemmas to prove
`cosHiReal_antitoneOn_1118_to_three_pi_div_four`. Added the exact endpoint
bound node-1118 cosine `<= -103/720`, the exact threshold comparisons, the
split narrow/tail cosine bound, `edgeHiReal_antitoneOn_eleven`, and
`edgeDecFrom_eleven`. No frozen or C450 file was edited.

**Checks (scope).** `project_status.py --check` passed before editing this
session (index/manifest only); `git diff --check` and the forbidden-token scan
over `EdgeShape` passed. The authoritative CI snapshot still has no EdgeShape
verdict. No project or probe build was run because the local host is weak and
the cache/import budget is insufficient, so the new proof is **drafted, CI
pending**, not paid.

**Still unproved.** Kernel acceptance of everything after Bins; all 21
`EdgeIncTo` prefixes; negative suffixes 2--7; the remaining positive suffix
and prefix shape facts; nine sectors; strict total; seven exclusions; and the
arbitrary-center full-disk theorem.

**Next concrete step.** Read the first CI diagnostics in order Bins,
EndpointChecks, EdgeSuffixNonpos, EdgeShape. Fix only the first red target. If
EdgeShape is green, start edge 14's positive-coefficient increasing prefix,
using the witness-486 region and exact endpoint step checks.

## 2026-10-30 (session 31) — bounded local elaboration attempt blocked

**Files / SHA256.** No source change. `SevenClassQ0Deg3EdgeShape.lean`
`a69bccf854c23daa87827583f9aaa747085db6556341fe8a70cccf62f5589899`;
`TARGETS.txt` `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.

**Checks (scope).** Re-ran `audit_q0_degree3_narrow_cos.py`: all seven exact
`Fraction` assertions passed (node-1490 value `-0.6554928529996153`; both
edge 9/10 thresholds; both strict 1489-to-1490 steps). `project_status.py
--check` and `git diff --check` passed (index/manifest and whitespace only).
A 45 s bounded `lake env lean .../EdgeShape.lean` attempt did not reach
elaboration: Lake tried to check out Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` and aborted because the local
dependency tree has untracked files. No Lean diagnostic or kernel verdict was
obtained. Source audit found no forbidden tokens and the new sine-monotonicity
call matches existing Mathlib API use in this repository.

**Still unproved.** Kernel acceptance of Bins, EndpointChecks,
UpperReductionUnimodal, EdgeSuffixNonpos, and EdgeShape; negative suffixes
2--7; all 21 edge prefixes; remaining shape facts; seven exclusions; strict
total; arbitrary-center full-disk theorem.

**Next concrete step.** On the next authoritative CI run, read the first
diagnostic in order Bins, EndpointChecks, EdgeSuffixNonpos, EdgeShape. Fix only
that target first; if EdgeShape is green, draft edge 14's positive-coefficient
increasing prefix using witness 486 and exact endpoint steps.

## 2026-10-30 (session 32, part 4) — edge-14 shortcut rejected; CI still pending

**Files / SHA256.** No persistent source change. `SevenClassQ0Deg3EdgeShape.lean`
restored exactly to `a69bccf854c23daa87827583f9aaa747085db6556341fe8a70cccf62f5589899`;
`TARGETS.txt` `0e014984097afe340efcf6c6b948b1a114af817c7c44b115ed6d1f1847bac1f2`.
`LATEST.md` was re-read: it still snapshots run `41011262474`; the newer
`41017279843` / `41023888165` runs have no checked-in diagnostic yet.

**Progress / correction.** Audited the natural "nonpositive coefficient"
shortcut for edge 14 with exact `Fraction` arithmetic parsed from `mu` and
`tableEdges`. Edge 14 is `{10,2}` with
`b = edgeCoeff 14 = 848282000000000000000000000000000000193 / 8000000000000000000000000000000000000000`
(about `0.10603525`), and `b / (19/50)^2` is about `0.73431614`; therefore
`b ≤ 0` is false. Witness 486 gives `q ≈ 0.74551466 < 3/2 ≤ π/2`, so the
sine term is increasing, but the subtracted `b*q` term opposes it. A provisional
generic lemma was drafted and then fully removed after the exact countercheck;
the restored source hash matches the prior frozen working hash. Any edge-14
increasing-prefix proof must instead establish
`cosHiReal x ≥ b/(19/50)^2` on the prefix (margin at the witness is only about
`3e-4`), using a rigorous cosine lower bracket.

**Checks (scope).** Exact rational sign/margin audit only, not Lean. Also ran
`python tools/project_status.py --check` successfully (index/manifest scope),
`git diff --check`, and the forbidden-token scan over EdgeShape. No Lean build;
nothing new is CI green.

**Still unproved.** Every item listed in session 31, plus `EdgeIncTo 14` and all
other edge prefixes.

**Next concrete step.** Implement a rigorous degree-28 cosine *lower* bracket
and prove it exceeds the exact edge-14 ratio on `[0, nodeQ 486]`; then use
`edgeHiReal_deriv_nonpos`'s positive analogue plus
`monotoneOn_of_deriv_nonneg` to obtain `EdgeIncTo 14`. First inspect newer CI
and fix Bins if its binder repair has a diagnostic.
