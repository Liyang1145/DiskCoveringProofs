# Lane A notes

## Current directives

EXPERT (2026-10-30 07:19 UTC):
- C450 stays closed (36/36, root-reachable through B12Main); make no C450 edits.
- The `hbhi` branch under outer `h7` is correct; Bins had only the ambiguous
  modulus at line 95.
- Require exits 0 in order Cos, Mono, Bins, EndpointChecks,
  UpperReductionUnimodal. EndpointChecks has no independent verdict before Bins.
- `edgePeakValid_*` is genuine peak credit; `EdgeMonotone` remains the only gap
  to EdgeValid.
- After green, prove full-angle `cosHiNLag_nodeQ_antitone` (the existing grid
  theorem is half-angle), split the 42 derivative leaves into
  `SevenClassQ0Deg3EdgeShape.lean`, then sectors, strict total, and
  `Q0Degree3AreaInput`.
- SevenClassExclusions remains 0/7; edge/peak tables alone pay no class.

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

## 2026-10-30 (session 24) — Bins modulus repair; suffix target registered

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3Bins.lean`
  `0e1fc14a8abef4980f3002b7447bb5090846e77bcbb8e2b8dd15c3989a56b1bb`.
- `n11-work/ops/lanes/A/TARGETS.txt`
  `b532fb08e16550a05b5c8608026f7e8927995a11db2896f3aac9e9114ad88406`.

**Change.** In `capMonotoneOnGrid_of_piHiCapSaturated`, the leaf
`Nat.mod_lt k.val (by norm_num)` was made fully explicit as
`Nat.mod_lt k.val (n := 256) (by norm_num)`. This is the exact first diagnostic
from the expert handoff. No statement or premise was weakened. Registered
`SevenClassQ0Deg3EdgeSuffixHigh` as a new C450-independent CI target.

**Checks (scope).** `project_status.py --check`, `git diff --check`, and the
source diff pass. Exact `Fraction` audits re-ran: edge unimodality PASS 21/21
(JSON `2a0a38b150cae0b9d200c90f273084b3bdbd4f51d43f4eca1270d8ea5b2f412f`)
and derivative signs PASS 21/21 (JSON
`628a20f6e4758b3a18ccd83215ac23a7e2fabbb11c701bd667a820643b97d726`). These
audits verify finite rational data, not Lean. A minimal Lean probe and the
Mathlib probe both timed out during startup/import; no local project build was
run. Thus Bins, EndpointChecks, UpperReductionUnimodal, and both suffix modules
remain **drafted, CI pending**.

**Still unproved.** Kernel acceptance of every lane-A target; all 42
`EdgeIncTo`/`EdgeDecFrom` facts; full-angle cosine monotonicity on the grid;
all 9 sectors; strict total; `Degree3AreaCertificate`/`Q0Degree3AreaInput`; all
seven exclusions; and the arbitrary-center full-disk theorem.

**Next concrete step.** On the next CI cycle read Bins first. If green, read
EndpointChecks then UpperReductionUnimodal; if Bins still fails, fix only its
first diagnostic. In parallel, begin `SevenClassQ0Deg3EdgeShape.lean` with the
edge 9 negative-coefficient suffix as a checked template, then add the edge 12
high-coefficient suffix, before attempting positive-derivative prefixes.

## 2026-10-30 (session 25) — negative-coefficient derivative defect repaired

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeSuffixNonpos.lean`
  `bc1b13e1a148d7f894771c40db4db74758933fe83cae833a8d7f1098405a096f`.
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeSuffixHigh.lean`
  unchanged, `ab2c023394b3c70781d5e72a316c078b83c5327f8b44f7992557bc4892c10c32`.
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeReal.lean` unchanged,
  `4ed2c5816272ebcef894fdfd12b6f2e3746de33192693cfb8f1642e6d69ddc4d`.

**Mathematical correction.** The drafted theorem
`edgeHiReal_deriv_neg_of_coeff_neg` was invalid: for `b < 0` and merely
`cosHiReal x ≤ 0`, the expression `A * cosHiReal x - b` can be positive.
Replaced it by `edgeHiReal_deriv_neg_of_cos_le_coeff`, whose exact sufficient
condition is `cosHiReal x ≤ b / A`, and by
`edgeHiReal_antitoneOn_of_cos_le_coeff`. Removed the unsupported
`edgeDecFrom_nine`/`edgeDecFrom_ten` conclusions. The exact coefficient census
from frozen rational table bytes is: 9 negative edges (2--7, 9, 10, 11),
10 mid-range positive edges (0, 1, 8, 14--20), and 2 edges above `A` (12, 13).
The zero-peak high-coefficient suffix proof for 12/13 is unaffected.

**Checks (scope).** `project_status.py --check` passed;
`git diff --check` passed; forbidden-token scan over the edited module passed.
No Lean build was run locally, so this correction is **drafted, CI pending**.
The coefficient census is exact `Fraction` arithmetic over the Lean table bytes,
not a Lean verification.

**Still unproved.** All 42 shape facts; in particular edges 9/10 need a rational
cosine upper bound below `b/A` on the suffix (the sign at witness node 1489 is
not sufficient by itself). Kernel acceptance of Bins, EndpointChecks,
UpperReductionUnimodal, and both suffix modules remains pending.

**Next concrete step.** Read the new CI Bins diagnostic first. In Lean, prove a
strict rational Taylor upper bound for `cosHiReal` at/after node 1490 sufficient
for edges 9/10 (threshold about `-0.65444`), plus the one discrete comparison
from witness 1489, then instantiate `edgeHiReal_antitoneOn_of_cos_le_coeff`.

## 2026-10-30 (session 26) — upper-tail edge-9/10 cosine bound drafted

**Files / SHA256.**
- `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeSuffixNonpos.lean`
  `d0dfd9f9c29a5b94b28e048a490c0cb63f587918baea2406b4622d921581face`.
- `n11-work/ops/lanes/A/TARGETS.txt` unchanged,
  `b532fb08e16550a05b5c8608026f7e8927995a11db2896f3aac9e9114ad88406`.

**Change.** Added `cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le`:
for `3*pi/4 <= x <= piHi`, the degree-28 upper cosine bracket is at most
`-2/3`. This is stricter than both `edgeCoeff 9 / (19/50)^2` and
`edgeCoeff 10 / (19/50)^2` (about `-0.654606`), so it supplies the analytic
upper tail of the split suffix argument. The proof splits at `pi`, uses real
cosine monotonicity and the exact `cos(3*pi/4) = -sqrt(2)/2`, and controls the
Taylor remainder by `4^28/28! <= 1/100`.

**Checks (scope).** `project_status.py --check` passed (declaration/manifest
scope only); `git diff --check` passed; forbidden-token scan over the edited
module passed. No Lean build was run, so the new lemma is **drafted, CI
pending**. The arithmetic comparisons are exact rational checks.

**Still unproved.** The narrow interval from the edge-9/10 witness (`node 1489`)
to `3*pi/4`; the discrete witness-to-next-node comparison; all 42 shape facts;
kernel acceptance of Bins and the downstream modules; all seven exclusions;
strict total and the arbitrary-center full-disk theorem.

**Next concrete step.** Add a rational Taylor-grid lemma covering
`nodeQ piHi 2048 1490 <= x <= 3*pi/4` with `cosHiReal x <= -2/3`, then combine
it with this theorem and the exact one-step comparison at witness 1489.
