# Rejection note: wave4 `shard_splits` bookkeeping bug (immutable record)

Status of this note: **the `wave4-*` artifacts are rejected and frozen as
evidence. Do not use them, do not overwrite them.** The corrected replacement is
the `wave4fix-*` set described below.

## What was wrong

`merge_branches.py` computed the number of structural (shard) splits performed
when refining a source pending into its branch roots as the hardcoded constant

    shard_splits = 3

That value is correct only for the plans that split one pending twice
(stage11825: 11 branches for 8 pendings; reshard: 7 branches for 4 pendings).
For a `deep=0` plan every branch root IS a source pending, so no structural
split is performed and the correct value is 0. The wave4 freeze used the
`final-wave` plan (7 branches for 7 pendings) with the constant, so its
cumulative counters were 3 too high in both `split` and `processed`. This is a
bookkeeping/metadata defect only: the leaves, the pendings, the volume identity
and the tree structure of that freeze are unaffected, and no mathematical claim
depends on the counters.

Observed failure of the tree-count invariant (a forest of binary trees rooted at
the original box has `#internal = #leaves + #pending - 1`, i.e.
`split = certified + infeasible + pending - 1`):

    wave4-base.json   processed 13916  split 6964  certified 6634  infeasible 318  pending 10
    required          processed 13913  split 6961  (6961 = 6634 + 318 + 10 - 1)
    error              +3                +3

## The fix

`shard_splits` is now derived, never hardcoded:

    shard_splits = sum over source pendings of (roots_of_that_pending - 1)
                 = len(plan.branches) - len(source.pendings)

with the following checks added to `merge_branches.merge` (all reported in the
manifest under `counts`):

  * negative values are rejected (a plan with fewer branches than pendings);
  * the number of distinct parents must equal the number of source pendings;
  * the derived value must equal `branches - pendings`;
  * the SOURCE snapshot's own counts are checked against the invariant
    `split = certified + infeasible + pending - 1` and
    `processed = split + certified + infeasible` (guards against a corrupted
    base propagating its counters);
  * the merged totals are checked against the same invariant;
  * each branch's own `split` is checked against `frontier boxes - 1`.

Derivation check on the three plans in use: stage11825 11-8 = 3 (as before),
reshard 7-4 = 3 (as before), final-wave 7-7 = 0 (the corrected value).

## Quarantined artifacts (hashes of the files as they stand; do not modify)

    wave4-base.json       sha256 1f5247bb43232f3d4f440aaa31c0806728ad815d39efaee64e7e0d9b04b8e733
    wave4-plan.json       sha256 8662b5b077bd050fbfa8424efbfb3c4cf830323b373de7aa08bafe13e5b1c425
    wave4-manifest.json   sha256 6dd8ad997d8a7b9b5800ff29ec210884ce752289af8ea49dbf5a21b70ebf412d

(`wave4-plan.json` also pins the rejected base through its
`source.sha256 = 1f5247bb…`, so it is equally unusable as a wave plan.)

## Corrected replacement (generated from the same final-wave plan and the same
## seven stopped branch files under evidence/final-wave-domain/)

    wave4fix-base.json     sha256 daec632f122cc528eaf05aa49b1841e53f58caef203c49fc18cd53fc04094526
    wave4fix-plan.json     sha256 82777c96107b4c3a833b315ed193ed3fefb0f26023df489e28b9591d072ddecf
    wave4fix-manifest.json (merge manifest of the same run)

Counts of `wave4fix-base.json` (status partial):

    processed 13913   split 6961   certified 6634   infeasible 318   pending 10   leaves 6952

which satisfies both invariants exactly (6961 = 6634 + 318 + 10 - 1 and
13913 = 6961 + 6634 + 318). `wave4fix-plan.json` has
`branch_count = 10` (one root per pending), an absolute `source.path`, and
`source.sha256 = daec632f…`; an independent `check_plan` run reports no
problems.

Pinning note: pin the **file** hashes above. (For the `wave4fix` files the plan
file was written by the pre-patch writer, whose text used the platform newline,
so the LF-normalised text hash differs from the file hash; the writer now emits
bytes directly so that future waves report the file hash itself. Workers must
hash the plan file's bytes, as before.)

## Rules recorded here

 1. `wave4-*` = rejected evidence; keep, never use, never overwrite.
 2. `wave4fix-*` = the replacement to verify and use.
 3. Any wave whose base fails `split = certified + infeasible + pending - 1`
    must be regenerated rather than patched, because the counters are cumulative
    and the error propagates to later waves.
