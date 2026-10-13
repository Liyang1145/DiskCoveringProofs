# R15 — exact safe rerun interface for the 22 remaining joint-patch factors

Own files only: `research-2026/team-current/cline2-coupled-factors/`.
No heavy grid was run.  No claim registered.  Nothing in the lead's directory was modified.

## 1. Provenance split (the reason the old bounds are INAPPLICABLE)

There are **two different frozen coefficient files**, and the two halves of the joint
certificate currently use **different ones**:

| artifact | coefficient file | sha256 (first 12) |
|---|---|---|
| local Q0 ridge proof C854 (`certify_local_ridge.py`) | `joint_nested_frozen.json` | `5671967c5a3d` |
| 22 remaining factors (`certify_joint_rest.py`, `certify_joint_rest_tight.py`) | `joint_patch_frozen_v2.json` | `a856f2c12bcc` |

Evidence:
* `interval_joint_patch.py:8` → `frozen=P/'joint_nested_frozen.json'`, and
  `local_ridge_upper.json` records `coefficient_sha256 = 5671967c...` with an
  after-run source-hash block for all five files it imports.
* `certify_joint_rest_tight.py:7-8` → `frozen=P/'joint_patch_frozen_v2.json'`, and both it
  and `certify_joint_rest.py` textually replace the literal filename inside
  `certify_q0_closure.py` with `'joint_patch_frozen_v2.json'`.
* Every existing per-factor record `joint_patch_bound_00..28.json` carries
  `coefficient_sha256 = a856f2c12bcc24c428c2ac6044f81877059cc3039f73db992dc5e3e004c23636`.

**Consequence: the local Q0 half is already on the current coefficients; the 22-factor half
is not.**  The 22 factors must be recomputed, exactly as the task states.  Also note the two
halves are *independent coefficient paths* (`certify_joint_rest_tight.py` does not import
`interval_joint_patch.py`), so repointing the 22-factor half does not disturb the local Q0
proof.

File hashes:

```
joint_nested_frozen.json      5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb  (current)
joint_patch_frozen_v2.json    a856f2c12bcc24c428c2ac6044f81877059cc3039f73db992dc5e3e004c23636  (stale, INAPPLICABLE)
joint_patch_frozen.json       adf07c491585cfe536876da071f25b7707833eb05b39a053d920e15ee42e0eab  (older still)
```

Both current and stale files share identical schema: `z` length **121**, same
`faces` (11) / `edges` (21), same field list.  The index layout, normalizations and the
`assert all(x==0 for x in z[50:73])` guard (the eta/kappa block) are therefore unchanged, so
the kernel binds the new coefficients to the same factor indices with no reindexing.

## 2. The factor split (verified by direct read-out of the kernel, `audit_factor_list.py`)

29 factors.  `certify_joint_rest_tight.py:25` skips exactly

```
covered by the C854 local Q0 ridge proof : {1, 2, 12, 13, 21, 22, 23}      (7 factors)
R15 22 remaining targets                 : {0, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                                            14, 15, 16, 17, 18, 19, 20,
                                            24, 25, 26, 27, 28}           (22 factors)
```

The 22 are **exactly the complement** of the C854 skip list, `29 - 7 = 22`, with no factor
dropped.  In particular **factor 0 (`face0`) is included**; an earlier revision of
`rerun_joint_22.py` wrongly excluded it with an unsupported "has its own proof" note and is
withdrawn (`R15_22 = list(TO_PROCESS)` with an assertion `len == 22` and `0 in R15_22`).

### Label table, read straight off the kernel (not from memory)

`lead/certify_q0_closure.py` builds the list in three blocks -
`:35-67` `for t,f in enumerate(faces)` → `face0..face10`; `:68-75` `for bi in range(9)` →
`switch0..switch8`; `:76-108` `for i in range(9)` → `ring0..ring8` - so

| index | 0–10 | 11–19 | 20–28 |
|---|---|---|---|
| name | `face0 … face10` | `switch0 … switch8` | `ring0 … ring8` |

`audit_factor_list.py` loads the kernel with the **current** frozen bytes exposed under the
stale filename and prints all 29 `(index, name, domain)` triples plus the name→index map.
Its output confirms: 29 factors; `11 -> switch0`; `20 -> ring0` with domain
`[(0,π),(0,1),(0,1)]` (a 3-argument ring box, not a 1-argument switch interval); skip list
`{1,2,12,13,21,22,23}`; targets = the 22 above.  So the label in the R15 table
"index 20 = `ring0`" is **correct as printed**; the corresponding v2 record
`joint_patch_bound_20.json` also reads `ring0`, consistent with the kernel.

The audit script is read-only: it constructs the interval factor list and exits without
running any factor bound, and it removes the alias directory it needs.


## 3. The interface

`rerun_joint_22.py` (this directory).  It runs the lead's own certifier **unmodified** with
the **new** coefficients and writes into a **digest-keyed** directory in my scope.

How the repoint is done without touching lead files and without text-surgery on the kernel:

1. Build an ephemeral alias directory containing `joint_patch_frozen_v2.json` whose **bytes
   are exactly those of `joint_nested_frozen.json`** (sha256 verified equal before running),
   plus copies of the support files the certifier's `exec` needs
   (`certify_q0_closure.py`, `q0_exact_closure_radius.py`, `q0_graphs.json`) and the
   repo-relative input `n11/upper/certified_object.json`.
2. Run `certify_joint_rest_tight.py <i> <i+1>` with `cwd = alias`.  Both the digest computed
   at line 7 and the filename embedded at line 8 therefore resolve to the new bytes, while
   the kernel, normalizations, indices, C844 filter and per-factor budgets are the lead's
   originals.
3. Move each produced record into `out/r15_<digest12>/`, then delete the alias.

Commands (run from the repo root):

```
# full 22-factor sweep (one factor per process, each with the lead's own budget)
py -3 -B -X utf8 research-2026/team-current/cline2-coupled-factors/rerun_joint_22.py

# cheap pre-flight: factors 11 and 14 only
py -3 -B -X utf8 research-2026/team-current/cline2-coupled-factors/rerun_joint_22.py --preflight

# subset
py -3 -B -X utf8 research-2026/team-current/cline2-coupled-factors/rerun_joint_22.py --factors 20 24 25 26 27 28

# aggregate existing records only (no computation)
py -3 -B -X utf8 research-2026/team-current/cline2-coupled-factors/rerun_joint_22.py --aggregate
```

Outputs: `out/r15_5671967c5a3d/joint_patch_tight_bound_<i>.json` (the lead's schema plus
`wall_seconds`), `summary.json`, `summary.md`.

## 4. Safety properties (each one is a check in the script)

1. **Coefficient pinning.** The alias sha256 is asserted equal to the canonical
   `joint_nested_frozen.json` sha256 before any factor runs; every record is written with
   `coefficient_sha256 = 5671967c...`, and the aggregator flags `digest_ok` per row.  A
   record from the stale coefficients is therefore distinguishable by inspection and cannot
   be silently summed.
2. **Stale-output protection.** Records live only under the digest-keyed directory, so the
   certifier's own `if outpath.exists(): assert old['coefficient_sha256']==digest` skip-path
   can only ever see records of the *same* digest.  (The certifier's output filename does not
   contain the digest — it writes `joint_patch_tight_bound_<i>.json` — so mixing would
   otherwise be possible in the lead's directory; that is exactly what the digest-keyed
   directory prevents.)
3. **No bound conflation.** The aggregator sums only the factors actually present, prints
   `records_missing`, and both `summary.json` and `summary.md` carry a line stating the sum is
   over the 22 factors only and must not be combined with the C854 local value
   `28.10439974622152` or with any other partial bound absent a verified 29-factor split.
4. **No writes outside my scope.** Every artifact goes to
   `research-2026/team-current/cline2-coupled-factors/`; the alias is removed unless
   `--keep-alias` is passed.

## 5. Numeric readout actually available now

A **full** 22-factor readout under the new coefficients **does not exist** — confirmed
directly by the lead's own note in `LOCAL-RIDGE-UPPER-PROOF.md`: *"No 22 remaining factor
certificates for new coefficients yet; no full sum certificate."*  The pre-existing
`joint_patch_bound_*` records are all v2, and no `joint_patch_tight_bound_*` records existed
before this work.

**Status after the list correction:** the digest-keyed directory holds **2 of 22** records
(factors 11 and 14, from the interface validation run made *before* the factor-0 omission
was found — that run used the then-current list, so `face0` was never attempted and is
missing).  The corrected aggregator reports

```
missing = [0, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 24, 25, 26, 27, 28]
sum of present uppers = 0.000039953473        all22 = False
```

I ran only the two cheapest factors as an interface validation (about 0.6 s each, the same
evaluation counts as the old run's records for the same indices — 1411 evaluations — which
confirms the factor enumeration and domains are unchanged):

| factor | name | upper (new coefficients) | lower_probe | evals | budget_ended |
|---|---|---|---|---|---|
| 11 | switch0 | 2.0002210378923662e-05 | 2.7289974150546984e-08 | 1411 | False |
| 14 | switch3 | 1.9951263031208914e-05 | 4.188476284583149e-09 | 1411 | False |

Partial sum of these two (for interface checking only, **not** a bound): `0.000039953473`.
`summary.json` lists the other 20 as missing.

Note the coefficient change is not benign for the switch factors: in the v2 run switch5 and
switch7 had uppers `0.12902957` and `0.12983564`, while switch0/switch3 were `~2.0e-05`.
Under the new coefficients the optimizer redistributes magnitude across factors, so **no
v2 switch or ring value can be reused or extrapolated** — the whole 22 must be recomputed.

Cost estimate for the sweep (from the v2 timings, same certifier): most factors finish in
1–13 s with 1k–24k evaluations; the six `ring*` indices 20, 24, 25, 27, 28 each hit the
240 000-evaluation budget at ~60 s, so a full sweep is on the order of 8–12 minutes of wall
time.  I did not run it (instruction: no heavy grid).

## 6. How the full sum must be assembled (interface contract)

```
full joint-patch objective upper
    = [local Q0 ridge value]  +  [sum of the 22 factor uppers]
```
with the two terms **on the same coefficient digest** `5671967c...`:

* term 1 is `local_ridge_upper.json: upper = 28.10439974622152`, already on that digest
  (its recorded `coefficient_sha256` matches) and valid only on the Q0 local box
  `r∈[.379,.38], b1∈[1.106,1.108], b2∈[1.068,1.071], delta∈[.035,.040]`, all width fibers,
  0 live boxes;
* term 2 is the sum over the 22 records produced by this interface, and only counts when
  `records_missing = []` **and** every row has `digest_ok = True`;
* neither term may be quoted alone as a global statement: C853/C854 are local to the Q0
  ridge box, and the 22-factor sum is not a bound on the rest until its own coverage
  hypothesis (the factor domains actually tile the complement of the Q0 box) is verified
  separately.  That coverage step is **not** part of this interface and is **not** claimed.

## 7. Files

* `rerun_joint_22.py` — the interface (driver, alias builder, aggregator).
* `scan_frozen.py` — provenance scan used to establish section 1 (read-only).
* `out/r15_5671967c5a3d/` — digest-keyed records, `summary.json`, `summary.md`.
* `out/preflight.log` — the validation run log.
