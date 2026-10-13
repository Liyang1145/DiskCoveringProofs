# Parallel-domain sharding: API and audit

Scope: safe branch sharding of the k=10 wrapper domain plus an independent
merge/verification interface. Nothing here runs a solver, and nothing here
writes into the lead's tree. Files in this directory:

| file | role |
|---|---|
| `boxlib.py` | exact rational boxes, canonical widest-dim bisection, frontier tree checker |
| `plan_branches.py` | `plan` / `check` commands: immutable shard plan, plan verification |
| `merge_branches.py` | verifies worker outputs and emits a merge manifest |
| `selftest_rejections.py` | negative tests: every tampering mode must be rejected |
| `stage11825-plan.json` | the immutable plan for `evidence/hubline-domain-stage11825.json` |
| `merge-partial.json` | merge manifest for the branches that exist at the time of writing |

## 1. Branch numbering is byte-identical to the worker

`plan_branches.py plan <snapshot> <plan> --deep 2` reproduces exactly the root
order of `lead/run_domain_branch.py`:

    pending 0  -> canonical bisection twice -> branches 0,1,2,3
    pending i  -> branch 3+i,          i = 1..7      -> branches 4..10

Verified independently by regenerating the roots with the worker's own rule
(`k = max(range(3), key=lambda j: B[j][1]-B[j][0])`, midpoint split, children in
order `(lo,mid),(mid,hi)`, two levels for pending 0): all 11 `(parent, root)`
pairs match the plan by exact encoded box and by sha256 of the canonical box
string. The plan pins these hashes:

    plan sha256    74683b3d6eb701e7aa175984cf4e28a920fc2ed10e66227ce696081448b91f4d
    snapshot sha256 26fefd6a842b9ca961498c3fd45fbfa5fd1c7ab4906ef22574bea0e0de42d6d1

The plan is written once and never rewritten; `check` re-derives it from the
snapshot and compares (hash of the snapshot file, per-pending hash, per-branch
root hash, exact canonical refinement of every pending, pairwise
interior-disjointness of all branch roots, and equality of the total pending
volume with the total branch-root volume).

## 2. CLI and callable API

    plan   : py -3 plan_branches.py plan   <snapshot.json> <plan.json> [--deep K]
    check  : py -3 plan_branches.py check  <snapshot.json> <plan.json>
    merge  : py -3 merge_branches.py <plan.json> <branch0.json> ... [--out m.json]

Python API:

    boxlib.decode/encode/box_hash/box_str
    boxlib.widths/widest_dim/split_box/contains/interiors_overlap/volume
    boxlib.check_frontier(root, [(box, tag), ...]) -> (ok, reason, stats)
    plan_branches.make_plan(snapshot_path, deep=2) -> plan dict
    plan_branches.check_plan(plan, snapshot_path=None) -> (problems, snapshot)
    merge_branches.verify_branch(path, plan, plan_sha, problems_out) -> info | None
    merge_branches.merge(plan_path, branch_paths) -> manifest dict

## 3. What the merge verifies (all exact rational arithmetic)

For each branch file `evidence/parallel-domain/branch-N.json`:

1. `base_sha256` equals the stage-11825 snapshot hash; `worker_sha256` present;
   `branch_id` is a planned id; `branch_root` equals the planned root for that
   id (exact box equality, and `parent_pending_index` equals the plan's parent).
   The inherited `domain` field is never used.
2. Frontier = `leaves` (tagged atomic/infeasible) plus `pending` (tagged
   pending). The canonical widest-dimension bisection tree of `branch_root`,
   stopped at the frontier, must hit every frontier box exactly once and cover
   `branch_root` entirely. This single traversal certifies: containment in the
   root, no interior overlap, no hole, and canonicality (no non-canonical or
   unused box can survive: it would be either visited twice, left inside the
   root without being hit, or left over - all rejected).
   This is the precise form of "visited == frontier": the internal nodes of the
   traversal are exactly the canonical splits, and their count is compared with
   `counts.split`.
3. Counts consistency, matching the worker's DFS:
   `certified == #atomic leaves`, `infeasible == #infeasible leaves`,
   `pending == #pending`, `split == internal nodes of the traversal`,
   `processed == split + #(atomic+infeasible leaves)`.
   On the four branches available at the time of writing this holds exactly
   (branch 0: processed 20 = 12 splits + 8 leaves, etc.).
4. Cross-branch: no id twice (duplicate file rejected), no missing planned id,
   no unknown id, roots pairwise interior-disjoint, and total root volume equal
   to the total pending volume (checked in the plan step).

Merge arithmetic reported in the manifest (verified against the four existing
branches):

    processed   = 11825 (old) + 3 (parent-0 structural splits) + sum branch processed
    split       =  5916 (old) + 3 + sum branch split
    leaves      =  5909 (old) + sum branch leaves
    certified   =  5603 (old) + sum branch atomic
    infeasible  =   306 (old) + sum branch infeasible
    pending     =  sum branch pending          (old pendings are consumed)

With branches 0-3 only: processed 11908 = 11825+3+80, split 5967, leaves 5941,
certified 5634, infeasible 307, 20 pending boxes, volume equality TRUE, and the
only problem reported is the expected `missing branches: b04..b10`.
Leaves can never be duplicated because each branch root lies strictly inside a
distinct old pending box, and the old leaves lie strictly outside every pending
box (the old frontier is a canonical partition).

## 4. Audit of the worker's save/retry protocol

Findings on `lead/run_domain_branch.py` + `lead/hubline_domain.py` (read-only):

 * Both writes are atomic: `hubline_domain.save_state` writes
   `OUT.with_suffix('.tmp')` and then `os.replace`s it, and the worker's patched
   `save` does the same for the metadata version. No torn file can be observed.
 * The only transient state is a VALID state without the metadata fields: the
   sequence is (i) the worker's initial write of `{pending:[root],leaves:[],
   counts:...}` - no metadata; (ii) `original_save` writing the fresh state -
   no metadata; (iii) the patched `save` writing the state with
   `branch_id/parent_pending_index/branch_root/base_sha256/worker_sha256`.
   A merge attempted inside (i) or (ii) therefore sees a metadata-less file.
   `merge_branches.verify_branch` rejects it with
   `branch_root missing (metadata write window?)` instead of silently trusting
   a file whose root cannot be pinned - exactly the desired failure mode.
   Recommendation (matches the lead's plan): run the merge only after all
   workers have exited; alternatively retry until no branch reports the window.
 * `base_sha256` is the hash of the bytes of the stage-11825 snapshot as read at
   worker start, and `branch_root` is the exact box, so both are pinned by the
   plan's hashes; nothing depends on the inherited `domain`.
 * The worker loop stops when `pending` is empty (branch complete) or when
   `processed` fails to advance over a `run(20)` call (a stuck branch). A stuck
   branch leaves `pending` non-empty; the merge reports those boxes and keeps
   the manifest at `partial` - it never converts a stuck branch into a claim.
 * `run(20)` re-reads the branch file at each call, so the metadata fields are
   preserved across rounds and the counts are cumulative within the branch.

## 5. Negative tests (all pass)

`selftest_rejections.py` mutates a real branch file in a scratch directory and
confirms rejection for: missing `branch_root` (write window), swapped
`branch_root`, unknown branch id, leaf moved outside the root, dropped leaf
(coverage hole - detected as an un-reached canonical box), duplicated leaf,
tampered `counts.split`, the same branch supplied twice, and a torn JSON file.
Every case is rejected with a specific reason.

## 6. Launch protocol for the lead

   1. plan   : py -3 plan_branches.py plan <snapshot> stage11825-plan.json --deep 2
               (already frozen; sha256 above)
   2. workers: one process per id 0..10, writing
               evidence/parallel-domain/branch-<id>.json
               (the lead's existing run_domain_branch.py does this)
   3. merge  : after all workers exit,
               py -3 merge_branches.py stage11825-plan.json <all 11 branch files>
               -> merge-manifest.json; status becomes certified-full-domain only
               when there are no problems and no pending boxes remain.

No solver is started by anything in this directory, and no file outside
`members/structure/parallel-domain/` is written.

---

# FIXES (second revision; the first merge convention is withdrawn)

Four load-bearing defects were found in review and are fixed. Regression tests
live in `selftest_fixes.py` (all pass; the first convention is used nowhere).

1. **Pending count came from the wrong source.** The aggregate used
   `counts.get('pending', 0)`, but the worker's counts dict has no `pending`
   key, so an all-pending branch set produced `totals.pending == 0` and could be
   reported as `certified-full-domain`. The aggregate now sums
   `info['n_pending']` (frontier boxes tagged pending), and
   `assert agg['pending'] == len(final_pending)` guards it. The status is
   additionally gated on `len(final_pending) == 0` and on all planned branches
   being present.
   Test: 11 synthetic pure-pending branch files -> `status=partial`,
   `totals.pending=11`, no problems (the old code returned
   `certified-full-domain` here). Positive control: 11 synthetic fully-atomic
   branch files -> `certified-full-domain`, `certified = 5603+11`.
2. **The plan was not actually re-verified.** The old code only checked root
   disjointness and total volume. `merge()` now calls
   `plan_branches.check_plan(plan, plan.source.path)`: actual snapshot
   bytes/hash, every pending hash, each branch root contained in its parent,
   exact canonical widest-dimension refinement of every parent, cross-root
   interior-disjointness, volume identity.
   Tests: a plan with a tampered `source.sha256` is rejected with
   `plan: snapshot hash mismatch`; a plan with a tampered branch root is
   rejected with `plan: branch b05 root not inside pending 2`.
3. **Provenance/race on file hashes.** `verify_branch` and `load_plan` used to
   read the file, parse it, then hash the path again - two reads, so the
   recorded hash need not be the parsed bytes. Every file is now read once into
   `raw`; the parsed object and the reported `sha256` both come from those same
   bytes, and `load_snapshot` does the same for the snapshot.
   Tests: static check that no `BX.file_sha256(<path>)` call remains in the
   merge tool, plus a functional check that the reported hash equals the hash of
   the bytes.
4. **There was no merged manifest.** `--export` now writes a merged manifest in
   the ORIGINAL domain-manifest format (`status`, `domain`, `counts`, `pending`,
   `leaves`, `hashes`, plus an explicit `provenance` block) into this members
   directory. It refuses unless every structural check passed, copies the old
   snapshot's leaves verbatim and appends only the branches' own new leaves,
   copies the remaining pending boxes through, and forces `status='partial'`
   whenever pending boxes remain. The provenance block states that a
   full-domain claim still requires the atomic replay.
   Tests: export with missing branches is refused and writes nothing; the
   pending fixture exports with `status=partial`, 11 pending and the old leaf
   count unchanged; the atomic fixture exports with `certified full domain`,
   0 pending, old leaves + 11; no duplicate leaf boxes in the export.

Re-run on the four real branches available at the time of writing (new
convention): `status=partial`, `problems=['missing branches: b04..b10']`,
`totals.pending=6` (from the frontier: 1+2+1+2), `volume_equal=true`,
`processed = 11825+3+458 = 12286`, `split = 5916+3+230 = 6149`,
`certified = 5603+223 = 5826`, `infeasible = 306+5 = 311`. `--export` on the
same files is refused (b04..b10 missing) and writes nothing.

Nothing in this directory starts a process (no launcher, no background start),
so the Hidden/CREATE_NO_WINDOW requirement is not at risk here; the tools only
read the snapshot and the branch files and write inside this members directory.

## F3 completion (third revision) and legacy API marking

 * `plan_branches.check_plan` no longer calls `BX.file_sha256(spath)` before
   `load_snapshot(spath)`.  It calls `load_snapshot` exactly once and compares
   the plan's recorded hash with `snap["sha256"]`, which `load_snapshot`
   computes from the single `read_bytes` it parsed.  Instrumented check: 1
   `load_snapshot` invocation, 1 `read_bytes` of the snapshot, no other read of
   that path; verdict on the real plan: OK, no problems.
 * The legacy interface inside `plan_branches.py` is now explicitly deprecated
   and non-load-bearing in the module docstring and in each docstring, and both
   entry points emit `DeprecationWarning` when called: `verify_branch_output`
   (old output schema, ids `b00..b10`) and `merge` (summary-only, aggregated
   pending from counts), plus the module-global `plan_sha256` they used.
   `merge_branches` never calls them (verified statically).  The authoritative
   merge/export is `merge_branches.merge` / `merge_branches.export`.
 * Remaining `file_sha256` uses in live code are only in the `plan` subcommand,
   where the hash reported is that of the plan file just written; no live path
   hashes a path whose bytes it has already parsed.
