# n=11 WIP — GitHub Actions CI (build line moved here, 2026-10-15)

**Where:** repo `Liyang1145/DiskCoveringProofs`, branch **`ci/n11-build`** only (user-approved 2026-10-15 16:xx CST,
instead of a new repo: Hark's GitHub app cannot create repos — `POST /user/repos` → 403 "Resource not accessible by integration").
Everything lives under `ci-n11/` plus `.github/workflows/n11-*.yml` on that branch.
**Never** push to `main`, never open a PR / issue / comment. Branch base = main @ `294f644`.
Actions page: https://github.com/Liyang1145/DiskCoveringProofs/actions?query=branch%3Aci%2Fn11-build

## Local mirror of the branch content
`ci/repo/` = exactly the files committed on the branch (`ci-n11/…`, `.github/workflows/n11-*.yml`).
`ci-n11/lean/` = `wip/lean` unmodified; `ci-n11/drafts/{energy,class33,telescope}/N11Formalization/*.lean` = copies of
`energy/lean-wip/N11Formalization`, `class33/lean/N11Formalization`, `wip-additions/C450FullTelescope.lean`.
**Source of truth for drafts stays in the line dirs**; re-copy into `ci/repo/ci-n11/drafts/...` before each push.

## Workflows (push-triggered; workflow_dispatch can't be used because the files are not on the default branch)
| workflow | triggered by changes under | track content | concurrency |
|---|---|---|---|
| `n11-main.yml` | `ci-n11/lean/**`, `ci-n11/drafts/telescope/**`, `ci-n11/tools/**`, `n11-chunk.yml` | A = accepted A25 root (788 root imports → 1,134 modules), B = C450 Source12/13 pilot (68), C = Source14..36 (782), D = `C450FullTelescope` | queue (no cancel) |
| `n11-energy.yml` | `ci-n11/drafts/energy/**`, tools | energy-matrix, energy-paid16 (H001..H083, HAgg, HAll, B12), energy-refine (57 EnergyRefineN*, Agg, All, B13) | cancel-in-progress |
| `n11-class.yml` | `ci-n11/drafts/class33/**`, tools | class-core, class-switch (18), class-face (33), class-asm (4) | cancel-in-progress |

Each track is a chain of ≤6 h chunk jobs (`n11-chunk.yml`; main 8, energy/class 3). A chunk: free disk, 12 GB swap,
elan, restore `ci-n11/lean/.lake/build` from actions/cache (key prefix `n11-<track>-`, newest wins), `lake exe cache get`,
`tools/chunk.sh` (copies drafts into the tree, then `tools/sched.py` builds the union of the track's group closures
with a deadline 300 min after job start). sched.py = memory-aware scheduler (≤4 workers; `lean -R . -o/-i` into
`.lake/build/lib/lean`, LEAN_PATH from `lake env`; stamp = sha256(source + import stamps) in `<mod>.n11stamp`, failed
stamps in `<mod>.n11fail` (not retried until the source changes); under MemAvailable < 1.5 GB kills the youngest job and
requeues it solo). `lake build` was dropped after run 1: 4 parallel heavy Lean processes killed the runner., axiom audit (`tools/audit.py`) of whatever compiled, upload artifact `results-<track>-c<k>`,
save cache. A chunk that finished all groups sets `done=true`, the later chunks then skip in seconds.
`summary` job → artifact `summary-<track>` (merged per-module table + audit) and the run's step summary.
Existing team workflows `delivery-bytes.yml` and `math-checks.yml` also fire on every push to the branch (they
trigger on all pushes); their result is irrelevant to this build — ignore them. Left untouched on purpose.

## How to trigger
Push a commit to `ci/n11-build` touching the track's paths (e.g. a fixed draft). Re-run without changes:
`curl -X POST $API/actions/runs/<id>/rerun` (or apicall github workflow_run_rerun). Cancel: workflow_run_cancel.
Push recipe (sandbox, credentials github): partial clone, add on top of the branch head:
```
git clone -q --depth 1 --filter=blob:none --no-checkout --single-branch --branch ci/n11-build https://github.com/Liyang1145/DiskCoveringProofs.git /tmp/dcp
cd /tmp/dcp; export GIT_INDEX_FILE=/tmp/dcp-index; git read-tree HEAD
git --work-tree=/workspace/work/dcp-n11-lean/ci/repo add ci-n11 .github/workflows/n11-*.yml   # only changed files get new blobs
T=$(git write-tree --missing-ok); C=$(git commit-tree $T -p HEAD -m "...")
git push origin $C:refs/heads/ci/n11-build
```
(Working in /tmp: `git add` on JuiceFS of 2,600 files times out; with the tar copy to /tmp/stage it takes ~3 s.)

## How to read results
`python3 ci/mon.py` (shell with github credentials): runs, jobs, current step, failed steps, live commit statuses
`n11/<track>` ("c<k>: ok/total (new), failed, blocked [first failures]") and `n11/<track>/diag` (MemAvailable, running
modules with minutes and RSS), every 10 min by `tools/report.sh`, posted on the run's commit sha.
`python3 ci/mon.py log <job_id>` — tail of a finished job's log. `python3 ci/mon.py art <run_id>` — download artifacts
to `ci/artifacts/<run_id>/` (`results-*/<track>-c<k>.jsonl` per module: status built|cached|failed|blocked, seconds, peak_rss_mb, sorry;
`*-groups.jsonl` sched rc per chunk (0 = all final, 3 = deadline); `logs/mod/<module>.out` for failed/warning modules; `*-audit.jsonl` axioms per constant; `logs/*.log.gz` raw lake output).
`ci/ledger.jsonl` — one row per CI run we triggered (append).

## Credit rule
Paid only if: module built green in CI (status built/replayed, no `sorry` warning) **and** the audit of its aggregator
constant shows axioms ⊆ {propext, Classical.choice, Quot.sound}. Cite the run id.
