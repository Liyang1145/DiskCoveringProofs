# n=11 formalization continuous loop — runbook
Target: pay the three open Props of the team WIP (wip/lean, Lean v4.33.1, Mathlib 0df444a3…):
  h450 = C450Source11Segment.RemainingSourceObligation
  henergy = EnergyTerminalBatchB11.RemainingTerminalRadius
  h33 = ActualMainRoute.Canonical33Obligation (or SevenFiniteTables)
so that ActualMainRoute.main_of_remaining yields N11MainStatement SourceExactRoot.sourceRadius with no sorry, axioms only propext/Classical.choice/Quot.sound.
Read STATUS.md (full map) and wip/assets HANDOFF (src/HANDOFF.json) first.

Lines (each owns its own dir; never edit another line's dir):
- build  : ci/ (GitHub Actions, since 2026-10-15 16:19 CST) — the WIP+Mathlib build runs ONLY in CI on branch ci/n11-build of Liyang1145/DiskCoveringProofs (see ci/README.md). wip-build/ (local Mathlib attempts) is retired: the sandbox cannot import Mathlib.
- energy : energy/      — C921 energy terminals: verify 1687 candidate routes exactly, produce certificates for the 389 that need new ones; emit Lean in WIP style.
- class  : class33/     — nine-switch aggregation + SwitchCertificate bridge; two q1-balanced representative tables; seven class tables / Canonical33Obligation.

Discipline:
- Never count anything paid unless compiled green (WIP toolchain) with axiom audit; core-Lean/Python checks are pre-validation only and labelled so.
- Write atomically (tmp+rename), checkpoint per item, resumable drivers, append ledgers (<line>/ledger.jsonl).
- 2 CPUs / ~7 GB RAM shared: nice -n 10 for bulk jobs; NO local Mathlib Lean process (it does not fit; use CI); check `free -g` before heavy steps.
- Background shell jobs ≤ 1150 s per segment.
- GitHub: pushes ONLY to branch ci/n11-build of Liyang1145/DiskCoveringProofs (user-approved 2026-10-15), content under ci-n11/ + .github/workflows/n11-*.yml. Never push main, never open PR/issue/comment, no other repo.

CI step of every loop turn (build line):
  1. `python3 ci/mon.py` (shell, credentials github). Note run ids / statuses `n11/<track>` in ci/ledger.jsonl when a run completes.
  2. Completed chunk/run: `python3 ci/mon.py art <run_id>`; read results-*/<track>-c<k>.jsonl (failed modules), *-audit.jsonl, logs/*.log.gz (zgrep -A30 '✖' for errors).
  3. Draft failures (energy/class/telescope): fix the source in its line dir (energy/lean-wip, class33/lean, wip-additions), re-copy into ci/repo/ci-n11/drafts/..., push (recipe in ci/README.md) → the track's workflow re-runs (energy/class cancel the running one; lake resumes from cache). Team-module failures: record only (never edit wip/lean).
  4. A track that stopped before finishing (all chunks used, done=false): re-run with workflow_run_rerun (resumes from cache).
  5. Credit: move a module to "Paid" in LOOP_STATE only if CI built it green (no sorry) AND the audit row of its aggregator is ok, citing the run id.
- If an approach loops twice without progress, record it in LOOP_STATE blockers and pick the next queue item.

Core-Lean toolchain recipe (after container restart; / is RAM-backed, keep it small):
  mkdir -p /var/tmp/lean && cd /var/tmp/lean && tar --zstd -xf /workspace/work/toolcache/lean-4.33.1-linux_aarch64.tar.zst --wildcards 'lean-4.33.1-linux_aarch64/bin*' 'lean-4.33.1-linux_aarch64/lib/lean/*' --exclude='*.ilean' --exclude='*.a' --exclude='*/Lake*'
  (needs Init/Std/Lean .olean AND .ir files; deleting .ir breaks codegen; ~2.2 GB). Then class33/drive2.sh (list data/core_modules_v2.txt, oleans /tmp/c33).
Core-Lean parts must stay ≤100 leaves / 25-leaf chunks (300-leaf parts OOM at ~2 GB free).
