# ci-n11 (branch `ci/n11-build` of Liyang1145/DiskCoveringProofs)

GitHub Actions build of the n = 11 disk-covering Lean 4 formalization **WIP** (team snapshot) plus
draft modules. Nothing here is accepted mathematics by itself; a module counts only if it compiles
green in CI **and** its axiom audit shows only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

Lives only on branch `ci/n11-build` (never merged into `main`). Layout below is relative to `ci-n11/`.

* `lean/` — the team WIP project **unmodified** (restored from release `proof-assets-core-20261014`,
  `n11-wip-0001.zip`, 2383/2383 files hash-verified). Toolchain `leanprover/lean4:v4.33.1`,
  Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
* `drafts/` — added draft modules, copied into `lean/N11Formalization/` by CI (never overwriting a team file):
  `energy/` (Paid16GeneralH*, HAgg*, HAll, EnergyTerminalBatchB12/B13, EnergyRefine*, Paid16MatrixCellCertificate),
  `class33/` (Class33*), `telescope/` (C450FullTelescope → `h450`).
* `tools/` — target lists (`targets/`), audit lists (`audit/`), `chunk.sh` (one resumable build chunk),
  `parse_lake_log.py`, `audit.py`, `report.sh` (progress as commit statuses), `summarize.py`.
* `.github/workflows/n11-{main,energy,class}.yml` (+ reusable `n11-chunk.yml`) — triggered by pushes to
  `ci/n11-build` touching that track's paths; three tracks run in parallel:
  `main` (A = accepted A25 root closure, B = C450 Source12/13 pilot, C = Source14..36, D = telescope),
  `energy`, `class`. Each track is a chain of ≤6 h chunks; `lean/.lake/build` is carried between chunks and runs via
  `actions/cache` (lake is incremental). Per-chunk artifacts `results-<track>-c<k>` hold per-module JSONL,
  raw lake logs and axiom audits; the `summary` job merges them (artifact `summary-<track>`). Live progress: commit status `n11/<track>` on the pushed commit.
