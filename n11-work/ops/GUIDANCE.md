# n11 formalization — supervisor guidance (Hark / architect)

Frozen goal (do not weaken): `∀ r c, 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r`
for Fin 11 centres, full closed unit disk, SAME C891 boxed root coordinate 6.

## Tree
- `n11-work/lean/` = 2026-10-14 public WIP snapshot + 2026-10-28 energy package overlay.
  Root `N11Formalization.lean` = stage-1 root (sha 9321A97F…) with two imports commented
  `-- HARK-MISSING` (C450ChainCompletion, C450ChainCompletionMain: not in public assets).
- Emitters / evidence: `n11-work/evidence-20261014/`, `n11-work/evidence-20261028/`
  (HANDOFF: `assets/replay/n11-wip/energy-stage1-20261028/HANDOFF.md` on main).
- CI: every push to `n11/work` touching `n11-work/lean/**` or `ops/BUILD_TARGETS.txt`
  runs `n11-lean-build` on GitHub Actions (4 cores / 16 GB, serial `lake build` of
  BUILD_TARGETS, ≤5 h, partial .lake/build cached). Results: `ops/ci/LATEST.md`
  (refreshed by the supervisor each cycle).

## Hard rules (from AGENTS.md / handoff — violations get reverted)
1. No `sorry`, `admit`, new `axiom`, `native_decide`, `Lean.ofReduceBool`, `implemented_by`
   tricks, radius replacement, symmetry weakening, or `maxHeartbeats 0`-style resource
   blowups on mathematics. Axiom report must stay `[propext, Classical.choice, Quot.sound]`.
2. Never edit frozen certificates/data modules in place; add new modules beside them.
3. Do not touch `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`.
4. Only the supervisor edits the root `N11Formalization.lean`. If your module should be
   root-imported, say so in your lane NOTES.md ("ROOT-IMPORT REQUEST: …").
5. A module counts as paid only after CI shows it built (exit 0) — never claim otherwise.
   Write "drafted", "CI pending", "CI green", "CI red" precisely.
6. Kernel-scale lessons (measured): no `decide +kernel` over `Finset.univ.image` unions;
   keep every kernel `decide` under ~170–500 literals; aggregate hierarchically via
   `Finset.card_biUnion` over `Fin k` families with pairwise disjointness facts.
   Read the error line, not the axiom report (`No goals to be solved` = red module).
7. Prefer generating Lean with deterministic Python emitters committed beside the output,
   with exact `Fraction` arithmetic and a self-check, over hand-writing large files.

## Local tools in the worker sandbox (aarch64, 2 cores, 7 GB — weak)
- `source /workspace/tools/env.sh` → python3, lean/lake v4.33.1, codex.
- `/workspace/tools/mathlib-probe/` = Mathlib-only Lake project (oleans cached). Use it to
  prototype tactics/lemma patterns (`cd /workspace/tools/mathlib-probe && lake env lean X.lean`).
  The full N11 project is NOT built locally — CI is the authority for project modules.

## Priorities (supervisor sets; re-read every session)
See LANES.md. Order of mathematical value: B (cheap, mechanical credit 815→1997) ≈ A
(restores C450 36/36 integration) > C (energy 389 residual) > SevenClassExclusions (0/7,
the real open analysis; scoping only until A/B land).
