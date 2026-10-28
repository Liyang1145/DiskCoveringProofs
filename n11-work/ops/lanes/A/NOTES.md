# Lane A notes

## 2026-10-28 — C450 telescope reconstruction drafted

**Did.** Reconstructed the two public-assets-missing modules from the existing
kernel-checked source telescope:
- `n11-work/lean/N11Formalization/C450ChainCompletion.lean`
- `n11-work/lean/N11Formalization/C450ChainCompletionMain.lean`
- deterministic emitter: `n11-work/ops/lanes/A/emit_chain_completion.py`

`C450ChainCompletion.source36_remaining` proves the vacuous `drop 36` obligation.
`h450` then applies all 25 transfer declarations
`C450Source12Segment.source11_remaining_of_remaining` through
`C450Source36Segment.source35_remaining_of_remaining`, yielding exactly
`C450Source11Segment.RemainingSourceObligation`.  It also exposes
`source_obligation`, `c450_atom`, `card_boundaryIdx_eq_nine`, and
`exists_covers_ringLabels`.  `C450ChainCompletionMain` sends this `h450` to
`ActualMetricClassReduction.main_of_seven_class_certificates` under the expected
name `main_of_energy_and_seven_classes` (B11 energy residual + seven classes).

**Checks executed (scope stated).**
- `python tools/project_status.py --check`: PASSED for the handoff index/manifest
  declarations only; explicitly not a math or full-byte audit.
- Static telescope audit: PASS, 25 declarations/types present for Source12..36
  and 25 ordered applications in the generated nested term.
- Core Lean check of the two empty-list proof patterns: exit 0 (plain Lean,
  generic `List Nat`; not the project modules).
- Forbidden-token scan over the two new Lean modules: no hits.
- No full project build attempted locally; CI is the kernel authority.
- `/workspace/tools/mathlib-probe` was unusable this session because its shared
  `importGraph` checkout had a stale `.git/index.lock`; no shared-tool files were
  modified.

**Hashes (SHA256).**
- New `C450ChainCompletion.lean`: `51f6b8417ef69b8c0e8c8b24c96e22cc30c470b1058c81726260580b658c5181`
- New `C450ChainCompletionMain.lean`: `942dd90f69781a7ce1d57c5a393c3c11626cfe4135b30c5834fb2656ca3b6c03`
- Emitter: `f806b5c83eb343f7b93544fe0937f98adf3e4a0303a5244ea91aa416e04a6db0`
- Input telescope boundary `C450Source12Segment.lean`: `fc49c02543a23a1f71543486d931fe73197b7af4e9b21c41d7b678f65ff261eb`
- Terminal `C450Source36Segment.lean`: `85c9d33fb9eb275720a5af73adfc9824dfb73cc37fe2a9492e1f25514662dfbb`
- Interface `C450NormalizedInterface.lean`: `56990750e9557d61036864bee4806299f02771949227a46e7506597964a60650`
- Consumer `ActualMetricClassReduction.lean`: `4c6b872adbd37a812898a80c39decf1cb500937a6e79a695d06f6fc3320c8936`

**Status.** DRAFTED, CI PENDING.  Neither module is paid until `n11-lean-build`
returns exit 0.  The mathematical obligations left unpaid by the repository
(energy terminal residual and all seven class exclusions) are unchanged; this
work only removes the C450 `h450` premise.

**ROOT-IMPORT REQUEST:** replace the two `-- HARK-MISSING` lines near
`N11Formalization.lean:1952` with imports of `C450ChainCompletion` and
`C450ChainCompletionMain`.  Lane A targets are listed in
`n11-work/ops/lanes/A/TARGETS.txt`.

**Next concrete step.** Inspect the first CI build of the two targets.  If green,
request/perform the supervisor-owned root re-import and a root build; if red,
fix the reported elaboration error before touching root.
