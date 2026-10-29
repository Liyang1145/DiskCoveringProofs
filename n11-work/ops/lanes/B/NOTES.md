EXPERT (2026-10-29):
- Next1182 design is sound; current red is mechanical, not mathematical.
- In part_s01..part_s07 bounds, use `have hb := block_*_bounds n h_*; exact ⟨hb.1, le_trans hb.2 (by norm_num)⟩`; keep s08 direct.
- Remove trailing `norm_num` after the `simp` in `new_count` (CI line 546 No goals).
- Build only Paid16GeneralNext1182 first; then B13; no B13Main/1997 claim until both green and root-imported.
- Pre-split B13 `b11_lt`/`next505_lt` full-set decide+kernel into ≤21-literal blocks before trusting B13.
- Keep TARGETS to Next1182 + B13.

SUPERVISOR (2026-10-29): TARGETS remain Next1182 + B13 until both are CI-green; B13Main and ResidualCensus stay out; do real work, do not poll Actions.

# Lane B notes

## 2026-10-29 - session part 5: hierarchical B13 lower-bound proof

### Done
- Replaced B13's monolithic 310-element `b11_lt` kernel decode with
  `b10_lt` (100-element B10 set), `remaining210_lt` (210-element G03--G12
  union), and a union dispatch. This follows the recorded CI-timeout risk and
  leaves each new decode at or below the measured safe range.
- Re-read `Paid16GeneralNext505` and retained its existing 505-element
  `next505_lt`; a recursive 25-chunk replacement is the next refinement if CI
  still times out there.

### Files (SHA256)
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13.lean`
  `7C73BD67377D1F72B920439F20C7F81D51EAD063EA20A61395EC8E4362758DFC`

### Checks executed (scope)
- `git diff --check` exit 0; forbidden-token scan over B13 exit 0. Static
  source inspection only. No local project build was started; CI remains the
  only project kernel authority. Both targets remain CI pending / unpaid.

### Still unproved / unverified
- Next1182 and B13 have no CI verdict on current bytes. B13 cardinality and
  transfer, residual census 389, B13Main, `SevenClassExclusions`, and the
  arbitrary-center full-disk theorem remain unverified.

### Next concrete step
- On the next CI run, quote the first genuine Next1182 error. If both existing
  targets exit 0, update the root-import request; otherwise split
  `next505_lt` recursively across `Paid16GeneralNext505.ids00`--`ids24`.

## 2026-10-29 - session part 43: removed redundant `norm_num` in `new_count`

### Done
- Re-read CI run `40893868710` (sha `495c970c`, source 648 lines) against the
  current WT source. Besides the 126 now-fixed part-bound `Type mismatch`
  lines, `new_count` had two independent errors: `590:75 unsolved goals`
  (the `hdisj` block, cascading because the 28 disjoint lemmas failed) and
  `603:2 No goals to be solved` (the trailing `norm_num`).
- Local Mathlib probe `/workspace/tools/mathlib-probe/LaneBCountProbe.lean`
  reproduces the exact `new_count` shape with 8 `Icc` parts and 28 `Disjoint`
  lemmas. It compiled exit 0 (~4.5 min, Mathlib import dominated): the
  `fin_cases i <;> fin_cases j <;> simp_all [part, d01, ...]` hdisj pattern is
  valid, and `simp [Fin.sum_univ_succ, part, c01, ...]` alone closes the
  cardinality goal. Hence the trailing `norm_num` is genuinely redundant.
- Removed `lines.append("  norm_num")` from `emit_next1182_top.py` after the
  `new_count` `simp`, regenerated the module. Part-42 `have hb := ...; omega`
  composition retained.

### Files (SHA256, uppercase)
- `n11-work/lean/N11Formalization/Paid16GeneralNext1182.lean`
  `73FE3DA40C7CE0B1F9D7703EACECD6739D388A4297E7FAA1735203D675248B76`
- `n11-work/ops/lanes/B/emit_next1182_top.py`
  `4EB412D623899EC2D08696A9E81102EFA2E7CB4EA2FC06486DC6992C20F9A827`
- `n11-work/ops/lanes/B/emit_next1182_top-report.json`
  `0438CDCA939DBB7FB75C2F9622A287081EB9C3503D5F6E407116D13328F23718`
- `n11-work/ops/lanes/B/audit_next1182_blocks-report.json`
  `01F84D3F5CE3E50B3D393589E00C68E2CF0BF3CFA84DE7F652A93AC6A6E9E70B`
- `EnergyTerminalBatchB13.lean` unchanged
  `B4F556F05B8C4D0618C8287094AFB14AD7DF494DD999567F83C6CF4B20EC5096`;
  `TARGETS.txt` unchanged `D0572BD0...` (targets Next1182 + B13).

### Checks executed (scope)
- Emitter rerun wrote 37,355 bytes, sha `73FE3DA4...`; audit exit 0 with 1182
  ids, parts `168x7 + 6`, 57 literal-block theorems, 28 interval-disjointness
  theorems, 0 top-level kernel decodes.
- `py_compile`, `git diff --check`, forbidden-token scan pass (only expected
  `#print axioms` lines match "axiom").
- Probe check is a Mathlib-only analogue, **not** project elaboration. No local
  project build was started; CI remains authoritative.

### Still unproved / unverified
- Next1182 and B13 remain **CI pending / unpaid**. The part-42 `omega`
  composition and the `new_count` change have no project Lean verdict yet.
  B13Main, residual census 389, `SevenClassExclusions`, and the arbitrary-center
  full-disk theorem remain unverified.

### Next concrete step
- On CI for sha `73FE3DA4...`: if Next1182 exits 0, inspect B13's first
  independent error; if not, quote the first error line only. Do not expand
  TARGETS or claim payment until both targets exit 0.

## 2026-10-29 - session part 40: patched CI timeout in Next1182 block bounds

### Done
- Read CI run `40861839784`: `Paid16GeneralNext1182` is red at the former
  `Finset.all_eq_true.mp ... (by decide +kernel)` block proof; Lean reports a
  200000-heartbeat tactic timeout and a dependent `whnf` timeout. B13 exits 1
  through its Next1182 dependency; no independent B13 error is present.
- Replaced all 57 block proofs by elimination of the imported
  `mem_idsNN` literal disjunction followed by `all_goals norm_num`. This removes
  every top-level kernel `decide`/`Finset.all` reduction while retaining the
  literal interval bounds. Emitter and audit were updated accordingly.

### Files (SHA256, uppercase)
- `n11-work/lean/N11Formalization/Paid16GeneralNext1182.lean`
  `F78988D46502FD1F6F147863C4DE8CF6C74E1243B185ED6757799AC4308A0FE8`
- `n11-work/ops/lanes/B/emit_next1182_top.py`
  `85B0D5BCD1FCFD7BD320027BEC07810E89ABD8CA3285CE624907E85891992F32`
- `n11-work/ops/lanes/B/audit_next1182_blocks.py`
  `F8DE4080AD0B7CB76A6657CDD4268160C77ABF6E973F6018BBB1519512EF159F`
- reports: emitter `60D2066ED85AFE7F4FF273A40953B9A4CC9A3CA7D07840D9E56E3F799037C6CF`; audit `78C7BEEE62979E0BAA9059B374825254E06DFC56429862F9A8F665CBCE933577`.
- `EnergyTerminalBatchB13.lean` unchanged
  `B4F556F05B8C4D0618C8287094AFB14AD7DF494DD999567F83C6CF4B20EC5096`.

### Checks executed (scope)
- `py_compile`, emitter rerun, `audit_next1182_blocks.py`: exact 1182-id
  inventory, part sizes `168x7 + 6`, 57 block theorems, 28 interval
  disjointness theorems, 57 membership-disjunction proofs, zero top-level
  kernel decodes; `ok`. `git diff --check` and forbidden-token scan passed.
- This is source/manifest inspection only, **not Lean elaboration**. The new
  `norm_num` block pattern has no kernel verdict yet. A bounded Mathlib probe
  of the exact 21-way `rcases` + `all_goals norm_num` pattern
  (`mathlib-probe/LaneBMemNormProbe.lean`, `timeout 180`) timed out during
  import and supplied no verdict. No local project build was started.
  Next1182/B13 remain **CI pending**, now with a new top SHA.

### Still unproved / unverified
- Next1182 and B13 remain unpaid. B13 1997-cardinality and radius transfer,
  B13Main, census 389, `SevenClassExclusions`, and the arbitrary-center
  full-disk theorem remain unverified/unpaid.

### Next concrete step
- On the next CI run quote the first genuine error in Next1182. If the
  `mem_idsNN` + `norm_num` blocks pass, diagnose B13's first independent error;
  otherwise patch only the first failing block line. Keep TARGETS at Next1182
  and B13 and make no payment claim until both build.

## 2026-10-29 - session part 39: bounded `Finset.all` block checks

- Briefly replaced each 21-id block bound by one bounded `Finset.all` kernel
  check. CI then reported a tactic timeout at the first such check, so part 40
  superseded this design. The old top SHA was `00EF2A6C…33325`; it has no
  surviving role. Inventory stayed 1182 ids (`168x7 + 6`).

## 2026-10-29 - session part 38: reproducible regeneration + isolated kernel idiom probe

### Done
- Re-ran `emit_next1182_top.py` and `audit_next1182_blocks.py` after `py_compile`.
  Regeneration reproduced exactly 1182 ids, part sizes `168x7 + 6`, eight
  increasing/disjoint bounds, 57 literal-block lemmas (maximum 21 ids), 28
  interval-disjointness lemmas, and top SHA256 `26F316A8...583F6F`; audit `ok`.
- Ran `git diff --check` and forbidden-token scan on all Next1182 modules and
  the emitter. The only `maxRecDepth 10000` occurrence is the emitter's report
  text documenting its removal; no forbidden proof token is in Lean source.
- Started an isolated Mathlib probe of the exact `Finset.all` + `decide +kernel`
  + `Finset.all_eq_true.mp` idiom over a five-literal `Finset (Fin 5011)`.
  Probe source: `/workspace/tools/mathlib-probe/LaneBAllProbe.lean`.
  Local `timeout 90` did not finish within the observation window (Mathlib
  import cost on this weak sandbox), so it has **no verdict**; this is not a
  project build.

### Checks executed (scope)
- Full regenerate + static exact inventory audit (source/manifest inspection,
  not Lean elaboration). `git diff --check` and token scan passed.
- Existing CI `40861839784` predates this edit; Next1182 remains **CI pending**
  and is not paid.

### Still unproved / unverified
- Next1182 1182-cardinality/radius/terminal transfer and B13 1997-cardinality,
  radius transfer, B13Main, residual census 389, `SevenClassExclusions`, and
  the arbitrary-center full-disk theorem all remain unverified/unpaid.

### Next concrete step
- Quote the first genuine error from the next CI run for
  `Paid16GeneralNext1182`; patch only that error. If green, do the same for
  `EnergyTerminalBatchB13`, then update the root-import request. Do not add
  TARGETS before both are green.

## 2026-10-29 - session part 37 (condensed)
- Replaced 57 `rcases`/`all_goals omega` block bounds by one
  `Finset.all` kernel check per block (<=21 literals); removed
  `maxRecDepth 10000` from S01..S08. Audit script rejects its return.

## Earlier progress (condensed)
- Sessions 35--36 split the former 168-case bound proof into eight parts and
  57 literal blocks after CI timeout at 200000 heartbeats; later parts replaced
  those tactics by literal membership elimination plus `norm_num`.
- Session 16 reproduced `2506 terminals - 120 sharp - 1997 paid = 389`, with
  literal chunks 100/100/100/89. This is arithmetic inventory, not proof.
- Session 30 audited conditional `EnergyTerminalBatchB13Main.lean` statically;
  it remains outside TARGETS and has no kernel verdict.

## Retained engineering facts
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.
- `Finset.card_biUnion` takes disjointness explicitly:
  `Finset.card_biUnion hdisj`; `Fin.sum_univ_succ` expands the eight-term sum.
- B11 straddles 2565. If CI rejects B13, split B11 into B10 plus G03--G12
  instead of assuming an interval.
- `Finset.disjoint_left.mp` needs `(a := a)` in generated proofs.
- Emitters: `emit_next1182_top.py`, `emit_residual_census.py`. The former now
  emits literal-membership block proofs with no top-level kernel decodes.
- Mathlib probes can give tactic verdicts (`LaneBCountProbe.lean`, part 43);
  CI remains the only Lean-build authority for project modules.

## 2026-10-29 - session part 4 (same slot): post-CI source inspection

### Done
- Confirmed `n11-work/ops/ci/LATEST.md` run `40893868710` (sha `495c970c`)
  predates the part-43 rewrite: its `Paid16GeneralNext1182` errors are the 126
  old part-bound `Type mismatch` lines plus `590:75 unsolved goals` and
  `603:2 No goals to be solved`. The current worktree source (647 lines, sha
  `73FE3DA4...`) has literal `have hb := block_...; omega` part bounds and no
  trailing `norm_num`, so those exact errors are not evidence against it.
- Verified part/block inventory consistency in the current source: 57 block
  lemmas, S01--S07 have 8 blocks each, S08 has 1 (`rcases ... with h0`), and
  all 28 pairwise disjointness lemmas use part bounds, not kernel decodes.
- Inspected `EnergyTerminalBatchB13.lean` (129 lines) end to end: `paidIDs`,
  `new_disjoint_old` (B11/Next505 split), `paid_count = 1997`,
  `paid_not_sharp`, `paid_radius`, `remaining_of_b13` shapes are internally
  consistent with B12 and Next1182 exports.

### Risk identified (not fixed)
- B13's `b11_lt` does a single `decide +kernel` over the whole 815-element
  `EnergyTerminalBatchB11.paidIDs`, and `next505_lt` over 505 elements. This
  is above GUIDANCE's measured ~170--500-literal kernel-decode range and is
  the most likely next CI timeout. A hierarchical replacement must recurse
  through B11→B10→B09→...→B01 (each `paidIDs` is `previous ∪ smallBatch`).

### Checks executed (scope)
- Static source/CI-log inspection only; no local project build, no Lean
  elaboration of the current source. Both targets remain CI pending / unpaid.

### Next concrete step
- Replace `b11_lt` by a recursive per-batch bound: prove a chain of lemmas
  `EnergyTerminalBatchBk.paidIDs ⊆ {n | n.val < 2565}` down through B01 using
  each `new_disjoint_old`/`paidIDs` definition, then combine. Do this before
  asking CI to re-run B13.
