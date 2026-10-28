# n11 energy handoff — 2026-10-28 (stage 1 complete, stage 2 packets complete)

**Scope: energy terminal credit only.** `SevenClassExclusions` untouched; the SAME
C891 `sourceRoot 6` arbitrary-center full closed-disk theorem is **NOT** made
unconditional here.

## 1. Counts

| quantity | before | after |
|---|---|---|
| energy terminals kernel-paid | 310 / 2386 | **815 / 2386** |
| energy remaining | 2076 | **1571** |
| C450 segments | 36 / 36 | 36 / 36 |
| sharp patches | 120 / 120 | 120 / 120 |
| Q0/Q1 class exclusions | 0 / 7 | **0 / 7** |

Root `lean/N11Formalization.lean` SHA256 **`9321A97F790D6DA2BFD5232A1761E0FDE92FD25DC0CFBEB77A067EC14406ED03`**
(previous `4F5FE148D74B36DC77A7D69F80C7D3BD816AA0F069768E8A98B98D08EEF179BC`).
Full root build exit 0, `10722 jobs`, `✔ [10721/10722] Built N11Formalization (23s)`.
Byte-exact copy of the integrated root: `evidence/N11Formalization-root-stage1.lean.bak`.

## 2. What was actually proved

505 of the 1687 HOST-passing candidate records that had **never** been emitted
(`paid16-general-next512.json`, included in `inputs/`) are now concrete
`Paid16CellCertificate.Packet`s whose `Valid` proof is
`constructor <;> decide +kernel` — the pre-existing checker, one field at a time.
`Valid` is a decidable proposition over exact rationals; it is not solver output
and no maximum is sampled.

New modules (all root-imported):

| module | content |
|---|---|
| `PaidBlock` | `Block` = (ids, terminality, strict radius bound) + `Block.union` |
| `Paid16GeneralH01..H24` | 21 packets each, `valid_i` by `decide +kernel` |
| `Paid16GeneralH25` | 1 packet (505 = 24·21 + 1) |
| `Paid16GeneralNext505` | literal-id aggregate, `new_count = 505`, `disjoint_paid`, `disjoint_sharp` |
| `EnergyTerminalBatchB12` | `paidIDs.card = 815`, `paid_radius`, residual over **1571** |
| `EnergyTerminalBatchB12Main` | `B12.RemainingTerminalRadius → SevenClassExclusions → N11MainStatement sourceRadius` |

Credit transfer: `EnergyTerminalBatchB12.remaining_of_b12 :
B12.RemainingTerminalRadius → EnergyTerminalBatchB11.RemainingTerminalRadius`.
A consumer of the old residual now needs only the strictly weaker new one.

## 3. Evidence

* Probe `lean/ProbeEnergyNext505.lean` (sha `A4C24CCF3A5D7CCD0D6C98E13AFD46A0785E3CFCCD3DBCB979473CF6C43E7C57`):
  exit 0, **30** axiom reports, **all exactly** `[propext, Classical.choice, Quot.sound]`,
  0 errors, `unchanged`. Log: `evidence/probe-stage1.log`.
* Three-arm matched pair (same probe bytes in all arms), `evidence/matched-pair-summary.json`:
  * **A** root import reverted, root **not** rebuilt → probe exit **0**, 0 `unknownIdentifier` (the stale-olean trap reproduces);
  * **B** reverted + root rebuilt → exit **1**, **42** `unknownIdentifier`;
  * **C** restored + rebuilt → exit **0**, 0.
* Independent exact-rational audit (python `Fraction`, no Lean): for **all 2027**
  records of `next512`+`rest1515`, `lower − gap = T²` **exactly** and
  `pass ⟺ gap > 0`, with `T = 1899919265599193545242591/5000000000000000000000000`
  = `FlashCosineLeaf284Bridge.T`. So the HOST `pass` flag *is* the `numeric` field
  of `Valid`, recomputed by a second implementation.
* Module SHA256 (full list in `MANIFEST.json`): `PaidBlock 88A8C607…`,
  `H01 E00F27F6…`, `H25 FC572BC1…`, `Next505 8F20BBBD…`, `B12 FF479557…`,
  `B12Main ED46AD05…`.

## 4. Two measured defects (carry these forward)

1. **Do not kernel-search an `univ`-image union.** The first aggregate defined
   `newIDs` as a union of 25 `Finset.univ.image nodeID` sets and asked
   `decide +kernel` for the cardinality: 7.5 GB RSS, 80 s CPU in 690 s wall, no
   progress in 11 min. A literal-id aggregate (no `univ`) elaborates in **108 s**.
2. **A module can be red with every theorem proved.** A trailing `norm_num` after
   a `rw` that already closed `paid_count` produced `No goals to be solved`
   (module exit 1) while all theorems had elaborated and printed clean axiom
   reports. Read the error line, not the axiom reports.
3. Kernel depth: `decide +kernel` on a >~600-deep `Finset` insert chain either
   hits `(kernel) deep recursion detected` (1182 did) or, with
   `maxRecDepth 10000`, thrashes (7.3 GB, ~15 % CPU). 505 is fine.
   **Above ~500 ids, aggregate hierarchically** (`Finset.card_biUnion` over a
   `Fin k`-indexed family, or sub-aggregates whose every `decide` sees ≤ ~170
   literals).

## 5. Stage 2 (packets done, dispatch pending)

`rest1515` (1182 more HOST-passing records) is emitted and **kernel-checked**:

* `Paid16GeneralH26..H82` — 57 modules, **57/57 exit 0**
  (`evidence/progress-rest1182H.txt`);
* `Paid16GeneralNext1182S01..S08` — 8 sub-aggregates, **8/8 exit 0**, each with an
  exact sub-cardinality, `new_terminal`, `new_radius`, `disjoint_sharp`
  (`evidence/progress-hier.txt`).

**Not done (deliberately, no half-claims):** the *top* union of the eight
sub-aggregates and `EnergyTerminalBatchB13`. The top module was generated but did
not finish: its cardinality/disjointness steps compared one sub-aggregate against
the remaining 7-sub union (a 1176-deep chain) and thrashed. Drafts of the top and
of `B13` are **not** in this package and were moved out of `srcDir`.

Next executable step (exact):

1. Rebuild the top as `newIDs := Finset.univ.biUnion part` with
   `part : Fin 8 → Finset (Fin 5011) := ![S01.newIDs, …, S08.newIDs]`;
   `new_count` by `Finset.card_biUnion` with the 28 **pairwise** `decide +kernel`
   disjointness facts (each ≤ 168×168 literals); dispatch by `mem_biUnion` +
   `fin_cases`.
2. `EnergyTerminalBatchB13`: `paidIDs := EnergyTerminalBatchB12.paidIDs ∪
   Next1182.newIDs`, `paid_radius`, `RemainingTerminalRadius` over **389**, and
   `remaining_of : B13.Remaining → B12.Remaining`.
3. Root import + root build + a stage-2 probe (`lean/ProbeEnergyRest1182.lean` is
   included) + the same three-arm matched pair.
   Open sub-obligation: exact `paidIDs.card = 1997` needs
   `Disjoint B12.paidIDs Next1182.newIDs` in the kernel. The two id sets are
   **not** interval-separable (B12 goes up to 4485, rest1182 starts at 2565), so
   it is a real element-wise check (815 × 1182 ≈ 0.96 M comparisons at depth
   815+1182) — the one place a `maxRecDepth` bump plus a long kernel run may be
   unavoidable. Exact python set comparison: **0 overlap**.

## 6. Remaining energy residual after both stages: 389

Authoritative HOST census (`paid16-complete-host-census.json`,
`remaining_after_all_host_proposals_if_kernel_paid = 389`) decomposes it as
**354 method failures + 35 outside-census zero-dual ids**. By record presence:
340 near-miss records + 49 no-record ids. Near-miss deficits are tiny — worst
`|gap| = 6.80·10⁻⁵`, **240/340 within 10⁻⁶** of `T²` — and failure supports
concentrate on a handful of dual rows (`(211,210,264,297,298)` alone: 49).

Why the format is saturated, and which knob is cheap:
`DBMMinorantDual.lower w s c n rows lam rmin = f0Lo w s c − lamB n rows lam + rmin`
with `lamB n rows lam = Σ_a lam a · db(n, rowFrom a, rowTo a)`. In the failing
records `rmin ≈ −10⁻¹²` while the deficit is `10⁻⁷…10⁻⁵`, so the miss is in
`f0Lo − lamB`, not in `rmin`.
`CertifiedFieldMixtures.radius_of_dual {n m : ℕ}` is already generic in both the
mixture size `n` and the dual-row count `m`; only the concrete
`Paid16CellCertificate.Packet` hard-codes `Fin 16` fields / `Fin 7` rows.
**Raising the row cap is therefore a data-structure + re-emission job, not new
analysis**; adding mixture fields needs new harmonic field candidates
(`evidence/codex-handoff/harmonic-fields-b01-proposal.json`, `-b02-` are leads).

## 7. Reproduction

All Lean calls go through the project's single global mutex wrapper
(`Invoke-LeanSerial20261013.ps1`); never run Lean unlocked. The emitters are
deterministic and hash-guarded:

```
python emit_paid16_general_next505.py --all        # 29 modules from the frozen proposal
pwsh  build-modules.ps1 -List next505-list.txt -Tag next505mods
python emit_aggregate_cheap.py --manifest=next505-emission-manifest.json \
       --aggregate=Paid16GeneralNext505 --tag=next505 \
       --base=EnergyTerminalBatchB11 --count=505
pwsh  build-modules.ps1 -List agg505-list2.txt -Tag agg505b
pwsh  build-modules.ps1 -List b12b-list.txt     -Tag b12b
python patch_root.py <cur-root-sha> N11Formalization.EnergyTerminalBatchB12Main \
       root-import-stage1.txt
pwsh  build-modules.ps1 -List root-list.txt     -Tag root1
pwsh  run-matched-pair2.ps1
```
`inputs/paid16-general-next512.json` (sha256 `F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16`)
plus the two emitters regenerate every Lean file in
`n11-energy-sources-20261028.tar.gz` byte-exactly; the tarball also pins each
member's SHA256 in `MANIFEST.json`.
