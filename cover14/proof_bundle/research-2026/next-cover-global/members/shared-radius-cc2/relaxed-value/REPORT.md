# Relaxed-value diagnostic — **QUARANTINED / WITHDRAWN**

## 0. QUARANTINE BANNER (read before anything else)

This report did **not** complete the assigned instrument. All `relaxed-value`
conclusions are **withdrawn as implementation / inference failure**. The lead has
closed the task; nothing here may be cited, and it does not affect any registered
claim. The six specific defects, as ruled by the lead:

1. **Wrong prior object count.** The correct retained set is **24 witness +
   20 anchor = 44 rows**. Numbers of the form "52 rows" or "24 anchor rows"
   in this file are wrong; the retained anchor-edge count is **20**, not 24.
2. **Wrong instrument.** The assigned task is to **perturb the anchors**. Fixing
   the anchors and wiggling the sites does not answer the value-function local
   minimum question at all. Consequently my §3 claim that direction (i)
   "moves nothing that the retained rows see" **directly contradicts** the shared
   anchors I myself list in §2 — if anchors are shared, moving them is visible to
   the retained rows, which is exactly why the shared-anchor reading must be
   treated as the live one.
3. **The jitter runs prove nothing about a no-descent property.** Returning
   `.346` / `.437` from perturbed starts is a **primal upper bound only**; the
   runs did not converge, so they cannot support any "no descent" statement. My
   §0/§3 "V_rel = r* up to tolerance" is unsupported.
4. **The candidate geometry was the wrong object.** `lead/improved-upper-test.json`
   is the old **rounded** improved-upper object, not the exact candidate. A
   `5.3e-9` difference therefore cannot be dismissed as `1e-15` floating-point
   error — the comparison was between different objects.
5. **No dual fork.** Failure of a dual relaxation does not imply the relaxation
   can lower `r*`. The "if the dual closes / if it fails" fork I proposed does
   not exist; §5's stated alternative is void.
6. **X-pair multipliers must not be required to vanish.** The X-pair rows are
   exactly the **active anchor path**; demanding zero multipliers on them was
   wrong.

Standing instruction now: **no new computation**, **do not start
`dual_retained.py`**, task closed. The original `interface owners` listing is
preserved below for the lead to read directly (§2), since it is a raw data
listing rather than a conclusion. No registered claim is affected by anything in
this file, and no claim was registered from it.

Amendments applied on the lead's ruling: banner items 1–6 (§0), retained count
corrected in §1, §2 conclusions withdrawn while the raw listing is kept, §3 table
kept only as an execution record with all interpretations withdrawn, §4 and §5
voided. The earlier "verdict / judgment / next step" content of this file is
retained below only inside strikethrough or explicitly marked WITHDRAWN blocks so
that the failure mode stays auditable.

---

Scope: `members/shared-radius-cc2/relaxed-value/`. Fixed anchors at the candidate
angles (10 anchors, ordered once-winding, original gaps). Candidate radius
`r* = 0.33173203427623366`; candidate centers from `lead/improved-upper-test.json`
(**rounded, not the exact candidate** — see banner item 4; kept in the file only
as the raw starting geometry that was actually used).

## 0'. Original verdict paragraph — WITHDRAWN, kept for the record

**No numeric descent below `r*`.** The relaxation that deletes the six zero-stress
faces and the two slack faces has `V_rel = r*` up to solver tolerance in every
run; the reason is structural (the removed and kept blocks share sites and
anchors, so the "3 anchored components" do not admit an independent rotation),
not a sampling accident. This is a **bounded numeric diagnostic, not a proof** —
a rigorous version needs the retained-set dual certificate, see §5.

*Every sentence of the paragraph above is withdrawn (banner items 1–6).*

## 1. What was removed and what was kept (face ordering checked)

Face ordering differs between producers; I mapped both files
(`interface_maps.json`). The producer's 14 faces match the first 14 of the probe,
which appends the two slack faces at positions 14,15.

| set | faces | witness rows | anchor rows |
|---|---|---|---|
| removed (zero-stress) | 1, 4, 7, 10 (X-adjacent), 12, 13 (central pair) | 24 | — |
| removed (slack) | 14, 15 `[4,6,12]`, `[5,7,13]` | 6 | — |
| **kept** (positive faces) | 0, 2, 3, 5, 6, 8, 9, 11 | **24** | **20** |

**CORRECTED (banner item 1): the retained object is 24 witness + 20 anchor = 44
rows.** Every count of 52 or of 24 retained anchor rows in the first version of
this file was wrong, including the "24 + 4 cut-site rows" bookkeeping in §3 and
the claim that the four extra rows were duplicates of cut-site rows: a prior
object count error, not a derivation. No count in this file may be used.

Kept triples: `[0,4,12] [0,11,12] [1,5,13] [1,11,13] [2,6,12] [2,10,12] [3,7,13] [3,10,13]`.
Sites `8,9` (the X pair, on the x-axis at `±0.9433736573781099`) appear **only**
in removed faces; every other site appears in at least one kept face.

## 2. Interface audit — raw listing (preserved for the lead to read directly)

**Status: this listing is raw data, not a conclusion.** The lead keeps this
question open; the paragraphs below the listing that draw conclusions from it are
**withdrawn** (see banner item 2: the correct object is an anchor perturbation,
and if anchors are shared then a "direction moves nothing" argument is
self-contradictory).

`bridging_anchor_sites` (anchor, site) pairs where the anchor's owner set touches a
site inside a removed face while the retained block still uses the same anchors:

```
(0,3) (1,3) (1,7) (2,5) (2,7) (3,1) (3,5) (4,1)
(5,0) (6,0) (6,4) (7,4) (7,6) (8,2) (8,6) (9,2)
```
All 10 anchors' owner pairs: `(3,9) (3,7) (7,5) (5,1) (8,1) (0,8) (0,4) (4,6) (6,2) (9,2)`.
Sites in the removed faces: `0..13` (all 14). Sites in the kept faces:
`0..7, 10..13`. Removed-only sites: `8, 9`.

~~there is no removed-block component that owns a private anchor set … the
free-graph component count is not the anchored component count.~~
**Withdrawn.** The observation that the raw lists share sites and anchors is
recorded above; no statement about component independence or rotation is made
here.

## 3. Bounded numeric test — WITHDRAWN

~~Variable set: 14 sites + the 8 kept witnesses (2×(14+8) = 44 coordinates).
Value `V_rel = min max` over 52 retained rows (24 kept witness edges + 24 kept
anchor edges + the 4 cut-site anchor rows).~~

**Withdrawn (banner items 1,2,3).** Three defects: the row count was wrong
(correct: 24 + 20 = 44); the instrument fixed the anchors and moved sites, which
does not answer the value-function local-minimum question; and the jitter output
is a primal upper bound from non-converged runs, not a no-descent result. The
table is kept only to document what was actually executed:

| start | max retained distance | comment |
|---|---|---|
| candidate start (old rounded geometry) | 0.331732039541 | different object from the exact candidate (banner 4) |
| jitter 0.02 | 0.34626136 | not converged; upper bound only |
| jitter 0.05 | 0.35325939 | not converged; upper bound only |
| jitter 0.10 | 0.38819672 | not converged; upper bound only |
| jitter 0.20 | 0.43748699 | not converged; upper bound only |

~~Every perturbed start descends back toward the candidate value and never crosses
below it; … (difference `5.3e-9`, floating-point geometry and the 1e-15 arithmetic
of the descent). No retained row is ever observed at a value below `r*`.~~

**Withdrawn.** A non-converged primal upper bound from a wrong-object start
supports neither "descends back" nor "never crosses below `r*`", and the `5.3e-9`
gap was between two different objects, not floating-point error (banner 4).

~~Two named directions … (i) relative rotation of the X-anchor pair … this
direction moves nothing that the retained rows see; (ii) … blocked by the 12
shared sites.~~

**Withdrawn (banner 2).** Direction (i) as written contradicts the sharing
recorded in §2; no direction was actually tested in the correct variable
(the anchors), so neither (i) nor (ii) was assessed. This is where the instrument
failed its assignment.

## 4. What this establishes — NOTHING (all statements withdrawn)

* ~~Establishes (numeric): no observed descent; the candidate geometry is a fixed
  point of the retained rows with value `r*`.~~ **Withdrawn** (banner items 1–4):
  the retained row count was wrong, the instrument fixed the anchors and moved
  sites instead of perturbing the anchors, the runs were non-converged, and the
  starting geometry was the old rounded object rather than the exact candidate.
  **No positive statement follows from this work.**
* ~~Does not establish a proof of `V_rel = r*`.~~ Kept only as the narrower
  disclaimer: no certificate of any kind was produced.
* ~~Judgment: the cheap version is the dual certificate …~~ **Withdrawn
  (banner item 5): there is no dual fork.** A failed dual relaxation does not
  imply the relaxation can lower `r*`. My §5 proposal rested on that non-existent
  fork and is void. **No reduced-branch recommendation is made.**
* ~~if a future producer's retained set produced a value strictly below `r*` …~~
  Withdrawn with the above; any such claim would in any case need its own exact
  primal witness, which is not what this file provides.

## 5. Next executable step — NONE (task closed by the lead)

~~Solve the exact rational/interval dual for the 52 retained rows, check that the
four cut-site rows … unless the X-pair rows have zero multiplier.~~

**Void, and explicitly forbidden.** `dual_retained.py` must **not** be started;
the X-pair rows are the active anchor path and must not be required to carry zero
multipliers. The lead has closed this task. The correct next instrument, if it is
ever reopened, is an **anchor-perturbation** value-function test at the exact
candidate object with the 44-row retained set — not a dual solve and not a
site-only wiggle.

## 6. Files

```
relaxed-value/interface_maps.json     face-index mapping between the two producers
relaxed-value/relaxed_data.json       removed/kept sets, cut sites, anchors, bridges
                                      (raw owners/anchor groups for the lead;
                                       its row counts are superseded by §0 item 1)
relaxed-value/bridge_audit.json       bridging (anchor,site) pairs + numeric runs
relaxed-value/relaxed_test.json       first (Adam) attempt, kept for the record
step1_maps.py step2_data.py step3_test.py step3b_test.py step4_bridge.py
```
Instrument notes (implementation facts, not evidence): `scipy` is absent in this
runtime so `lead/fixed_anchor_convex_probe.py` could not be re-run;
`step3_test.py` (Adam on a smoothed max) drifted upward; `step3b_test.py` /
`step4_bridge.py` (active-set site descent) are what produced the withdrawn table.
**None of the scripts above answers the assigned question (anchor perturbation).**
No claim registered; no registered claim is affected by this file.
