# INVALID — retraction of SECTOR-HEIGHT-OBSTRUCTION.md (lead-rejected, 2026-09-24)

`SECTOR-HEIGHT-OBSTRUCTION.md` is **INVALID** and must not be cited, in whole or in part.
The lead's rejection listed five concrete false statements; all five are confirmed against the
data, and the root cause is one modelling error (I used the wrong ring-centre norm) plus two
conflations (switch angle vs sector/wedge angle; arc half-width vs wedge half-angle).
Downstream conclusions (§3 (EX), §4 hub criterion, and everything resting on them) fall with
them. The lead's exact norm sandwich and 1D factor route are the only objects to be used.

## 1. The five false statements, confirmed and explained

| # | my statement | actual fact | why it was wrong |
|---|---|---|---|
| 1 | "degenerate centre norm = `r` (→ `|c₀| = r`)" | ring centre norm is `sqrt(1-r^2)`; at `r = .3799838531` this is `0.924993119632898`, and the saved norms run `0.7008700542 … 0.8925217299` | I used the **tangency** condition (`|c| = r`, which is the *hub/interior* extreme, `1-2r`-type) as if it were the inward-root formula. The inward-root ring centre satisfies `|c| = sqrt(1-r^2)` (saturating case). |
| 2 | "the owned full width is ... " | **full covered arc width = `2 asin r = 0.779557680390332`** at saturation | bookkeeping only; my text mixed full width and half width |
| 3 | "`Σαᵢ = 2π`" (sector angles) | switch data give `Σ angle(cᵢ-P, cⱼ-P) = 14.910737621273`, i.e. the switch-angle measure is not `2π`; the lead's relation `Σα = 2π + 2Σb` is the correct one | I applied a flat-Euclidean partition identity to **corner angles of the boundary arcs**, which already include the arc curvature; the boundary partition identity applies to the **half-widths** (`Σ wᵢ = π`, verified: `3.141592653590`), not to the corner angles |
| 4 | "isosceles sector `u = v` gives `α = w/2`" | false: with `u = v` the wedge is isosceles, but `α` (corner angle) and `w` (arc half-width) are unrelated by a factor 2; measured wedge angles at the switches are `0.5366, 1.0059, 1.0955, 1.0059, 0.5366, 0.7344, 0.9030, 0.9030, 0.7344`, while the `wᵢ` are `0.2808 … 0.3882` and the switch angles `1.2710 … 2.1014` | conflation of three distinct measures; no identity of that shape holds |
| 5 | "**(EX)** the ten remaining disks must cover `D \ {origin}`" | false. Deleting the pinned boundary disk removes its **boundary arc**, which no other disk need cover in the parent configuration; so no such obligation exists and the C840 deletion argument is invalid | a necessary condition for the *parent* 11-disk cover does not survive deletion of one member |

Additionally, the "hub criterion" in §4 was **false**: two disks of radius `r` centred at the
origin cover `B(0,ε)` whenever `r >= ε` (my `h_j <= r-ε` fails for `h_j = 0`), and a single
centre-at-origin disk covers `B(0,ε)` while the other hub may be arbitrarily far (my
`h_1h_2 <= 2rε` is then vacuous/false as a joint necessary condition). The arccos-sum identity
I quoted was applied to a configuration it does not describe.

## 2. Root cause (single point of failure)

Every false statement traces to **one** substitution: I placed the inward-root ring centre at
`|c| = r` instead of `|c| = sqrt(1-r^2)`. That substitution then (a) made me "prove" a
degenerate corner that cannot exist in that form, (b) made me treat the switch angle as the
sector angle, and (c) produced a hub criterion for the wrong ball geometry.

## 3. What, if anything, survives

Nothing from `SECTOR-HEIGHT-OBSTRUCTION.md`'s §2–§4 is usable. The only statements in this
directory that remain valid are:

* the calibration table of the **9 tight Voronoi vertices and 9 tight boundary points** of the
  saved object (`STATUS.md` §2, `tools/active_verified.py`, `tools/tcert_audit.py`) —
  unaffected, re-derived independently of this document;
* the fact that the arc half-widths satisfy `Σ wᵢ = π` (verified above, `3.141592653590`),
  matching the arc-capacity equalities in `EQUALITY-MECHANISM.md`;
* the naming rule (`C529` for the saved object, `T_cert` for the separate `cert_sym60.json`
  object), `STATUS.md` §3.

## 4. Correct reference data (for whoever needs it; no claim attached)

```
r = 0.37998385311983870904851817957      sqrt(1-r^2) = 0.924993119632898
full covered arc width at saturation = 2 asin r = 0.779557680390332
saved ring norms: 0.8925217299, 0.7617982718, 0.7617982718, 0.7008700539,
                  0.7008700542, 0.8588109377, 0.8588109380, 0.8208532620, 0.8208532656
Σ wᵢ (arc half-widths) = 3.141592653590 = π      (arc-capacity identity)
switch corner angles angle(cᵢ-P,cⱼ-P): 1.5425, 2.1014, 2.1014, 1.5425, 1.2710,
                                       1.6375, 1.8061, 1.6375, 1.2710   (Σ = 14.9107)
owner wedge angles at those switches: 0.5366, 1.0059, 1.0955, 1.0059, 0.5366,
                                      0.7344, 0.9030, 0.9030, 0.7344
```
Repro: `py -3 -B -X utf8 tools/correct_facts_check.py`.

## 5. Status

**Work on the sector-height / degeneracy line is STOPPED.** No further runs, no `claim_add`,
no encoding of (EX), no use of the false hub criterion. If the line is ever reopened, the
first step must be to re-derive the corner in the inward-root variables with
`|c| = sqrt(1-r^2)` and the lead's `Σα = 2π + 2Σb` bookkeeping before any inequality is
written.
