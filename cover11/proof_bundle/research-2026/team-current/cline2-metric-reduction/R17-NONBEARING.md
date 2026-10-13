# R17 GEOMETRY REPORT — ENTIRELY NONBEARING (final marker)

Per instruction: the whole R17 geometry report is marked **NONBEARING**. No further corrected
formula is issued, and nothing below is offered for formula approval.

## Files marked nonbearing

* `NEXT-IMPLICATION-FLAT-EXCLUSION.md` — **whole file nonbearing.** Its deformation section and
  the `eps ~ delta` / `h ~ sqrt(delta)` geometry in particular. The one thing that had been
  carried forward from it (the `h = r sin(eps/2)` relation in `WITHDRAWAL-R17.md` §2/§5, item
  I-min) is **also void** and must not be used by anyone.
* `WITHDRAWAL-R17.md` — **whole file nonbearing.** It contains no usable geometry. In particular
  its §2 (claimed exact flat-limit geometry), §3 (collar widths), §4 (projection by height) and
  §5 (the I-min formulation using `h = r sin(eps/2)`) are void.
* `r17_1_height_scaling.py`, `r17_2_flat_limit.py`, `r17_3_corrected_scaling.py`,
  `r17_4_exact_scaling.py`, `r17_5_true_scaling.py`, `r17_6_closed_form.py` — **all nonbearing
  artifacts**; none is evidence for anything.

## Correction to the record

The flat width `2 asin(r/2)` that appeared in `WITHDRAWAL-R17.md` §1 and §2 was written there as
the lead's correction. That attribution is **false and is retracted**: the lead never stated it.
The correct flat width is `2 asin r` with chord `2r`, already established in C842's proof. The
`2 asin(r/2)` value was my own construction from an isosceles family and is not part of the
lead's statements.

Scope of my error, for the record: the isosceles construction (site equidistant from both
endpoint sites) is not the general actual sector; it holds only under the additional hypothesis
that both endpoint distances are `r`, and is not the configuration C842's argument uses.

## What remains bearing from Round 17

Only the qualitative structural mapping, and only as a restatement of the lead's own statements:

* the flat class `alpha2 = pi` is a boundary stratum of an open positive domain, so excluding it
  closes no configuration class by itself;
* the two missing classes are (1) `alpha2 = pi` with `min(b1,b2) < 1` and (2) all `alpha2 < pi`,
  with the structural premises each needing separate coverage;
* the correct near-flat geometry, including the missing domain projection, is supplied by
  `lead/NEAR-FLAT-SECTOR-GEOMETRY.md` (lead), not by anything in my files.

No claim registered, no formula issued for approval, no new numerics. Stopping this obligation.

## DEAD entry

`R17-E3` appended in `DEAD.md`.
