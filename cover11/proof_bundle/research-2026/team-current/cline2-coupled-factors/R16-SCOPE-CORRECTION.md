# R16 scope correction — what the stationary local max does and does not refute

Own scope.  **No new work**, **no numeric run**.  This is a bookkeeping note only, recording
the lead's scope correction so that no surviving artifact of mine overclaims.

## The counterexample (lead, Cartesian 2nd AD)

`r = .377, b1 = 1.008, b2 = 1.001`, face 1, `delta in [-.32, -.31]`:

```
G'(-.32) = +0.0015593421934
G'(-.31) = -0.0027098790910
G'' ~ -.46 .. -.39
```

both endpoints legal, so `G'` crosses zero from `+` to `-`: an interior stationary point of
**local maximum** type.

## What it refutes

* **The stationary-minimum criterion** — refuted.  The integrating-factor route
  (`G'' + k G' > 0` on face 1, `G'' - k G' > 0` on face 2) is dead, and with it the claims
  built on it.
* **The disjunction `G' != 0 OR G'' > 0`** as a way to exclude stationary maxima — refuted at
  this point.

## What it does NOT refute (lead's scope correction, accepted)

* **It does NOT prove that endpoints suffice or fail for the full arc.**  A local maximum at
  this interior point says nothing about whether the objective's VALUE there exceeds the
  values at the arc endpoints; it may well remain below them.  Endpoint sufficiency is
  therefore **not** disproved, and any wording of mine implying otherwise is withdrawn.
* **It does NOT refute** the boundary component of the picture: the conditional boundary
  endpoint bounds (`C863` norm bound, ridge certificate) are untouched.

## Standing status of the new route (lead's, not mine)

Direct bound of the **stationary boxes** at low bearings, with all **non-stationary** boxes
discarded conditionally on the boundary endpoint bounds (`C863` / ridge certificate).  I hold
no claim on that route.

## My artifacts affected by this correction

| artifact | status |
|---|---|
| `r16xx_kcriterion.py`, `r16yy_obstruction.py` | the `k`-criterion measurements — **moot**; the criterion they test is refuted, and the census feeding them was invalid anyway |
| `R16-INTERVAL-DISJUNCTION-RUN.md` | **INVALID** (wrong filter) and now additionally moot (disjunction refuted) |
| `R16-CORRECTED-FILTER.md` | stands (corrected identity + control records) |
| `R16-CARTESIAN-CONTROLS.md` | stands (identities, three controls, corrected sign rule) |
| `R16-CURVATURE-LEGAL-ARCS.md` | the curvature data were computed from the earlier (uncorrected) assembly plus an unfiltered census — treat the numbers as **unverified**, not as refuted; the one claim they make that survives independently is that neither face arc is convex on the sampled set |

## Idle

No further work, no runs, no claims.  Idle pending the lead's new route.
