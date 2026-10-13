# root-cc2 / chord-envelope-audit status

Scope `research-2026/next-cover-global/members/root-cc2/chord-envelope-audit/` (only).
Lead artifacts read-only. **No claim registered** (lead instruction).

## Verdict

`lead/BOUNDARY-CHORD-ENVELOPE.md` **is correct as an analytic interface**. The lifting
lemma is right (convexity of the squared chord over `[0,r]^2`, maximum at a corner, giving
`|x-y| <= max(r, 2r sin(alpha/2))`), the transfer to
`theta <= max(2asin(r/2), 2asin(r sin(alpha/2)))` is right, the affine envelope
`theta <= 167/500 + (31/250) alpha` is valid on `[0,pi]`, and `Sigma theta = 2pi` gives
`Sigma alpha >= K_q = (2pi - q*167/500)/(31/250)`, i.e. `K_10 = 23.7354`,
`K_11 = 21.0418`.

**None of the forbidden assumptions is used**: endpoint radii need not be equal (the
binding corner is the unequal-radius corner `(r,0)`), the facet triangle is never assumed
isosceles (`beta` does not enter this bound), no interior-point tangents are used, and no
feasibility/KKT of the optimizer is assumed.

## Independently verified constants (my code, 60 digits; not the lead's I type)

| constant | value | bound | margin |
|---|---|---|---|
| `A = 2 asin(U/2)` | 0.3332722560435834 | `< 167/500` | 7.28e-4 |
| `f'(121/50)` | 0.1231917171873321 | `< 31/250` | 8.08e-4 |
| `f(121/50) - (121/50) f'(121/50)` | 0.3330484963622716 | `< 167/500` | 9.52e-4 |

Envelope slack: minimum `7.28e-4` at `alpha = 0` (binding), `4.73e-2` at `alpha = pi`;
positive on a 100001-point grid. Concavity of `f` holds with
`f'' = -U(1-U^2) sin(a/2) / [2(1-U^2 sin^2(a/2))^{3/2}] <= 0`.

## Quantitative caveat

The margin on `f'(alpha0) < 31/250` is `8e-4`, so the envelope is nearly pinned by
concavity; the plateau region `alpha in [0,pi/3]` (where the envelope sits ~0.27 above the
true `A`) is intrinsic to this relaxation, and the candidate graph passes with
`Sigma alpha ~ 25.553` vs `K_10 = 23.735` (margin `~1.82`). "Optimizer proposals violate
the inequality" means the proposals are not covers, not that the graphs are impossible;
exclusion comes only from a negative supporting-plane bound on the augmented relaxation.

## Repro

```
cd research-2026/next-cover-global/members/root-cc2/chord-envelope-audit
py -3 -B py/env01_constants.py     # -> evidence/env01_constants.txt
```

## Not audited

The 12-graph probe and its 9 exclusions, the independent Fraction replay, the catalogue
bookkeeping, and the interaction with the safe-area constants (`../area-safe-audit/`
covers the safe-area reduction separately).
