# C914 independent audit (r20-rigidity)

Artifacts audited: `lead/simplex_tree_pilot.py` (`repair` / `field` / `lower`),
`lead/certify_corner_simplexes.py`, `lead/simplex_tree_pilot.json`,
`lead/corner_simplex_certificates.json`, plus the C911 forces read-only.
Independent instrument: `c914_audit.py` (this directory, no lead helper import, my own forest
traversal, my own interval minimum rule). Reproduction: `py -3 -B -X utf8 c914_audit.py`.

## Readings (all recomputed, not quoted)

| item | result |
|---|---|
| forest correction (`repair`) | my own **DFS** forest (not the lead's BFS) on a synthetic rational 51-field: all 22 free-node divergences **exactly zero** in `Fraction` arithmetic; anchor loads sum exactly to `(0,0)`. The loads are forest-dependent (both forests give valid fields), so the certificate's premises must be the *stored* field, as the lead states. |
| rational ceiling normalization | `B = F(ceil(norm_hi·1e12)+1, 1e12)` satisfies `I(B) > norm` exactly-checkably and after dividing by `B` the interval norm is `<= 1`. |
| stored fields | `C911`, `candidate`, `uniform`, `vertex0`: 51 edges, exact zero free divergence, norm `<= 1`. |
| pilot tree | counts `{split 127, certified 0, open 128}`; **no leaf certified** in this pilot; leaf normalized volumes satisfy `sum 2^-depth = 1`; one split has `det(child)/det(parent) = 1/2` as an exact `Fraction` (half-volume identity, no floating geometry). |
| corner set identity | `conv{(1-t)e_j + t e_k, k=0..8} = {y >= 0, sum y = 1, y_j >= 1-t}`: forward direction by construction, reverse by `z = (y-(1-t)e_j)/t` being a convex combination; both verified on 200 random rational combinations. |
| variance penalty | `kappa_i = max(0, -lo(l_i·U on the arc))`, `penalty += kappa_i·width_i^2/8`; the two steps `Var <= (b-a)^2/4` and the `1/2` from the Hessian bound give the factor `1/8`. |
| corner certificates | 9/9 `proved-interval`; recomputed with **my own** arc minimum rule (absolute frame, `kappa = max(0, -lo(intersection form))`): my bounds reproduce the lead's to all printed digits (`0.38028260203663`, `0.38531680615126`, `0.38165167342051`, `0.38139485166384`), worst `0.3802826020366289 > 19/50`. |

## Verdict and limits

The arithmetic kernel of C914 checks out independently (forest correction is forest-agnostic in its
algebra, the ceiling normalization is exact, the variance factor `/8` is correct, the corner set
identity holds, the tree volume identity is exact, and all 9 corner lower bounds reproduce).

Not audited: the SOC dual/support-function derivation itself; whether the union of the certified
corner cells plus unresolved leaves covers any region of interest (the artifacts state that it does
not — no leaf of the pilot is certified and the scope is explicitly "NOT global P"); the v2 proposals'
quality (irrelevant here, since only the exact rational `p` enters). The `solver values are not
premises` claim is consistent with what I read: `repair`/`field`/`lower` use only the rounded rational
forces and interval arithmetic. No new claim.

Hash of this audit's script/JSON: `c914_audit.py` a7d039efdfa240c6f0b918dfd04e8e8aec5e9458048e481f1ccb8e9e425dfda9…, `c914_audit.json`
(the exact digests are in the run log).

## Correction (lead source audit of this audit, 2026-09-25)

The first version of `c914_audit.py` had the following defects, now fixed:

1. **The nine corner fields were not norm-checked.** Section (B) verified `sum ||p_e|| <= 1` for the four
   *tree* fields, not for the nine *corner* fields; the corner block only asserted exact balance.
   Now, per corner: `len(q) == 51`, `sum ||p_e|| <= 1` (interval upper endpoint), all 22 free-node
   divergences exactly zero, and `lb > 19/50` are **asserted inside the loop**, together with the
   corner-set identity `{corner} == {0..8}`. The previous review did **not** cover the corner norms;
   this note does not claim it did.
2. **Hardcoded booleans** in the output JSON replaced by derived ones; the corner lower bounds are now
   asserted, not merely printed.
3. **The convex-hull identity is now proved analytically**, not by sampling: forward direction
   `y = (1-t)e_j + t z` with `z` a convex combination (hence `sum y = 1`, `y >= 0`, `y_j >= 1-t`);
   reverse direction `z = (y - (1-t)e_j)/t` (hence `sum z = 1`, `z >= 0`). The 200 random points are
   removed; two exact-rational spot instances remain only as sanity output.
4. **Wording of the arc rule corrected**: my arc minimum is an *independent implementation of the same
   interval bound* (`cos`/`sin` interval box, `kappa = max(0, -lo(form))`), **not** a different
   representation. The `/8` factor is the two-step `Var <= (b-a)^2/4` and `1/2` combination.
5. The slow `9!` determinant enumeration was removed from this run; the half-volume identity
   `det(child)/det(parent) = 1/2` was verified exactly in the earlier run and is noted as such.

Re-run readings unchanged: four tree fields and nine corner fields all pass the exact-balance and
norm checks; all nine corner lower bounds reproduce the lead's values and exceed `19/50`; the pilot
still has `{split 127, certified 0, open 128}` and leaf volumes summing to 1.
