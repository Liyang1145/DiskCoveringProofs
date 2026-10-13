# FINAL STATE — cine2-closure-geometry (round 4 handoff)

Everything below is reproducible from this directory. I am not sending further
reports; the lead asked to stop probes after the message exchange.

## 1. What is established (and I stand behind it)

**The local boundary cyclic closure identity is TRUE as a necessary condition for
every inward-root 9-ring+2-hub cover, and the lead's halfplane proof of it is
correct.** In the lead's own notation (sector triangle `i = (A=P_(i-1), C=c_i,
B=P_i)`, `L_i` = base angle at `A`, `T_i` = base angle at `B`, `alpha_i` at `C`,
`w_i` = arc width `P_(i-1) -> P_i`):

```
   T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 = pi        (kernel / C820)
   equivalently   L_i + T_(i+1) + 2 b_i + (w_(i-1) + w_i)/2 = pi
   equivalently   T_i + L_(i+1) + 2 b_i = pi - (w_(i-1) + w_i)/2      (*)
```

with `2 b_i` = the angle at `P_i` between the rays to `c_i` and `c_(i+1)`.

**`(*)` is verified numerically to machine precision** — `|...  - pi| <= 4.4e-16`
at 9/9 switches — on:
* the saved certified upper candidate (`n11/upper/certified_object.json`), and
* regular 9-gon configurations with rings at `rho = 0.86, 0.90`
  (source `FINAL_IDENTITY.py`, log `FINAL_IDENTITY.log`).

Proof structure (all three steps independently reproduced, see §2):
1. **Containment.** For each chord of the switch polygon `K`, the outward unit
   normal `m_j` and arc width `w_j` give supporting distance `cos(w_j/2) >=
   sqrt(1-r^2)`; every site satisfies `|c| <= sqrt(1-r^2)` (inward-root, C464/C465
   replacement) so `m_j·c <= |c| <= cos(w_j/2)` by Cauchy-Schwarz. Hence all sites
   are strictly inside `K`.
2. **Voronoi separation.** `a in cl(V(c_i))`, `b in cl(V(c_(i+1)))` give
   `n·(a-P_i) <= 0 <= n·(b-P_i)` for `n = c_(i+1) - c_i`, while
   `n·(c_i-P_i) = -|n|^2/2 < 0 < +|n|^2/2 = n·(c_(i+1)-P_i)`.
3. **Cone order and closure.** The four rays `a, c_i, c_(i+1), b` occur in that
   order in the cone at `P_i` of aperture `theta = pi - (w_(i-1)+w_i)/2`, and the
   two triangle base angles among them are `T_i` (sector `i` at `P_i`) and
   `L_(i+1)` (sector `i+1` at `P_i`), giving `(*)`.

`w_i >= 2 pi - 16 asin(19/50) = 0.046444563591417459 > 0` is proved (each
`w_j <= 2 asin r <= 2 asin R`, `sum w = 2 pi`); the certificate filter
`qmin = 4 sin^2(pi - 8 asin R)/R^2 = 0.014935663152905878` is exactly this bound
at `s = R`, so it is sound and conservative.

## 2. Where my own reporting went wrong (do not reuse)

I twice reported a "counterexample" to the kernel form; both were **my index
bookkeeping errors**, not defects of the identity:
* Draft 1 (`AUDIT-CLOSURE.md`, rejected): invented four Voronoi cells at a switch
  including the hubs, and used a dot-product test as an "outside K" test. Both
  false. Withdrawn.
* Draft 2 and the round of messages: I evaluated `T_i + L_(i+1) + 2b_i` with
  `L_(i+1)` taken as the base angle at `P_(i+1)` instead of **at `P_i`**, which
  produced residuals up to 0.11 rad. Re-evaluating with the correct definitions
  gives machine-precision closure (see §1). **The 0.11 rad readings are
  artifacts and must not be cited.**
The one irreducible difficulty: the two base angles of a sector triangle are
`atan2(v sin a, u - v cos a)` (at one end) and `atan2(u sin a, v - u cos a)` (at
the other), and which end is which is easy to swap; every wrong residual I saw
traced back to that swap.

## 3. Files (freeze; no further edits planned)

**Final / citable**
* `FINAL_IDENTITY.py` + `FINAL_IDENTITY.log` — the identity `(*)`, 9/9 switches,
  saved candidate + regular 9-gons, machine precision.
* `AUDIT-CLOSURE-REPAIRED.md` — full audit: §2 proof, §3 conventions (now with
  the correction above), §4 degeneracies, §5 the `w` bound, §6 sector-norm
  constraint audit, §9 C820 review note.
* `verify_halfplane_proof.py` — containment + Voronoi dominance inequality checks.
* `interior_resolve.py` — interior angle of `K` equals `pi - (w_(i-1)+w_i)/2`
  (saved candidate and regular nonagon).
* `verify_saved_cover.py` — independent covering-radius check of the saved
  candidate (0.379983853120 = `T_cert`), Voronoi degrees 7/6.
* `lead_inequality.py` — the lead's sector-norm constraint is equivalent to
  `|c|^2 <= 1 - R^2`; it fails off the feasible set and must be used with its
  feasibility cut.
* `DEAD-LOCAL.md` — withdrawn claims, wrong conventions, method limits.

**Supporting probes** (used in the audit, self-contained):
`resolve_conv.py`, `decide.py`, `definitive2.py`, `final_convention.py`,
`lead_convention.py`, `switch_table.py`, `wedge_check.py`, `interior_resolve.py`.

**Known-dead probes** (kept only as history, not evidence):
`AUDIT-CLOSURE.md` (draft 1), `definitive.py`, `vertex_cells.py`,
`arcs_saved.py`, `closure_test*.py`, `model3.py`, `handbuilt.py`,
`branch_check.py`, `final_verify.py`, `verify_final.py`, `labeled.py`,
`cover_search*.py`, `stress_closure.py` (0 covers found; search-space issue).

## 4. Open items from my side (none blocking the closure identity)

1. The exact residual index pairing in `lead/certify_q0_closure.py` — my
   reading could not reproduce the kernel residual from coordinates, and the
   lead's coordinate assembly is authoritative. The geometrically consistent
   equation is `(*)`; I recommend the kernel producer confirms in one line that
   its `L` is the base angle at the PREVIOUS switch of the NEXT sector triangle.
2. Certificate-level obligations (factor algebra, box coverage, interval
   arithmetic) are outside this audit and remain the producer teammate's.

## 5. Verification commands

```
py -3 FINAL_IDENTITY.py                     # the identity, machine precision
py -3 verify_halfplane_proof.py             # containment + dominance inequalities
py -3 interior_resolve.py                   # interior-angle formula
py -3 verify_saved_cover.py                 # covering radius of the candidate
py -3 resolve_conv.py                       # conventions
```
