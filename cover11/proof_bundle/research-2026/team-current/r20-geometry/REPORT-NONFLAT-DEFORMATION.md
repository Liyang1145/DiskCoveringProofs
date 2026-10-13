# Non-flat control / domain-preserving deformation: verdict and counterexamples

Author: r20-geometry (continuation of the inactive r20-geometry work; no subagents).
Write scope: this directory only; `lead/` untouched; **no claim registered**. Inputs read only:
`../lead/joint_nested_frozen.json` (SHA256 `5671967c…221fb`), `../../../n11/upper/certified_object.json`,
plus the existing r20-geometry outputs (`cand_*`, `exp1..exp4`).

## 0. Object and quantifiers (what the two sides of the comparison quantify over)

* **Class.** `X67` = inward-root q0(6,7) 11-disk configurations (9 boundary-owning rings + 2 strict
  hubs, ring/switch scale and angle closure, non-negative overlap, unequal switch scales allowed),
  parameter `r ∈ (3/8, U]`, `U = 37999/100000`. `X67` is **non-empty and contains the certified
  extremal cover** (`n11/upper/certified_object.json`, hubs = original indices {0,2}, degree pair
  (7,6)), see `r20-alternative/R20-ALTERNATIVE.md` §(★11); independently, the frozen dual is *tight*
  at that object's own patch data (§1 below). Hence no proof that kills all of `X67` in
  `r ∈ [.379,.37999]` can be correct, and every certificate in that `r`-range is a **sub-class**
  statement.
* **Chart.** `gen chart` = the C849 seven-factor patch relaxation
  `(t, α1,u1,s1, α2,s2, α3,v3, A,H)` with the frozen closure `b1,b2` (C820), `t = r/R0`,
  `R0 = 19/50`; legality margins as in `r20_lib.gen_margins` (re-implemented independently in
  `verify_indep_candidate.py::margins`). It is a **relaxation** of the local patch data of any
  `X67` member; a chart point need not be realizable as a cover.
* **Functional.** `J` = sum of the seven frozen-dual atoms {faces 1,2; switches 12,13;
  sectors 21,22,23} (`lead/exchange_joint_patch.py:13` cluster `[21,22,23,12,13,1,2]`), evaluated
  with the frozen `z`. The flat-certificate chain needs
  `J ≤ T := π − (const + Σ22_sup) = 28.10704541577262956809`
  (`lead/LOCAL-Q0-FLAT-EXCLUSION.md`, `ROUND15-CONVEX-HUB-LENS.md`); the certified seven-factor
  upper bound for the **flat high-bearing** relaxation (`α2=π`, `r∈[.379,.37999]`,
  `b1,b2∈[1,acos r]`, all legal widths/hub) is
  `U_HB := 28.1069488227408612601720960810780525207519531`
  (`lead/highbearing_boundary_assembly.json`, components C861/C863/C869/stationary).

## 1. The witness is the extremal cover itself (independently re-verified)

`cand_full29.py` evaluates **all 29** frozen atoms at the certified cover's own patch data.
Re-run: `const + Σ29 = 3.141592653589800` vs `π = 3.141592653589793` (slack `7.1e-15`).
My independent recomputation (`verify_indep_candidate.py`, mpmath 50 digits, exact-rational centre
data, switch points by **angular bisection** instead of the radical-line formula, my own atom
transcription) gives

| quantity | value |
|---|---|
| `Σ29 + const − π` | `+1.0e-49` (i.e. the frozen dual is tight at this data point) |
| `J(p*)` | `28.11447884468304165192883` (float64 path: `28.114478844683042`) |
| `J(p*) − T` | `+7.4334289e-3` |
| `J(p*) − U_HB` | `+7.5300219e-3` |
| `J(p*) −` (numeric flat max, 3 starts) | `+1.0242e-2` |
| chart legality of `p*` | min margin `+8e-51` (six endpoint and two face-circle constraints active) |

`p*` has `α2 = 2.967354039336` (so `π − α2 = 0.174239`), `b1 = b2 = 1.050678342 ≥ 1`,
`r = 0.3799838531198387 ∈ [.379,.37999]`: it lies in the same box as `U_HB`, and it is a
**realized** configuration (an actual cover), not merely a chart point.
The tightness of the frozen dual at `p*` also means the frozen q0(6,7) graph is the certified
object's own combinatorial type (its faces reproduce the frozen atom list to `1e-49`), consistent
with the class-membership facts quoted in §0.

## 2. The propositions attacked, and their verdicts

> **Q-Deform (box version).** For every legal non-flat patch `p` of the chart with
> `r ∈ [.379,.37999]`, `b1,b2 ∈ [1, acos r]`, there is a legal **flat** patch `p̃` of the same chart
> in the same box with `J(p̃) ≥ J(p)`.

**False.** Counterexample `p = p*` (the certified cover's own patch): `J(p*) = 28.1144788…`, while
*every* flat high-bearing patch has `J ≤ U_HB = 28.1069488…` (lead's certified assembly). So no
flat patch in the box dominates `p*`; a fortiori no *domain-preserving deformation* with
non-decreasing `J` onto the flat slice exists. (Whole-flat-slice version: numeric flat maximum
`28.104237` over the 7-parameter flat chart with 3 starts, and the certified bound covers the
high-bearing part plus the both-low collar C876 — not the entire flat slice; see §4 scope.)

> **Q-Deform (local version).** Along the extremal outer data, flattening the middle sector does
> not decrease `J`.

**False, even infinitesimally.** One-sided differences at fixed `(A,H)` (mpmath, closure
recomputed): `J(α2−h) − J(α2) = +5.498e-5` for `h=1e-3` → `∂J/∂α2 ≈ −0.055`, i.e. `J`
**increases** when the sector is made less flat. (These perturbed points leave the active
constraint `h`-proportionally; the clean family statement is the fibre-maximum sweep below.)

> **Q-Cert.** Every legal non-flat patch of the box has `J ≤ T`.

**False** by the same witness (`J(p*) − T = +7.43e-3`).

### Fibre-maxima family (deterministic grid `(A,H)` + box refinement, mpmath; 0 random restarts)

Fixed outer data = the certified cover's `(t,α1,u1,α3,v3)`, re-maximising `J` over the legal
`(A,H)` at each `ε = π − α2`:

| `ε` | 0 | 0.005 | 0.02 | 0.05 | 0.07 | 0.1 | 0.174239 | 0.4 |
|---|---|---|---|---|---|---|---|---|
| this work | 28.10217 | 28.10253 | 28.10360 | 28.10567 | 28.10700 | 28.10893 | 28.11332 | 28.12313 |
| `exp3_profile` (independent float64 grids) | 28.10295 | 28.10331 | 28.10438 | 28.10646 | — | 28.10973 | 28.11412 | 28.12317 |

Both implementations agree to `≤1.3e-3` and show the same structure: `J` grows with `ε` at
`≈ 0.065` per radian near flatness, crossing `T` at `ε ≈ 0.06–0.07`. The extremal cover sits at
`ε = 0.174` with `J > U_HB`.

### Asymmetric / degenerate attack (`exp5_asym_degeneracy.py`; deterministic, no restarts)

* switch asymmetry `s1 ≠ s2`: `J` **decreases** (`s1=t−0.1` → 28.0851; `s1=t−0.15, s2=t−0.05` →
  28.0548); the extremal point has `s1 = s2 = t` exactly.
* neighbour asymmetry `α1,α3` and outer endpoints `u1,v3`: `J` decreases (e.g. `α1+0.3` →
  28.1086, `α1−0.3, α3−0.3` → 28.1051); most non-symmetric endpoint moves are chart-infeasible.
* degenerate corners: `t = 75/76`, `s1=s2=t−0.3`, `u1=v3=0.19`, `α1=α3=0.05`, `α2→g/2` are all
  infeasible in the chart; `α2 = π − 1e-8` gives `28.10348 < T` (near-flat collar below `T`);
  `α1=α3=π−1e-6` gives `28.08486`.
* coarse `(ε, s1,s2)` box scan: largest non-flat value reached
  `28.122356791423` at `ε = 0.60, s1=s2=t` → excess over `T`: `+1.531e-2`; over `U_HB`: `+1.541e-2`.

## 3. What this means for the flat exclusion route (the requested clarification)

1. **Role.** The flat exclusion is an **endpoint/degeneracy elimination inside a relaxation**:
   `α2 = π` is the degenerate endpoint of the compact necessary angle domain `α ∈ [g/2, π]`
   (sector triangle collapses: `u2=v2=t`, `w2=2asin r`). The C876/C854-chain removes that endpoint
   (plus a bearing collar) for `r ∈ [.379,.37999]`. It is **not** the sharp inequality: it produces
   no lower bound for `r_D(11)` unless combined with an interior analysis, and it cannot be a
   statement about the whole class because the class contains an actual cover in that `r`-range.
2. **The endpoint cannot be inflated into the interior by objective monotonicity.** Any route of
   the form "project the non-flat patch to the flat slice, keep legality, and compare `J`" is
   refuted by `p*` (globally in the high-bearing box) and by the local slope (infinitesimally).
   Quantitatively, extending the *certificate* to the non-flat box would need
   `const + Σ22_sup ≤ π − sup_nonflat J`; with `sup J ≥ 28.1145` (realized) this means improving
   the 22-factor bound by `≥ 7.43e-3` (and by `≥ 1.53e-2` to cover the scanned maximum
   `28.1224`), from the current `−24.965452762182836` to `≤ −24.972886` resp. `≤ −24.980764`.
3. **Why the flat certificate cannot simply be re-run on the interior.** In the flat case the
   patch objective separates fibrewise: fixing `(r,b1,b2,A)` leaves a constant plus three
   univariate functions of `w1,w3,H` (C849). For `α2 < π` the closure couples `(α2, s1, s2)` to
   the widths and the faces (`B = π + b1 + b2 − α2 − A`, and `L2,T2,w2` depend on `s1,s2,α2`), so
   the flat fibre decomposition is **flat-specific**; the arc-by-arc maximisation architecture
   does not transfer.

## 4. Scope, non-claims, missing interfaces

* **Claimed here** (with the evidence above): (i) `J(p*) = 28.1144788446830…` at the certified
  cover's own patch data, independently recomputed in 50-digit arithmetic, with the frozen dual
  tight to `1e-49`; (ii) the certified flat-upper side `U_HB = 28.1069488…` is *below* it, so
  `Q-Deform`/`Q-Cert` fail in the high-bearing box; (iii) the local slope in `α2` is negative;
  (iv) the asymmetric/degenerate probes do not produce a larger witness, and the largest scanned
  non-flat value is `28.1224`.
* **Not claimed:** that the whole q0(6,7) route is dead — it is not; only the *J-monotone
  flat-domination* transfer is refuted (the class must contain the extremum, so the sharp
  statement must be an equality/rigidity statement, not an exclusion). Not claimed: a certified
  upper bound for the flat slice outside the high-bearing box / both-low collar (that region is
  open; the numeric `28.104237` is only a lower bound of the true flat maximum). Not claimed: that
  `28.1224` is the non-flat supremum (grid scan floor). My `U_HB` quotation is conditional on the
  lead's C876-chain certificates, which I did not re-verify; the `p*` side is independently
  verified here.
* **Missing interfaces** (the exact next obligations):
  (a) *chart ↔ class*: a statement of which chart points are realizable patch data; `p*` is, the
  scan maxima may not be;
  (b) for a sharp inequality on the interior: an equality-aware loss function with a controlled
  remainder (the `α2`-coupling above), not another area-dual bound;
  (c) the 22-factor bound improvement quantified in §3.2 if the certificate route is to be
  extended to the interior at all (and note that even then no *exclusion* of the class is
  possible, only a positive margin for `r < r*`).

## 5. Budget and repro

Existing outputs were inspected first (`cand_*.py`, `exp1..exp4`, `witness_nonflat.json`,
`exp3_profile.json`); one pre-existing defect was found there: `exp3` section (B) re-optimised
`(A,H)` on a `24×24` grid and its reported offsets are biased low by `≈6–9e-3`, so its
"asymmetric checks" are not comparable with `J(p*)`; `exp5` replaces them. The non-flat attack used
**0 random restarts** (deterministic grids only; ≤ 60 outer grid points in the box scan), within
the 20-start envelope. The separate lead-requested fan audit (`AUDIT-FAN-DISK-MECHANISM.md`) used
60 float64 Nelder–Mead starts plus one deterministic 41k-point screen; that is a different task and
is disclosed there.

```
py -3 -B research-2026/team-current/r20-geometry/cand_full29.py              # 29-atom identity at p*
py -3 -B research-2026/team-current/r20-geometry/verify_indep_candidate.py   # independent 50-digit recheck + family
py -3 -B research-2026/team-current/r20-geometry/exp5_asym_degeneracy.py     # asymmetric + degenerate attack
```

Evidence: `verify_indep_candidate.out.txt/.json`, `exp5_asym_degeneracy.out.txt/.json`,
`cand_full29.out.txt`, `witness_nonflat.json`, `exp3_profile.out.txt`.
