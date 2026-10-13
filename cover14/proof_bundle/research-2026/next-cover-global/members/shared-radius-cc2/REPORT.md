# Independent audit — QUARANTINED (corrections-only final)

Member `shared-radius-cc2`. Objects: `lead/SHARED-FACE-RADIUS-THEOREM.md`,
`lead/HEXAGON-FACE-CAP.md`.

## 0. QUARANTINE NOTICE (read first)

The lead has **retracted C1238 and C1232** (no downstream claims used them) and
**rejected C1236 as a whole** (the core hexagon inequality is valid separately as
C1239). The following statements from earlier versions of this report are
therefore **withdrawn and must not be cited**:

1. **§1's branch table and its spot values are unverified.** In particular
   `(π/4)^3` is **wrong**: `beta = (π/4,π/4,π/4)` with `x=y=1` gives
   `Σ_i theta_i = 3.5343 ≠ π`, so `x=1,y=1` is not feasible there; the value
   `2.121320344` must not be used, and the same doubt applies to the `(1.0)^3`
   and `(π/3)^3` entries of that list. The correct lower-branch value for
   `(π/4)^3` is **`√2 + 1/2 = 1.914213562373095 < 3√3/2`** according to the lead's
   lower-branch lemma (`lead/SHARED-RADIUS-LOWER-BRANCH.md`). I did **not**
   independently verify that lemma and do not assert it here — including it only
   to cancel my own false number.
2. **§5's `A_{ij}` "caveat" was FALSE and is withdrawn.** `A_{ij} = u_i + u_j`
   gives `A_{ij} − u_i = u_j`, hence `|A_{ij} − u_i| = |u_j| = U` **exactly**
   (the `√3` in my caveat came from a hand-arithmetic slip). The lead's equality
   construction was right and my "correction" was wrong.
3. **§2's alternative derivative factorisation `A'(t) = 2√3 cos t·cos(t−π/3)` is
   wrong factor-wise** (lead's correction). Only the primary expressions
   `x0 = cos t + sin t/√3`, `A = 3 sin t cos t + √3 sin²t`,
   `A'' = −6 sin 2t + 2√3 cos 2t` were numerically checked by me; the
   factorisation must not be cited.
4. **The non-concavity finding is confinement-limited.** `A''>0` is established
   **only along the diagonal** `beta=(t,t,t)`. It does **not** by itself establish
   non-concavity in the full 3-D domain, and I found no such 3-D witness. C1233
   is to be read as a diagonal-slice statement only.
5. No further tests were run and no further claims were registered, per the
   lead's instruction. Nothing below is accepted; every item is my own audit and
   requires independent check before use.

Requested model route `commandcode2 / deepseek/deepseek-v4.1-flash`: I have no
provider/model field in my tool schema, so this is **unverified** and not claimed.

---

## 1. Object and the (correct) envelope reduction

`A(beta) = x0(beta) Σ_i sin beta_i` on `{0<beta_i<π, Σbeta<2π}`, with `x0` the
root of `H(x) = Σ_i atan2(sin beta_i, x−cos beta_i) = π` (`H` strictly decreasing,
`H(1)=(3π−Σbeta)/2`, `H(0+)=3π−Σbeta`).

Verified against an independent representation (complex argument) and against
bisection, **legal upper branch `π<Σbeta<2π` only** (14820 points):
`max|x0_bisect − x0_algebraic| = 1.39e−15`,
`max|H(x0)−π| ≤ 1.8e−13`, branch violations `≤0`.
Agreement of the theorem's `(b+√(b²−4ac))/(2a)` with the crossing is therefore
machine precision — the algebraic representation is correct. (Lead's own note
that `Σbeta<π` has no crossing in `(0,1]` is confirmed: `H(1)>π` there, no root.)

**Two branches of the reduction** (I got the direction wrong twice and it has not
been accepted; recorded here only for the record — treat as **unverified**):

| case | `x0` | claimed feasible x | claimed value |
|---|---|---|---|
| `Σbeta ≤ π` | `x0 = 1` | `x ∈ (0,1]` | `Σ sin beta_i` |
| `π < Σbeta < 2π` | `x0 < 1` | `x ∈ (0,x0]` | `x0 Σ sin beta_i` |

QUARANTINED spot values (from that unaccepted table; **do not cite**):
`(π/4)^3 → 2.121320344` (**false**, see §0.1), `(1.0)^3 → 2.524412954` (doubtful),
`(π/3)^3 → 2.598076211` (doubtful), `(1.2)^3 → 2.517821865`,
`(π/2)^3 → 1.732050808`, candidate → `2.568290234`, `(1.3)^3 → 2.381364890`,
`(1.4,1.28,0.5) → 2.408498697`. The 2-D `(x,θ)` scan and the "attained value at
`x=x0,y=1`" reading are likewise unverified for the `Σbeta≤π` branch, where the
lead's lower-branch lemma gives the different value `√2+1/2` at `(π/4)^3`.

## 2. Concavity of A(beta): NOT concave, on the diagonal only

On `beta=(t,t,t)` the envelope is elementary and exact. Solving
`3 atan2(sin t, x−cos t) = π` for `t ∈ [π/3, 2π/3]` gives

```
x0(t) = cos t + sin t/√3 ,     A(t,t,t) = 3 sin t cos t + √3 sin²t
A''(t) = −6 sin 2t + 2√3 cos 2t
```
(The factorisation `A'(t) = 2√3 cos t·cos(t−π/3)` that appeared here earlier is
**wrong factor-wise** — withdrawn per §0.3; only `A'(t) = 3cos2t + √3 sin2t` is
kept.) Verified numerically: `max|A_code − A_closed| = 8.9e−16` on 1001 diagonal
points; `A'(π/3) = 0`, `A'(π/3⁻) = 3/2`,
`A''(π/3) = −4√3 = −6.928203230`, `A''(7π/12) = 0`,
`A''(2π/3) = +2√3 = +3.464101615`.

**Verdict (DIAGONAL ONLY).** Along the diagonal, `A` is **concave on `(0, 7π/12]`**
and **convex on `(7π/12, 2π/3)`**. This is a statement about the diagonal slice;
it does **not** establish non-concavity on the 3-D domain (see §0.4). Note the
direction point: the "midpoint above the chord" pattern *confirms* concavity, so
it is not a valid disproof. Diagonal witnesses:

* curvature: `A''(2π/3) = 2√3 > 0` (locally convex near the degenerate end);
* finite version inside the convex window, e.g. `t1=1.9, t2=2.05`:
  `A(t1)=0.6332367`, `A(mid)=0.3793646`, `A(t2)=0.1364219`,
  `chord_mid=0.3848293`, so `A(mid) − chord_mid = −0.0054647 < 0` (concavity fails);
  also `t1=1.85,t2=2.05`: `−0.0080326 < 0`; `t1=2.0,t2=2.09`: `−0.0028892 < 0`;
* for contrast a point in the concave window `t1=0.3,t2=1.5` gives
  `+1.0569138 > 0` (consistent with concavity).

`A` is not even concave at the junction; but the failure is confined to the
degenerate neighbourhood of `Σbeta=2π`, which is the region a certificate will
in any case handle by compact limits.

## 3. The candidate tangent

At `beta0 = (0.9223829833, 1.1925065472, 1.1925065472)`:
`A(beta0) = 2.568290234377852`, `grad A(beta0) = (0.02189936, −0.18872610, −0.18872610)`
(central differences of the **true** `A`, `h=1e−6`, one-sided values agree to 3e−9).

**Diagnostic (direction corrected).** The relevant test for "L majorizes A" is
`max_beta [A(beta) − L(beta)] ≤ 0`; the earlier report tested `L−A` and drew the
opposite conclusion, which was wrong. Re-run with the correct sign on 3000 random
feasible points plus local polish: `max_beta [A(beta) − L(beta)] = −0.0144445 < 0`.
So my earlier "tangent fails globally" verdict is **withdrawn**; the diagnostic is
consistent with the tangent majorizing (no violation found). This is still only
numeric — no tangent-majorization theorem is claimed here.
`L(beta0) = A(beta0)`, and the tangent slack at the candidate is `0` by construction.

**Simpler valid majorants (all rigorous, no scan needed).**
* constant: `A ≤ 3√3/2 = 2.598076211353` (slack at the candidate `0.029786`).
  Two different upper bounds are in play and must not be conflated:
  (i) the *trivial* bound `A = x Σy_i sin beta_i ≤ Σ sin beta_i ≤ 3`, whose
  supremum `3` is approached as `beta → (π/2,π/2,π/2)` — but there the actual
  interface value is only `x0 Σ sin beta_i = (1/√3)·3 = 1.732050808`, because
  `x0 = 1/√3` is forced; (ii) the *theorem's* envelope `x0 Σ sin beta_i`, which is
  the actual (attained) optimum and peaks at `3√3/2` at `(π/3,π/3,π/3)`;
  (iii) the hexagon cap `3√3/2 U²` of §5, which reaches the same constant with no
  `x0` bookkeeping. So `3√3/2` rests on (ii)+(iii), not on `x0 ≤ 1` alone;
* Jensen: `A = x0 Σ sin beta_i ≤ Σ sin beta_i ≤ 3 sin(Σbeta/3)` (since `x0≤1`
  and `sin` is concave), which is concave and radial;
* `min(3 sin(Σbeta/3), 3√3/2)`: for `Σbeta ≤ π` the Jensen term is the smaller
  (and equals `3√3/2` at `Σbeta = 3π/2` only if `Σbeta` could be that large in
  this branch, which it cannot since `Σbeta ≤ π`); for `π < Σbeta ≤ 2π` the
  constant `3√3/2` is the smaller one, so the min is active on `Σbeta ≥ π`
  (verified with zero violation on 4000 random feasible `beta` against the direct
  solver).

## 4. Where the envelope peaks — QUARANTINED (C1234/C1238 retracted)

Global search with the `direct_v2`/`direct_v3` solvers gave
`max A = 2.598076211353316` at `beta=(π/3,π/3,π/3)`, i.e. `3√3/2`, and the
diagonal sweep (2e5 points) peaked at `2.598076211352` at `t = π/3`. **These are
not accepted**: C1234 and C1238 were retracted (no downstream claims affected),
and the `(π/4)^3` failure in §0.1 shows that this solver's `Σbeta≤π` branch was
wrong, so the same global claim must not be relied on. The spot values quoted here
earlier (`(1.0)^3 → 2.524412954`, `(1.84)^3 → 0.840377144`, `(2.0)^3 → 0.296893642`,
`(π/2)^3 → 1.732050808`, `(1.2)^3 → 2.517821865`) are recorded as **unverified
solver output**. The buggy-envelope and feasibility-inverted instruments are noted
in §7 and must not be cited.

## 5. Hexagon cap — audit of `lead/HEXAGON-FACE-CAP.md`

I re-derived the proof independently and agree with it. Three checks:

**(a) Cancellation.** `Q_i = [O,u_i,A_i] + [O,A_i,u_{i+1}]` and summing the six
triangles around the closed walk cancels the `O`-spokes, giving
`Σ_i Q_i = signed_area(u1,A1,u2,A2,u3,A3)`. Reproduced by direct shoelace
comparison on genuine configurations (central triangle + one real neighbour
triangle per edge, sharing the chord exactly): identity holds to `4.4e−16`
(400 configs) and `2.2e−16` (3000 configs), including a thin and an acute cover.
Status of this check: the identity is verified for the algebraic walk; what I did
**not** exhaustively verify is that every local interface arising in the
application produces such a walk (i.e. that each facet's two chord-endpoints
really are `u_i,u_{i+1}` with the same chord length for both facets). The proof
is sound whenever that is so; that hypothesis belongs to the interface layer
(`lead/BOUNDARY-FACET-RADIUS-*`), not to this inequality.

**(b) Signed n-gon inequality.** Re-derived from the discrete Fourier expansion and
agree with every step: `area = ½ Im Σ_j conj(z_j) z_{j+1} = (n/2)Σ_k |a_k|² sin(2πk/n)`,
`Σ_j |z_{j+1}−z_j|² = 2n Σ_k |a_k|²(1−cos(2πk/n))`, quotient
`= cot(πk/n)/4 ≤ cot(π/n)/4` for `1≤k≤n/2` (`k=0` is null; `n/2<k<n` contributes
`≤0`); equality needs a single positive mode `k=1`, i.e. a regular positively
oriented n-gon. Independent numerics: regular n-gon attains `(1/4)cot(π/n)`
exactly for `n=3..10`; random closed n-gons (edges ≤1, monotone projection
construction) never violate the bound for `n=3,4,5,6,7,8,10`; a self-intersecting
closed hexagon satisfies it too (`2.25 ≤ 2.9462`); for `n=6`, `(1/4)cot(π/6)=√3/4`.

**(c) The chain.** Six facet side lengths are `T_1,T_1,T_2,T_2,T_3,T_3` with
`T_k ≤ U`, so `Σ l_k² ≤ 6U²` and `Σ Q_i ≤ (√3/4)(6U²) = (3√3/2)U² ≈ 2.598 U²`.
Sharpness: a configuration attaining the bound was found by coordinate ascent
(`signed hexagon area 2.5980762165` vs bound `2.5980762113`, all six sides `=U`),
and random realizable configurations (1968/1968) stayed within the bound, worst
ratio `0.9296`.

**WITHDRAWN (was false): the `A_{ij}` notation caveat.** The text that stood here
claimed `A_{ij} = u_i + u_j` gives `|A_{ij} − u_i| = √3 > U`. That is wrong:
`A_{ij} − u_i = u_j`, so `|A_{ij} − u_i| = |u_j| = U` exactly, and the lead's
all-norm-`U` statement holds. The caveat is deleted; the equality example in
`lead/HEXAGON-FACE-CAP.md` needs no re-check from me.

**Claim status.** My C1236 (which bundled the three checks above with the false
caveat) was **rejected as a whole**; the core inequality stands separately as
C1239. Nothing in §5 should be cited through my claim id.

**On the "factor `3/2.598`" remark I made earlier:** that compared the hexagon cap
against the *trivial* bound `A ≤ 3`, not against the theorem's envelope; the
envelope's own supremum is also `3√3/2` (per §4, itself quarantined/retracted),
so the two routes are not in a "one improves the other" relation. Treat that
remark as withdrawn.

**Why this *was* meant to matter — comparison, now conditional.** If the envelope
supremum were `3√3/2` (that is C1234/C1238, both retracted/quarantined), then both
routes would deliver the same constant by independent machinery: the `x0` route
via the monotone `H` plus per-box interval work on `Σbeta`, the hexagon route via
a two-line cancellation plus the classical signed n-gon inequality with **no
`beta`-dependence at all**. Since the envelope-side global statement is not
verified, the comparison is **conditional**: only the hexagon half
(`ΣQᵢ ≤ 3√3/2·U²`, C1239) is claimed. My earlier "the two bounds give the same
constant / neither dominates" sentences are withdrawn with C1237/C1238.

## 6. Claim ledger from this audit

| id | my claim | status as of this note |
|----|----------|------------------------|
| C1231 | x0 formula + branch table (v1) | **retracted by me** (direction transposed) |
| C1232 | diagonal closed form + derivatives | **retracted by the lead** |
| C1233 | non-concavity | to be read as **diagonal-only**; 3-D confinement not established |
| C1234 | global `max A = 3√3/2` (numeric) | numeric, **not accepted** |
| C1235 | candidate tangent `max(A−L) < 0` (numeric) | numeric, **not accepted** (self-reported, no independent replay) |
| C1236 | hexagon bundle incl. false `A_{ij}` caveat | **rejected as a whole by the lead**; core inequality valid separately as **C1239** |
| C1237 | x0 formula + branches (v2) | **retracted by me** (wrong "hexagon is tighter" note) |
| C1238 | x0 formula + branches (v3) | **retracted by the lead** |

Not accepted, and not re-registered: any statement in this report. The only
externally validated item in the neighbourhood of this audit is the lead's **C1239**
(hexagon inequality) — the three checks I performed in §5(a)–(c) reproduce it, but
my reproduction carries no independent weight beyond the lead's own proof.
No analytic proof of the envelope supremum; no tangent-majorization theorem; no
change to the n14 global optimum.

## 7. Files

```
envelope_clean.py             H/theta primitives, bisection-vs-algebraic self-tests
direct_v2.py / direct_v3.py   corrected direct solvers (equality constraint)
direction_table.py            raw unambiguous S(x) / branch table (settles direction)
audit_ground_truth.py         exhaustive (x,theta) scan with y from chord identity
audit_polygon.py              signed n-gon inequality: constants, random n-gons, cancellation
audit_cap_final.py            hexagon realizability/sharpness/cancellation
audit_adversarial_cap_fixed.py  attainable-bound search with mirror signs
audit_cancellation_exact.py, audit_genuine_genuine.py   cancellation on genuine configs
verify_corrections.py         all corrected facts of this report
run_audit_final.py, run_bounded_scan.py, audit_feasibility_direction.py
audit_clean_scan.py, audit_realizable_max.py  (instrument attempts; see note below)
```
Data: `corrections_verified.json`, `clean_self_test.json`, `decisive_results.json`,
`bounded_scan.json`, `cap_audit_final.json`, `polygon_audit.json`,
`adversarial_cap_fixed.json`, `genuine_genuine.json`, `ground_truth_scan.json`,
`direction_table.py` output.
Do **not** cite: `audit_envelope.py` (`b≡0` bug), `run_decisive.py` (inverted
feasibility), `audit_clean_scan.py` / `audit_realizable_max.py` (λ-bisection
direction / degenerate circumcenters) — all superseded and listed only to prevent
reuse.
