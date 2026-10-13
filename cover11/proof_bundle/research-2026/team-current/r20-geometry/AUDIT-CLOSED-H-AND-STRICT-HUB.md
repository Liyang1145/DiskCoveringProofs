# Closed-hub degeneracy classification + strict-hub nonemptiness criterion (C879 follow-up)

Author: r20-geometry. Evidence: `audit_closed_h_strict_hub.py/.out.txt/.json`,
`audit_hstar_by_d.json`, `audit_fan_disk_mechanism.out.txt`. `lead/` untouched; no claim
registered by me (the review of C879 is a review event, not a new claim).

## 0. Correction of my previous note (two fixes; both accepted, tables re-derived from the identity)

Local frame as above ($a=(-d/2,0)$, $b=(d/2,0)$, $p_{in}=(0,-k)$, $p_{out}=(0,+k)$,
$k=\sqrt{r^2-d^2/4}$, height $y$ = coordinate along $n$, inward = $y<0$). Write
$F_{in}=|h-p_{in}|^2-r^2$, $F_{out}=|h-p_{out}|^2-r^2$, $R_c$ = circumradius($a,b,h$). The
organising identity (symbolic; numerically confirmed to $3\cdot10^{-40}$ over 360 samples) is

$$4y^2(R_c^2-r^2)=F_{in}\,F_{out},\qquad F_{in}-F_{out}=4ky .$$

**Fix 1 (geometry).** $\{R_c\le r\}$ is the **symmetric difference of the two disks** — the two
*crescents* $B(p_{in},r)\setminus\operatorname{int}B(p_{out},r)$ and its reverse — **not** the
union of two half-disk caps. Points of the overlap (inside both disks), including $y<0$ ones,
have $F_{in}F_{out}>0$, i.e. $R_c>r$ (e.g. $h=m$ where $R_c=\infty$). My earlier "cap" description
and the earlier claim that inside $B(p_{in},r)$ and $y<0$ one automatically has $R_c\le r$ were
wrong. What survives is the *strict-hub* statement: for $|h|<1-r$ one has $F_{out}>0$, hence

$$F_{in}\le0\iff R_c\le r,$$

and $F_{in}\le 0<F_{out}$ forces $4ky=F_{in}-F_{out}<0$, i.e. $y<0$: inward side and
non-collinearity are automatic (my earlier "extra non-collinearity" objection stays withdrawn).

**Fix 2 (closed domain; the lead is right that an outer-circle point is not automatically bad).**
On $|h|\le1-r$ one has $F_{out}\ge0$ (because $|h-p_{out}|\ge|p_{out}|-|h|\ge1-(1-r)=r$), and
$F_{out}=0$ only for $|p_{out}|=1$ and $h=h^\*=(1-r)p_{out}$ (internal tangency of the two
circles). Consequences, all by the identity:

* $F_{out}>0$: mechanism condition $\iff$ face condition (no extras, no misses);
* $F_{out}=0$ (i.e. at $h^\*$): the face condition holds *identically* ($R_c=r$), while
  $F_{in}=4ky_{h^\*}$ decides the mechanism condition, so
  * $y_{h^\*}<0\iff|h^\*-p_{in}|<r$: **legitimate inward closed point** — not a bad point
    (my report already showed $|h^\*-p_{in}|-r\approx-0.36$, i.e. exactly this case);
  * $y_{h^\*}>0\iff|h^\*-p_{in}|>r$: **missed point** — face condition true via the outward
    circle, mechanism disk does not contain it;
  * $y_{h^\*}=0\iff|h^\*-p_{in}|=r$: $h^\*\in\{a,b\}$, degenerate (both circles meet there);
* **off the base line there are no extra points; on the base line there is a degenerate stratum
  (Round-4 fix, see §0bis/Fix 3)**: `F_in ≤ 0` with `y ≠ 0` gives `F_inF_out ≤ 0` hence `R_c ≤ r`;
  `F_in ≤ 0` with `y = 0` combined with the closed-domain estimate `F_out ≥ 0` forces
  `0 ≤ F_in = F_out ≤ 0`, i.e. `h ∈ {a,b}` (the ring centres), where the circumradius is undefined
  (direction-dependent limit `d/(2|sinθ|)`). The earlier blanket claim "no extra points" silently
  divided by `4y²` and is corrected in Fix 3. Verified over 16 903 sampled closed-domain points:
  `min F_out = 9.5·10^{-4} > 0`, zero points with `F_in ≤ 0` and `F_out ≤ 0` (this scan is unaffected —
  it says the overlap interior never meets the closed domain).
* The earlier scan line "18 spurious extra points" was a roundoff/degenerate-boundary artefact
  ($y_{h^\*}>0$ and $|h^\*-p_{in}|\le r$ are equivalent conditions; the two cannot coexist
  strictly) and is **withdrawn**. Corrected patch statement: for the closed relaxation the
  mechanism region is *necessary* up to the finitely many missed points
  $h^\*$ with $y_{h^\*}>0$ (at most one per edge) — one **adds** those points (or excludes them
  explicitly from an "iff" claim); nothing needs deleting.

**Fix 3 (Round 4 — the base-line degeneracy; the lead's correction "y=0 with h=a/b is an extra,
one cannot say 'no extras' uniformly").** The implication chain used for the "no extras" statement
divides by `4y²`. At `y=0` one must argue directly: `F_{in}=F_{out}` (valid at `y=0`), while inside
the mechanism region `F_{in}≤0` and on the closed hub domain `F_{out}≥0`; hence `F_{in}=F_{out}=0`
and `h∈{a,b}` (the two ring centres) — **do not** invoke the full product identity at `y=0`, it
contains the undefined `R_c`. At `h=a` the circumradius of `(a,b,h)` is
**undefined**: along `h=a+εu`, `u=(cosθ,sinθ)`, one has
`R_c → d/(2|sinθ|) ∈ [d/2,∞)` (`d<2r` by Lemma 1, so the infimum `d/2` is `<r`, but the supremum is
`∞`). These are genuine degenerate extras for a closed-domain *iff* reading. They are harmless for
the strict statement and for C879: `|a-p_{out}|=|b-p_{out}|=r` gives
`|a|,|b| ≥ |p_{out}|-r ≥ 1-r`, so a ring centre belongs to the closed hub disk `|h|≤1-r` **only if**
its norm equals `1-r`; the part of the stratum inside the closed domain is exactly
`{a,b}∩∂B(0,1-r)` (in general the degenerate points lie *outside* it) and it never meets `|h|<1-r`.
Full statement and proof: `STRICT-HUB-FINITE-DISJUNCTION.md` §0.

## 1. What is automatic and what is not (sharpened decomposition of the claim)

* $m\in\operatorname{int}D$ is automatic ($|m|\le(|c_i|+|c_j|)/2\le s<1$), hence $t_-<0<t_+$.
* "$U$ covered by both rings" ⟹ $|t_U|\le k$ ⟹ $t_+\le k$ ⟹ **$p_{out}\notin\operatorname{int}D$
  is automatic** (no tie-uniqueness used).
* $t_-<-k$ (i.e. $p_{in}\in\operatorname{int}D$, i.e. $V$ not covered by both) is **exactly** the
  tie-uniqueness hypothesis: $V$ equidistant and covered by one of the two disks is covered by
  both, hence lies in the common overlap as a second equidistant point, contradiction.
* $d=2r$ is impossible: then $k=0$ and $t_+\le k=0$ contradicts $t_+>0$.

## 2. Closed-hub degeneracy: complete classification (new)

Work on the closed relaxation $\bar H=\bar B(0,1-r)$. Since $\operatorname{int}D\ni m$ and
$U$ covered give $|p_{out}|\ge1$, for every $h$ with $|h|\le1-r$:

$$|h-p_{out}|\ge|p_{out}|-|h|\ge 1-(1-r)=r,$$

with equality only if $|p_{out}|=1$ **and** $h=(1-r)p_{out}/|p_{out}|$. The two circles
$\partial B(p_{out},r)$ and $\partial B(0,1-r)$ are internally tangent at that point, so the two
*disks* meet there and nowhere else. Therefore, for one edge (pair) with centre midpoint $m$,
radical direction $n$ and height coordinate $y$:

> **The only closed-domain point where the two branches can differ is $h^\*=(1-r)p_{out}$, and it
> exists only when $|p_{out}|=1$.** By the identity and $F_{in}=4ky_{h^\*}$ at $h^\*$:
> * $y_{h^\*}<0\iff|h^\*-p_{in}|<r$: **legitimate inward point** ($R_c=r$ exactly, and the
>   mechanism's disk contains it) — *not* a bad point;
> * $y_{h^\*}>0\iff|h^\*-p_{in}|>r$: **missed point** ($R_c=r$ via the outward circle, but the
>   mechanism's disk does not contain it) — the closed region must be enlarged by it for an
>   "iff" reading;
> * $y_{h^\*}=0\iff|h^\*-p_{in}|=r$: $h^\*\in\{a,b\}$, degenerate.
> Moreover, off the base line there are **no extra points**: every closed-domain point of the
> mechanism region with $y\ne0$ satisfies $R_c\le r$; on the base line the mechanism region meets
> the closed domain exactly in the degenerate stratum $h\in\{a,b\}$ (see Fix 3), where $R_c$ has no
> value. So "no extras" must be read as "no extras with a well-defined face predicate".

$y_{h^\*}=(1-r)k-r\,(m\cdot n)$ is a closed-form sign test; $h^\*$ is non-collinear iff
$y_{h^\*}\ne0$.

Numerical verification (r = r\* = 0.37998385311983873, exact-rational centre data, mpmath):

* Certified cover, all nine adjacent pairs: $|p_{out}|=1$ (tight switch arcs) and
  $y_{h^\*}\in[-0.19,-0.07]<0$ for **every** pair — i.e. all nine $h^\*$ are legitimate inward
  points (verdict table in `audit_product_identity.out.txt`); no missed and no degenerate cases.
* Admissible-pair scan with $|p_{out}|=1$: 2594 pairs have $y_{h^\*}>0$ (outward, non-collinear;
  those are exactly the pairs with $|h^\*-p_{in}|-r>0$, e.g. $d=0.01246$, $y_{h^\*}=+0.2298$,
  $|h^\*-p_{in}|-r=+3.2\cdot10^{-1}$: a **missed** point). The previously reported "18 bad extra
  points" were the roundoff tail of the same set and are **withdrawn**.
* Geometric trend at $r=r^\*$: $\max y_{h^\*}$ falls with $d$
  (0.231, 0.207, 0.157, 0.104, 0.044 for $d\approx0.01,0.06,0.16,0.25,0.35$) and is negative from
  $d\gtrsim0.46$ on; the certified chain has $d\in[0.451,0.659]$ and is on the safe side.

**Corrected patch statement for the closed domain.** Nothing has to be deleted, and two strata must
be named explicitly for an *iff* reading: (a) **add** the finitely many missed points
$\{h^\* : |p_{out}|=1,\ y_{h^\*}>0\}$ (at most one per edge); (b) **name/exclude** the degenerate
stratum $\{a,b\}\cap\partial B(0,1-r)$ (at most two per edge, present only when a ring centre has
norm exactly $1-r$), where the face predicate has no value. If one wants to stay strictly inside the
inward branch, intersecting each edge's condition with the orientation half-plane $\{y\le0\}$ is
still admissible (it removes nothing from the region since $F_{in}<0$ already forces $y<0$; it only
clarifies the branch), but it is *not* a repair of the missed points. For the strict problem none of
this is needed because $|h|<1-r$ excludes $h^\*$ and, by Fix 3, excludes $\{a,b\}$ as well.

## 3. Strict-hub nonemptiness: finite analytic criterion (new, no grids)

Given a fan edge set with inner intersections $p_1,\dots,p_m$ (radius $r$) and $\rho:=1-r$, let
$S=\bigcap_j \bar B(p_j,r)$ (closed convex, compact).

$$\exists h:\ |h|<\rho\ \text{and}\ |h-p_j|\le r\ \ \forall j
\qquad\Longleftrightarrow\qquad \min_{h\in S}|h|<\rho .$$

Closed nonemptiness of $S\cap\bar B(0,\rho)$ is **not** sufficient (a tangency at $|h|=\rho$
passes it while having no strict point) — that is exactly the degenerate case the lead flagged.
The minimum over $S$ is attained in the finite candidate set

1. $h=0$, if $0\in S$;
2. the closest point of each circle $\partial B(p_j,r)$ to the origin,
   $h=p_j\,(1-r/|p_j|)$, if it lies in $S$;
3. every circle–circle intersection $p_j$-circle with $p_k$-circle ($B=0$ tangency counted once),
   if it lies in $S$;

each candidate tested by the weak inequalities $|h-p_j|\le r$ (with exact/interval arithmetic at
tangencies). No grid, no sampling; $O(m^2)$ candidates. Equivalent MEC form: strict-hub
nonemptiness ⟺ $\min_{|h|\le\rho}\max_j|h-p_j|\le r$ is attained at some point of the *open*
disk; the constrained minimiser is the unconstrained minimum-enclosing-circle centre if
$|c_{\text{MEC}}|<\rho$, otherwise a point of $|h|=\rho$ found from the finite critical set
$\{\arg(p_j)\,{\rm if\ maximal}\}\cup\{$ pair-crossing directions
$(p_j-p_k)\cdot\hat e=(|p_j|^2-|p_k|^2)/(2\rho)\}$.

Verification: on the certified cover's two fan chains (4 and 5 edges, inner intersections
computed from the exact-rational centres) the minimum is attained at circle–circle candidates and
equals the hub norm itself ($\min|h|=0.272977466$ resp. $0.149428499<\rho=0.620016147$): the
extreme hub is in every fan disk, so the strict criterion passes. Adversarial control (two equal
disks tangent to each other and to the hubnorm circle at one point, radius 1/2, $\rho=1/2$):
closed lens nonempty yet $\min|h|-\rho=+0.0$ exactly ⟹ criterion "no strict hub", while
"$S\cap\bar B(0,\rho)\ne\emptyset$" would wrongly accept.

## 4. Scope / non-claims

* The classification of §2 is for **one edge at a time** and is exact (an equivalence, not a
  bound); the whole-chain bad set is the union of the per-edge candidates filtered by the other
  edges' disks — still finite, at most one candidate per edge.
* §3 decides existence of a strict hub satisfying the *fan disk constraints*; it does not decide
  two-fan compatibility (both hubs simultaneously), nor the gluing of the two central triangles.
* Nothing here proves the tie-uniqueness hypothesis (my earlier bounded search suggests it is
  redundant, but that stays numeric); C879 assumes it per edge, which is respected above.
* All statements are conditional on the data precision of the certified object ($10^{-17}$
  rational centres); equality cases are handled by weak tests + exact/interval arithmetic.

Repro:
```
py -3 -B research-2026/team-current/r20-geometry/audit_closed_h_strict_hub.py
```
