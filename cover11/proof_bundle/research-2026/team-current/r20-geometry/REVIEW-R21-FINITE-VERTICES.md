# Interface review: C877 finite-vertex maximum + R21 residual membership

Reviewer: r20-geometry (cline2 DS v4.1f session, no subagents). Scope: the two lead notes
`lead/R21-RESIDUAL-FINITE-VERTICES.md` (C877) and `lead/R21-RESIDUAL-MEMBERSHIP.md`, i.e. the
finite-vertex reduction the lead is using to remove the hub continuum in R20/R21. Inputs read
only; nothing in `lead/` modified; no claim registered.

**Verdict: C877 holds as stated, and none of the three named degeneracies (line tangency,
isolated K, closed halfplane) breaks it.** The proofs below are independent re-derivations of
each case, plus one explicit finite example (`review_r21_vertices.py`) showing where the real
risk sits: not in the theorem but in the *membership filter* it depends on.

## 1. Object and notation (as in C877)

Ring centres $c_1,\dots,c_n$ distinct, $|c_i|\le s<1$; their closed radius-$r$ disks cover
$\partial D$; $U=\{x\in D:\ |x-c_i|>r\ \forall i\}$, $K=\overline U$, $H=B(0,1-r)$,
$S=K\cap\{n\!\cdot\! x\le t\}$, and
$V(L)=\{$circle–circle intersection points in $S\}\cup\{$points of $L\cap C_i$ that lie in $K\}$.

Annulus lemma (restated, used below): for a unit direction $e$ take $i$ with $|e-c_i|\le r$;
along $te$, $t\in[s,1]$, $\frac{d}{dt}|te-c_i|^2=2(t-e\!\cdot\! c_i)\ge 2(t-s)\ge0$, so
$|te-c_i|^2\le|e-c_i|^2\le r^2$. Hence $s\le|x|\le1$ is ring-covered, i.e.
$K\subset B(0,s)\subset D^\circ$ — the whole residual is at distance $\ge 1-s>0$ from $\partial D$.

## 2. The three degeneracies

**(a) "isolated K".** *Impossible for nonempty K, not merely harmless.* By R21-MEMBERSHIP,
$x\in K$ iff the active normals $v_i=x-c_i$ ($|x-c_i|=r$) admit a nonzero $d$ with
$v_i\!\cdot\!d\ge0$ for all of them. Sufficiency there gives $x+\epsilon d\in U$ for all small
$\epsilon>0$ (inactive disks by continuity, active ones by $2\epsilon v_i\!\cdot d+\epsilon^2|d|^2>0$),
and the step stays inside $D$ because $K\subset B(0,s)\subset D^\circ$ (annulus lemma). Hence every
$x\in K$ is a limit of strictly-uncovered points: **K has no isolated points**, so "S nonempty but
V empty with S a single point" cannot arise. The secondary count argument of C877
(S nonempty $\Rightarrow$ V nonempty) is therefore not needed — V nonempty follows from
maximality anyway (case (e) below).

**(b) Tangency.** A tangency is a *double* intersection and must simply be retained:
circle–circle tangency gives one point (algebraic multiplicity 2), line–circle tangency gives one
point with the line passing through it; both satisfy "$\in S$" verbatim, so they enter V. In
particular a tangency point can never be a maximizer that is missing from V. What must not be done
is discarding it as "not a transverse intersection". Verified numerically:
`review_r21_vertices.py` part (B) takes a separating line exactly tangent to a ring circle at a
point of K (8-disk family, $r=1/2$, $|c_i|=7/10$, boundary covered analytically and by sampling);
the tangent point is in the vertex list and $\max_S=\max_V$ to sampling accuracy ($\le1.6\cdot10^{-7}$)
for 6 splits and 4 hub positions.

**(c) Closed halfplane.** The only place where closedness matters is a maximizer $x^\*$ of
$f(y)=|y-h|^2$ lying on $L$ with *no* active circle. Then $x^\*\in U$, so a segment of $L$ through
$x^\*$ lies in $S$, and $f|_L$ has second derivative $2>0$: no local maximum. Closedness is what
lets the argument start at the boundary at all; using the *open* halfplane would not remove the
case, it would only make "the first point" of $L$ harder to name. With an active circle, $x^\*$
is in V by the definition of part (B) of the vertex list. No further assumption is needed.

**(d) Exhaustiveness of C877's case analysis (my re-derivation).** $\partial S\subset\partial K\cup L$
and $\partial K\subset\bigcup_i C_i$ (K is strictly inside D). If $x^\*\in\operatorname{int}S$: $f$ is
strictly convex, no maximum. Otherwise: (i) $x^\*$ on no circle and not on $L$ — already interior;
(ii) $x^\*\in L$, no active circle — excluded by (c); (iii) $x^\*$ on exactly one circle, not on
$L$ — locally $K$ is the closed exterior of that circle and the side constraint is inactive, so
$f$ restricted to the circle cannot have a local maximum: at a critical point of the restriction
$c=h$ (then $f$ is constant along the circle and moving outward gives $2r>0$) or $u=(c-h)/|c-h|$
(then the outward derivative is $2(|c-h|+r)>0$); outward movement stays in $K$ locally. (iv) on
$\ge2$ circles, or on a circle and $L$ — in V. This covers everything, including coincident
residual topology and internal tangencies (retained, never discarded).

**(e) Why this is enough.** For every $h$, $\max_{x\in S}|x-h|^2=\max_{v\in V}|v-h|^2$; in
particular $S\subset\overline{\operatorname{conv}}V$ (separate a point outside the hull by a far
hub $h=Rn$ and let $R\to\infty$), and the constrained one-centre problem reduces to the finite
minimax $\min_{h\in H}\max_{v\in V}|v-h|^2$ — a 2-D convex problem. R21-HUB-FREE's primal form
("$\bigcap\{B(0,1-r)\}\cap\{B(v,r): v\in V\}\ne\emptyset$") is the same statement; its (a)/(b)
dichotomy is correct (I re-derived it: a boundary point of the intersection lies on a constraint
circle; a feasible arc that ends produces a circle–circle point; an arc that never ends makes the
whole circle lie in every convex disk, hence its centre lies in all of them; empty-interior cases
with a unique active circle are impossible as in (c)).

## 3. Where the real risk is (and its direction)

The theorem is sensitive to *one* ingredient: **membership must be "closure of the
strictly-uncovered set"**, not the naive "all distances $\ge r$". Explicit counterexample to the
naive reading (`review_r21_vertices.py` part (A)):

three centres at $|c_i|=\tfrac12$, $120^\circ$ apart, $r=\tfrac12$; $x_0=0$. Then
$|x_0-c_i|=\tfrac12=r$ for all $i$ (naive test accepts $x_0$), $x_0$ **is** a pairwise
circle–circle intersection (so a naive vertex enumerator lists it), yet the active normals are
$120^\circ$ apart, no direction has $v_i\!\cdot d\ge0$ for all $i$, and indeed a punctured
neighbourhood of $x_0$ is covered by the three disks: $x_0\notin K$.

Direction of the error is the dangerous one: including $x_0$ makes V strictly larger than V∩S,
hence $\max_V>\max_S$ is possible and a *legitimate* two-hub covering can be rejected. So the
naive rule is unsound for the exclusion direction (it can produce false "must be excluded"
readings), while the strict-`>` rule would drop genuine vertices. C877+R21-MEMBERSHIP give exactly
the right filter; the two-sided equality $\max_S=\max_V$ then holds for all $h$.

Two further scope points, both benign but worth pinning:

1. $K\subset B(0,s)\subset D^\circ$ is load-bearing: it supplies (i) $\partial K\subset\bigcup C_i$,
   (ii) "moving outward is admissible" in case (iii), (iii) the escape step staying in D in (a).
   If $|c_i|\le s$ or boundary coverage failed, K could touch $\partial D$ and case (iii) could
   lose its escape direction.
2. The degenerate inner-minimizer case $h=c_i$ (then $f$ is constant along $C_i$) *cannot occur in
   the inward-root application*: hubs satisfy $|h|\le 1-r$, and an inward ring centre with a
   positive arc satisfies $|c_i|>1-r$ (the inward root is
   $d=\cos a-\sqrt{r^2-\sin^2a}\in(1-r,\sqrt{1-r^2}]$ for arc half-width $a\in(0,\arcsin r]$).
   Even if it occurred, case (iii) still excludes it via the outward derivative $2r>0$.

## 4. Exact scope of the reviewed statement

**Confirmed (conditional only on the definitions/annulus lemma):** for finitely many distinct ring
centres with $|c_i|\le s<1$ whose radius-$r$ closed disks cover $\partial D$, for every line
$(n,t)$ and every $h\in\mathbb R^2$,
$$\max_{x\in K\cap\{n\cdot x\le t\}}|x-h|^2=\max_{v\in V}|v-h|^2,\qquad V\subset S,\ V\ne\emptyset
\text{ whenever }S\ne\emptyset .$$
**Not claimed here:** the outer variables (ring placements, $r$, the line) remain continuous —
the lead's own note says this; the vertex set V changes at circle-arrangement and line events; and
$S=\emptyset$ sides are handled by $M_H(\emptyset)=0$. Numerical calibration is
`review_r21_vertices.out.txt` / `.json`; the continuum content is §2, not the sampling.

## 5. Repro

```
py -3 -B research-2026/team-current/r20-geometry/review_r21_vertices.py
```

Outputs: `review_r21_vertices.out.txt`, `review_r21_vertices.json`
(trap distances/verdicts, tangent-line split comparison, 6 split/hub calibrations).
This review is an independent re-derivation (different wording, explicit counterexample,
explicit calibration); it is not an independent research identity and does not upgrade any status.
