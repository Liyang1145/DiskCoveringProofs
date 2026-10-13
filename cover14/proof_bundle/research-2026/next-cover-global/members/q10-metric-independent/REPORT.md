# Two analytic four-gap cuts for q10/m4 index 879

Route: independent reasoning in current context; model/provider route unverified. No optimization or catalogue reruns. Scope: necessary conditions for the *abstract incidence witness system*, hence also for extracted covers; not a global optimality proof.

## Input and indexing

Read STATUS.md, DEAD.md, lead/k10-catalogue-corrected.json entry `10/4[879]`, candidate-catalogue-match.json, STRESS-OBSTRUCTION.md and DUAL-SLACK-LOCALIZATION.md. The human's latest premise (q11 removed, only 879 remains) is stronger than the historical STATUS head. No independent assertion about that newer reduction is made here.

Use production labels: A_j lies on the unit circle and is incident to owners j,j+1 (indices mod 10). Let theta_j=arg(A_{j+1})-arg(A_j), in the common cyclic branch; d_j=L-theta_j>=0, sum d_j=10L-2pi, L=2asin U, U=0.33173203427623414 exactly as a terminating decimal. Owner i is constrained by anchors A_{i-1},A_i, so its arc width is t_i=theta_{i-1}, NOT theta_i.

The catalogue faces imply hub 10 is within 2r of each owner 9,0,1,2, and hub 12 is within 2r of each owner 4,5,6,7. This uses the triangle inequality along a common face witness; witnesses may differ between owners. Explicit end incidences: (0,9,10), (1,2,10), (4,5,12), (6,7,12).

## Proved structural gain

Every feasible incidence system at r<=U satisfies BOTH strict inequalities

    d_8+d_9+d_0+d_1 > 1/10,
    d_3+d_4+d_5+d_6 > 1/10.                         (A)

The two sums are disjoint; the two omitted deficits are d_2,d_7. In particular,

    d_2+d_7 < 10L-2pi-1/5.

For polytope processing the weaker CLOSED cuts with >=1/10 are safe. Their intersections generate new vertices; merely retaining old simplex vertices is invalid. In fact these two cuts remove EVERY original simplex vertex: at such a vertex one of the two disjoint sums is zero. This does not prove emptiness of the cut polytope.

No symmetry WLOG, candidate sharp stress, nearest-circle hypothesis, or local reference labeling is used.

## Exact owner-lens support lemma

Let an owner's two unit anchors have angular separation t in [0,L], midpoint direction e, and positive tangent direction tau. Set

    c=cos(t/2), s=sin(t/2), h=sqrt(U^2-s^2).

Writing its site x=c e+u e+v tau, the two endpoint inequalities |x-A_-|,|x-A_+|<=U are exactly

    u^2+v^2+2s|v| <= h^2.                          (B)

Consequently, for a unit vector n with a=|n.e|, b=|n.tau|, the support of the centered lens is

    H_t(n) = h a                 if b<=s/U,
             U-s b             if b>=s/U.         (C)

At equality the branches agree. Proof: by reflections take u,v>=0 and maximize au+bv subject to u^2+(v+s)^2<=U^2. The unconstrained disk support occurs at (u,v)=(Ua,Ub-s), legal iff Ub>=s. Otherwise the maximum occurs at v=0,u=h. This proof includes h=0 by continuity (and directly from B).

Also

    h^2 = sin^2(L/2)-sin^2(t/2)
        = integral_t^L (sin z)/2 dz <= U(L-t),    (D)

since 0<=z<=L<pi/2 and sin(z)/2<=sin(L)/2=U sqrt(1-U^2)<U. The weaker coefficient U is enough below.

## Four-owner fan proof

Consider four consecutive owners a,a+1,a+2,a+3 with a common hub at distance <=2U from each. Let their owner deficits be delta_i=L-t_i and S=sum of these four deltas. Assume, toward contradiction, S<=1/10.

The angular separation of the midpoint directions of the first and fourth owner's anchor chords is

    Delta=t_a/2+t_{a+1}+t_{a+2}+t_{a+3}/2
         =3L-S+(delta_a+delta_{a+3})/2.

Thus 3L-1/10<=Delta<=3L<pi. Take n as the unit direction from midpoint direction e_a to midpoint direction e_{a+3}. Elementary circle geometry gives

    n.e_a=-sin(Delta/2), n.e_{a+3}=sin(Delta/2),
    |n.tau_a|=|n.tau_{a+3}|=cos(Delta/2).

Every individual t_i>=L-1/10. The elementary bounds below give

    sin(t_i/2)/U > .28/.332 > .8,
    cos(Delta/2) < .8.

Hence the vertex branch of (C) holds at both endpoint owners. Their projected separation is therefore at least

    n.(x_{a+3}-x_a)
      >= (c_a+c_{a+3}-h_a-h_{a+3}) sin(Delta/2).  (E)

From (D) and Cauchy--Schwarz,

    h_a+h_{a+3} <= sqrt(2U(delta_a+delta_{a+3}))
                <= sqrt(2US) < .258.

Also each c_i>=sqrt(1-U^2)>.9433 and sin(Delta/2)>.82. Thus (E) is strictly greater than

    (2*.9433-.258)*.82 = 1.335452 > 1.328 > 4U.

But the common hub gives |x_{a+3}-x_a|<=4U, a contradiction. Therefore S>1/10. Apply a=9 (hub10) and a=4 (hub12); convert owner deficits delta_i=d_{i-1} to get (A).

### Elementary constants, no numerical optimization premise

All decimals below are exact rationals. We have .3317<U<.3318<.332.

* L>.676: sin(.338)<=.338-.338^3/6+.338^5/120<.3317<U.
* L<.68: sin(.34)>=.34-.34^3/6>.332>U. Hence L<pi/2 and 3L<pi (using pi>3.14 suffices).
* sqrt(1-U^2)>.9433 follows .9433^2+.3318^2=.99990613<1.
* t_i/2>(.676-.1)/2=.288; sin(.288)>=.288-.288^3/6>.28.
* Delta/2>(3*.676-.1)/2=.964. As Delta/2<pi/2, sin(Delta/2)>sin(.964)>.82. The last inequality follows the rational lower polynomial x-x^3/6+x^5/120-x^7/5040 at x=.964.
* cos(Delta/2)<cos(.676)<=1-.676^2/2+.676^4/24<.8.
* sqrt(2U/10)<sqrt(.0664)<.258 because .258^2=.066564.

Alternating Taylor bounds apply on [0,1]. These are analytic rational checks; no saved floating calculation is bearing. Eight exact Fraction arithmetic controls pass in `rational-controls.json`; reproduction: `py -3 -B research-2026/next-cover-global/members/q10-metric-independent/rational_controls.py`. The checks verify constants, not the geometric interface.

## Stronger anchor-only nonlinear cut (optional)

For any pair of owners a,b sharing a hub, form their lens midpoints m_i=c_i e_i. For every unit n, necessarily

    n.(m_b-m_a) <= 4U+H_{t_a}(n)+H_{t_b}(n).      (F)

This is immediate from the support formula and |x_b-x_a|<=4U. Unlike a single fixed sharp stress, (F) adapts analytically to the current arc widths and has the cap's square-root behavior explicitly. Formula (E) is its sharp vertex-branch specialization. The branch must be checked; one cannot use h|n.e| for all angles.

(A) is a deliberately conservative affine consequence useful immediately. Improving 1/10 can be reduced to a small analytic scalar extremum, but no larger constant is claimed here. The lemma will not by itself prove r>=r*: it only removes metric classes with insufficient deficit on either long four-owner fan. It may overlap regions already excluded by lead's piecewise flows; no quantitative speedup is asserted.

## Original target / remaining gap / next action

Original target: unrestricted n14 optimality at the attained exact r*. Remaining implication: every q10/879 anchor metric outside the certified candidate neighborhood must be excluded (or otherwise lower-bounded by r*). The two affine cuts reduce, but do not settle, that continuum.

Next action: intersect the lead's remaining q10 anchor cells with the two CLOSED halfspaces in (A), reconstruct complete intersection vertices, then reuse existing flow certificates/local bridge. Do not rerun topology enumeration. This is a proposal to the lead, not a computation performed in this report.
