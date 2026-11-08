# Boundary fan correction for 26 congruent disks

This addendum to PROOF.md proves r_D(26)>457/2000 = 0.2285. Use
U=228501/1000000 in the normalization and the abstract Voronoi dual.
The geometric reductions, the signed-area identity, the concavity of G_U,
and the one-edge and two-edge face group bounds from PROOF.md apply at U.

Keep the sign of the owner triangle area in the signed-area identity.
For its arc of half-angle delta, write s=sin(delta), c=cos(delta),
h=sqrt(U^2-s^2), and let the site coordinates in the radial and tangential
frame of the arc midpoint be (c-h+x,y). The two anchors are (c,+s) and
(c,-s). Their distance constraints imply 0<=x<=2h and
|y|<=sqrt(U^2-(x-h)^2)-s <= hx/s. The last inequality is the tangent
bound for the concave square-root function at x=0. Consequently the
site is at distance at most Ux/s from the ideal position (c-h,0).

Adding the signed owner triangle area to its circular segment area gives
exactly delta-s(c-h+x)=G_U(delta)-sx. Let d=pi/b, and define
J(delta)=G_U(d)+G_U'(d)(delta-d)-G_U(delta).
Both J and sx are nonnegative. Since the half-angles sum to pi, the
total fan contribution is b G_U(d)-sum_i R_i, where R_i=J(delta_i)+s_i x_i.

Allocate half of R_i to each of the two boundary edges incident to owner i.
Assign each switch triangle to its adjacent center-only triangle as in
PROOF.md. The one-edge group already loses more than 0.0387 U^2,
by the same Young bound and an exact comparison. A two-edge group loses
more than 2(0.0405)U^2 by the same common-disk Heron bound.

For b=16 or b=17, target a loss of 0.0405 U^2 per edge. In a one-edge group,
if the two incident residuals sum to at least B=2(0.0405-0.0387)U^2,
their allocated halves already supply the additional loss. Otherwise
both incident half-angles lie in [d-w,d+w], with w=0.008 for b=16 and
w=0.009 for b=17. Indeed, the checker verifies J(d-w),J(d+w)>B, and J is
convex with its minimum at d. The sum of the two quantities s_i x_i is <B.

Write l=d-w, u=d+w and a(t)=cos(t)-sqrt(U^2-sin(t)^2).
The ideal sites have radii in [a(l),a(u)] because
a'(t)=sin(t)(cos(t)/sqrt(U^2-sin(t)^2)-1)>=0.
Their rays differ by the sum of their half-angles, at most 2u.
The law of cosines bounds their ideal separation by
sqrt((a(u)-a(l))^2+4a(u)^2 sin(u)^2).
The two deviations from the ideal sites sum to at most U B/sin(l)^2.
The checker verifies that the resulting upper bound for L/U is <1.563.
On [0,1.563], f(t)=t/2+t sqrt(1-t^2/4) is increasing, by concavity
and its positive derivative at 1.563. The shared-edge estimate therefore
bounds the group by U^2 f(1.563), yielding a loss >0.0405 U^2 even
before counting its allocated residuals.

Thus the area upper bound is
(50-b)(3sqrt(3)/4)U^2 + b U^2/2 + b G_U(pi/b) - b e_b U^2,
where e_b=0.0405 for b=16,17 and 0.0387 otherwise.
The companion checker proves this is strictly less than pi for all
13 possible b. All decisions use outward-rounded BigInt interval
arithmetic. The printed gaps are approximate displays of lower bounds.
The sine, cosine and arctangent bounds use consecutive alternating
partial sums on [0,1], and pi uses Machin's identity. Run with Node.js:
`node verify_fan_correction.js`.

The strict enlargement and compactness arguments from PROOF.md finish
the lower bound. The optimal radius remains open.

