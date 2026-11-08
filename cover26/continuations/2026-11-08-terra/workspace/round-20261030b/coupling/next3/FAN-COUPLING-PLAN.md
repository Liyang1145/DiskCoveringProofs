# Proposed joint fan/center-edge/face bound

This file records a proof route and a numerical diagnostic, not a new certified lower bound. The already certified next2 result is unchanged.

## Variables and exact constraints

Fix U and one boundary owner's consecutive anchors q_-,q_+ separated by angular width 2d, with s=sin d, c=cos d and h=sqrt(U^2-s^2). In an orthonormal frame about their chord midpoint, express the center as

    center=(c+x)e_rad + y e_tan.

Both anchors being covered gives

    x^2+(s+|y|)^2 <= U^2,
    |x|<=h,

and center being in the unit disk implies x<=1-c. The owner triangle area is s|x|; its deficit from the prior fan maximum is

    E(d,x)=s(h-|x|) >= 0.

If x<=0, put z=x+h, and define the ideal inner center a(d)=(c-h)e_rad. Then 0<=z<=h and the exact lens inequality gives

    2s|y| <= 2hz-z^2,
    |y| <= hz/s,
    |center-a(d)| <= (U/s)z,
    E(d,x)=s z.

This argument is valid only for s>0. Endpoint s=0 must be separately handled by continuity or a coarse bound. If x>0, the deficit is s(h-x), and x<=1-c; that branch cannot be silently treated as the inner branch.

For two adjacent owners with half-angles d,e, their ideal radial vectors differ in direction by d+e. With their ideal radii a_d=c_d-h_d, a_e=c_e-h_e, the ideal center distance is

    L0^2=a_d^2+a_e^2-2 a_d a_e cos(d+e).

When both owners are on their inner branches, their actual common boundary-edge length satisfies

    L <= L0 + U(z_d/s_d+z_e/s_e).

The previously certified shared-edge lemma bounds an incident internal face A and switch triangle C using L/U=x:

    A+C <= U^2 [x/2+x sqrt(1-x^2/4)].

For a two-edge ear with boundary side lengths L1,L2, the same internal triangle also satisfies A<=L1 L2/2. Thus a complete proof must minimize fan deficits plus appropriate one-edge or two-edge face/switch deficits over all allowed d,e and z variables, with every owner charged once, respecting sum d_i=pi and 14<=b<=26. A finite rational-interval certificate could partition the angle domains, retain the analytic slack inequalities above, and bound a weighted local potential; a rigorous treatment of the positive-x and small-s branches is mandatory. Independent local maxima of fans and center faces are insufficient.

## Diagnostic only

At U=.23 and b=17, equal half-angles pi/17 and saturated inner fans have ideal center-edge length L0/U approximately 1.34958. The prior shared-edge face+switch deficit there is approximately 0.12824 U^2 per single-edge face. If an ear had two such side lengths, the elementary A<=L1 L2/2 would alone force a face deficit of approximately 0.388 U^2. The existing independent area sum at these parameters exceeds pi by approximately 0.07894, so these two geometric effects are of a potentially useful size.

The equal-angle calculation is not a necessary condition: owners can have unequal angles and nonzero fan deficits, and each face must be charged at most once. Optimizing a deliberately crude independent fan/edge bound numerically gives no certified exclusion; no conclusion for U=.23 follows from this diagnostic. The next concrete obligation is a full-domain local-potential inequality whose sum accounts for k=1 and k=2 face incidence separately and closes the strict area gap for all b.
