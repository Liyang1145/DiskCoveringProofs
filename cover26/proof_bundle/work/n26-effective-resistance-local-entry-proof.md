# Effective-resistance localization into the unchanged original LOCAL box

This is a new continuous necessary-realization lemma, not a current admission,
whole-root closure, or a change to any old certificate. Its source must be
the actual original92-rod/62-vertex positive candidate network, with16 unit
circle anchors,26 original centers and20 independent actual face witnesses.
It is not the full134-rod model and does not import a typed geometry cache.

## 1. Grounded square completion and coordinate resistance

Let L be the rational weighted Laplacian, and partition it into anchor A and
free F blocks. Positive weights and a path from every free vertex to an anchor
prove G=L_FF is positive definite. Write H=-G^{-1}L_FA. The actual exact
inverse certificate and integer products verify G^{-1} and H; each row of H
is nonnegative and sums to one.

For ANY displacement h=(h_A,h_F), in each Cartesian coordinate, completing
the square gives

    h' L h = h_A' S h_A + z' G z,   z=h_F-Hh_A.

The Schur form S is nonnegative, either by minimizing the original positive
edge sum or by its checked nonnegative pair weights. For a free vertex v put
R_v=(G^{-1})_vv>0 and u=G^{-1}e_v. For every scalar vector z the EXACT identity

    R_v z'Gz-z_v^2
      = R_v (z-z_v u/R_v)'G(z-z_v u/R_v) >= 0

follows from Gu=e_v and u'Gu=R_v. Apply it separately to both Cartesian
coordinates and sum. If E=sum_e w_e |h_u-h_v|^2, then

    |h_v-(Hh_A)_v| <= sqrt(R_v E).

Thus, for per-anchor bounds |h_a|<=epsilon_a,

    |h_v| <= beta_v+sqrt(R_v E),
    beta_v=sum_a H_va epsilon_a.

No harmonicity of the ACTUAL realization is assumed: the deviation z remains
and is explicitly paid. R_v is the resistance to the wired grounded anchor
set, not a resistance to one arbitrarily selected anchor. It is at most the
resistance of any explicit positive path from v to an anchor, by the same
path Cauchy inequality and the variational minimum. The implementation
checks this comparison exactly for every actual free vertex.

## 2. Existing reference energy, with sharper displacement transfer

Use the SAME original rational reference positions p, positive weights w and
same-root squared-radius upper endpoint t_plus. Put

    W=sum w, E0=sum w |p_u-p_v|^2,
    g_v=sum_(vw) w(p_v-p_w), r_v=||g_v||_1.

The necessary rods have length <=rho<=Rstar, so their actual weighted energy
is at most W*t_plus. Edgewise expansion yields

    E <= W*t_plus-E0-2 sum_v g_v.h_v.

For each unit anchor define k_a=(g_a.p_a)/|p_a|^2>0 and s_a=g_a-k_a p_a.
The exact unit-circle identity is

    -2g_a.h_a=k_a(|p_a|^2-1+|h_a|^2)-2s_a.h_a.

The original closed angular intervals contain the exact candidate and select
the same short branches. Endpoints and EVERY contained quarter-turn give
whole-arc Cartesian enclosures, hence epsilon_a. Then

    A = W*t_plus-E0+sum_a k_a(|p_a|^2-1)
        +sum_a(k_a epsilon_a^2+2||s_a||_1 epsilon_a)
        +2 sum_(v free) r_v beta_v,
    K = 2 sum_(v free) r_v sqrt(R_v)

give E<=A+K sqrt(E). Every square root in the computation is rounded UP.
With A0=max(A,0), this implies

    sqrt(E) <= (K+sqrt(K^2+4A0))/2.

Using A0 is a deliberate safe relaxation when A<0; a negative A is NOT
called emptiness or silently interpreted as a negative square root.
The implementation also verifies the final rational Y satisfies
Y>=0 and Y^2-KY>=A0. This is sharper than the old K+sqrt(A0) bound.

## 3. Original52 coordinates, not an enlarged local theorem

For each of the26 centers add the independently enclosed distance from p_v
to the exact rotated root center. The resulting bound

    beta_v+sqrt(R_v)*Y+reference_rounding_v

applies to ANY corresponding necessary rod realization; no center or face
witness neighborhood is a hypothesis. Accept entry only if EVERY center's
Euclidean error is STRICTLY below the original bound LOCAL halfwidth
7/800000. Rotating back preserves Euclidean errors and therefore every
original coordinate error. The existing full52-coordinate local theorem
then excludes rho<Rstar.

LOCAL means a lower bound, NOT emptiness at equality. The exact candidate
must remain admissible. No D2 symmetry is imposed on competitors, no witness
is assumed to be a circumcenter, and no134-rod inverse is relabelled as the
old46-free inverse.

## 4. Evidence and remaining scope

The old path-pin implementation, all live/frozen executors, source root rows,
old nonOPEN nodes, support tables, paid ledgers and LOCAL width stay unchanged.
New arithmetic diagnostics may compare the two bounds and list actual OPEN
leaves that satisfy the stronger lemma. They do not change those leaves.

Admission still requires the ACTUAL entire latest source/model/history gate,
full original source association, distinct complete closed-forest retention,
OWN/publication, latest-current composition and independent final. An
arithmetic preparation object is NOT a faster geometry source or accepted
model cache. Failure to localize a whole box leaves it wholly unresolved.
This lemma alone proves neither catalogue completeness nor n26 optimality.
