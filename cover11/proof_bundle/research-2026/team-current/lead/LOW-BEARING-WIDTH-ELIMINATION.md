# Low-bearing width elimination

Fixed exact frozen seven-factor objective, physical r∈[.379,.37999], R0=.38. For either adjacent width branch j=0,1, let acos(r)/2≤b≤1 and g≤w≤Wmax, where g is the established width lower bound of interval_joint_patch.py and
 x0=2b-acos r, D=1-r cos x0, X=r sin x0,
 Wmax=2 atan2(X,D).
Empty width intervals are discarded. These are necessary width domains of C849 (not arbitrary configurations).

Use the exact cancelled width objective
 W=-r sqrt(1-r²)sin²b+(.5-mu)w+x/2+(mu+h)eta-d q/R0²-l sqrt(q)/R0,
 p=D cos w+X sin w, x=X cos w-D sin w,
 q=x²+(1-p)², eta=atan2(x,1-p).
The second-order interval AD in check_width_curvature.py evaluates this full smooth extension (not physically clipped). Since |D+iX|<1 on this bearing domain, 1-p>0 and q>0 for every w; any broad-box inability to verify this is only a refusal/subdivision.

## Derivative certificate
certify_width_monotone.py covers r with outward endpoints, b∈[acos(.38)/2,1] (a superset), and w∈[g,2asin(.38)]. Boxes are discarded only if X<0 or w>Wmax, or have a strictly positive interval W_w. Both children are retained in every bisection. It terminates at 330 evaluations, 0 live: 42 geometrically empty and 124 positive-derivative leaves, for the two coefficient branches combined. Minimum certified W_w lower bound is >.000694238531825579. Frozen and all source hashes are pinned in width_monotone_certificate.json. Positive-width cases with b near lower limit are included, not projected.

Thus W is strictly increasing on every legal width interval; allowing the whole interval up to Wmax can only enlarge the feasible set. Both branches achieve their relaxed width maximum at Wmax.

## Explicit endpoint value
Rotating D+iX by exp(-i Wmax) yields D-iX. Thus p=D, x=-X, 1-p=r cos x0, q=r² and eta=-x0. Therefore
 W_endpoint(r,b)= -r sqrt(1-r²)sin²b+(.5-mu)*2atan2(X,D)-X/2-(mu+h)x0-d(r/R0)²-l*r/R0.
No implicit root or width supremum remains on a side with b≤1. If both bearings are≤1, both width variables disappear; if only one is≤1, one disappears. This is a rigorous upper reduction for the flat seven-factor patch, not a circle-boundary objective bound and not the global n11 optimum.

The global-concavity shortcut is false: check_width_curvature.py certifies W_ww>.5559 (branch0), >.5723 (branch1) at r=.379,b=.9,w=.19, with q strictly between the legal gate and r². Monotonicity, not concavity, supplies the reduction.

## Independent explicit-derivative replay
Let cn=D²+X². Since p'=x, x'=-p and eta'=(cn-p)/q,
 W_w=.5-mu-p/2+(mu+h)(cn-p)/q+2d*x/R0²+l*x/(R0 sqrt(q)).
`control_width_monotone_explicit.py` uses this formula and the intersected identities q=x²+(1-p)²=1+cn-2p, no Jet or second-order AD. It closes the SAME outward domain at150evaluations,0live(24illegal,52positiveleaves), minlower>.005475999538554175. Source hash/result width_monotone_explicit_control.json. Sameintervalarithmetic backend, independent derivative inference. This control is not merely point sampling.
