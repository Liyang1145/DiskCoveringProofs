# Nine independent normalized metric coordinates

Let x_i=d_i/D, sum x_i=1. Define
(a,b,c,e,f,g,p,q,h)=(x0,x2,x4,x5,x7,x9,x0+x1,x5+x6,x0+x1+x2+x3+x4).
The exact affine inverse is
x=(a,p-a,b,h-p-b-c,c,e,q-e,f,1-h-q-f-g,g).
This is a bijection R9 -> {sum x=1}. In particular
pair34=h-p-b, pair89=1-h-q-f.
No symmetry hypothesis. At the attained candidate a=c=e=g≈.01900717316, b=f≈0, p=q=1/4, h=1/2 (the latter exact identities follow construction symmetry, not rounded values).

Certified C1350 necessary bounds give a,c,e,g in[0,3/64], b,f in[0,1/64], p,q in[7/32,9/32], h in[15/32,17/32]. Additional coupled inequalities constrain h-p-b and1-h-q-f to[7/32,9/32]. These are constraints, NOT new independent parameters. Retain them in exact polytopes; dropping them is only an outer relaxation.

A product box in these9 coordinates has exactly512 mapped vertices and trivially certified completeness by multilinear convex weights. It can replace a large clipped polytope only as an OUTER domain, never as an equal domain unless every original inequality is proved redundant. Some outer vertices can have negative reconstructed x_i; flow certificates remain valid at any anchors and thus can still bound the relaxed domain (provided the common angular branch and concavity checks hold). Such vertices must not be treated as geometrically admissible covers or used with lemmas requiring nonnegative deficits.

This representation is a possible controlled alternative if repeated cuts cause vertex growth: compare robust bound quality on the natural outerbox and originalpolytope before scaling. Not yet adopted in bearing certificates.
