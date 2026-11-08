# Uniform strict slack and finite generic-position reduction

This is a universal geometric ingredient, not a final unrestricted reduction
acceptance, a complete catalogue or a new current payment. The polynomial
checker supplies exact algebra and explicit nonzero witnesses. The following
ordered-real, continuity and density argument is separate from those checks.

Suppose m closed disks of common radius r cover the entire closed unit disk D,
with 1<=m<=26 and 0<=r<rho<1. Set epsilon=(rho-r)/2>0. Project every outside
centre onto D. The previously checked universal projection identity proves
that this cannot lose any point of D, so the projected centres still cover D
at radius r. Nothing assumes the candidate's symmetry or stationarity.

Choose 0<eta<min(epsilon/2,1/2) and multiply every projected centre by 1-eta.
Every shrunken centre has norm at most 1-eta, and moves by at most eta.
Perturb each shrunken centre by less than
delta=min(eta/2,epsilon/2). Such choices lie in a nonempty open subset of
R^(2m), remain strictly inside D, and move every original projected centre by
less than eta+delta<epsilon. For each p in D, choose one of its original
covering centres. The triangle inequality then gives its distance to the
perturbed centre at most r+epsilon<rho. This is a uniform implication for
EVERY p, not a finite covering sample or a claim about an optimizer.

The norm-change and two-dimensional Cauchy-Schwarz polynomial identities
support the distance inequality: the square of the norm of a sum is at most
the square of the sum of norms, whose nonnegative square roots give the
triangle inequality. Exact radial-shrink identities and the half-slack
identity are supplied separately.

## A finite algebraic exceptional set

For centres a,b,c,d, put v1=b-a, v2=c-a,
b1=|b|^2-|a|^2, b2=|c|^2-|a|^2 and
Delta=v1x*v2y-v1y*v2x. Exclude, for every applicable index choice:

1. |a|^2=0 (a zero centre).
2. |b-a|^2=0 (coincident centres).
3. Delta=0 (three collinear centres).
4. det[(centre_x,centre_y,|centre|^2,1)] for four centres equal to zero.
   For noncollinear triples this is exactly four cocircular centres.
5. b1^2-4|v1|^2=0. Since v1!=0, this is exactly tangency of the pair's
   bisector 2*v1.p=b1 to the unit circle.
6. X^2+Y^2-4*Delta^2=0, where
   X=b1*v2y-b2*v1y and Y=v1x*b2-v2x*b1.
   Since Delta!=0, Cramer's rule gives the unique triple bisector
   intersection p=(X,Y)/(2*Delta); the polynomial is zero exactly when
   this point lies on the unit circle.
7. (1+|a|^2-rho^2)^2-4|a|^2=0. For a!=0 and 0<rho<1,
   the equation of the two circle boundaries is
   2*a.p=1+|a|^2-rho^2 with |p|=1. This is their tangency condition.

The checker gives a nonzero exact rational evaluation for each of the first
six polynomials. For the seventh, evaluation at a=0 is
(1-rho^2)^2>0 for EVERY fixed 0<rho<1. A witness used to prove a polynomial
nonzero need not itself satisfy all the other general-position conditions.
These witnesses prove nonzeroness, not coverage of D by sampled points.

For any fixed rho in this interval, all these polynomials are therefore
nonzero polynomials in the centre coordinates. A nonzero real polynomial
cannot vanish on a nonempty open box: induction on the number of variables
reduces this to the fact that a nonzero one-variable polynomial has finitely
many roots. If it vanished throughout a box, every coefficient polynomial
would vanish on a lower-dimensional box, making all coefficients zero.
The real polynomial ring is an integral domain, so the finite product of
the listed nonzero polynomials, over all applicable labels, is nonzero.
Its zero set cannot contain the open perturbation region above. Consequently
one can choose final centres satisfying ALL seven exclusions simultaneously
while preserving the uniform strict cover at rho.

No probabilistic or floating-point perturbation is used as proof of this
existence claim. The argument also covers repeated original centres: their
generic final perturbations become distinct before any redundancy removal.

## Irredundancy and the clipped Voronoi diagram

Now remove redundant disks from this finite radius-rho family until an
irredundant subcover remains. Deletion terminates and retains every listed
general-position condition, because each condition is imposed on all
applicable subsets of the original perturbed family. Every retained disk has
a private point not belonging to any other retained closed disk.

At that point its centre is strictly closer than every other centre.
Continuity of the finitely many squared-distance differences gives a
neighbourhood with the same unique nearest centre. Its intersection with
the interior of D is nonempty, even when the original private point lies on
the unit circle. Thus every retained clipped Voronoi cell has a nonempty
two-dimensional interior. At any point of D, its nearest centre covers it,
because the entire family covers D and nearest distance is no larger than
the distance to a covering centre.

The exclusions prevent four-centre interior ties, collinear triple centres,
triple ties on the unit circle, bisector tangencies to that circle and
isolated tangent disk footprints. These are the particular generic-position
conditions used in the written no-return and triangular-dual bridge. This
does NOT itself prove the full simple triangular-disk dual, its boundary
transport, starring when m<26, the n-specific four-family counts, the
external eight-disk theorem, all lower classifications or final joint
acceptance. Those obligations remain explicit; no frozen geometry flag
or global proof level is changed by this ingredient.
