# B17 must retain actual inner-core coverage, not only present rods

Scope: any cover of the closed unit disk by at most26 disks of common radius
rho<=U=234701/1000000, with17 distinct cyclic boundary owners under the
existing ownership reduction. No symmetry, stationarity or triangulation is
assumed. This is a new elementary necessary condition, not a global lower
bound or a source acceptance.

Set R=1-2U=265299/500000. Each boundary owner's center has norm at least
1-rho, because its disk meets the unit circle. If |x|<R, its distance to
any such center is greater than 1-rho-R=2U-rho>=rho. Consequently boundary
owners miss the open core disk of radius R. The at most9 nonowner disks cover
that open core; their finite closed union therefore covers its closure.
In particular, they cover the ENTIRE core circle of radius R and the origin.

We have R>2U>=2rho. A disk of radius rho intersecting the core circle has
at most one connected positive-length arc, of length less than a half turn:
if its center has norm t>0, its circle intersection is
cos(theta-theta_center)>=(R^2+t^2-rho^2)/(2Rt)>0.
A center at zero cannot reach the circle because rho<R.

If that arc had length at least1/6turn, its endpoint chord would have length
at least2R sin(pi/6)=R>2rho, impossible for two points in a radius-rho disk.
Thus EVERY positive-length arc has length STRICTLY below1/6turn. Six such
disks cannot cover the full circle: the length of their union is at most the
sum of their arc lengths, which is strictly less than one full turn.
At least SEVEN nonowner disks have positive-length core-circle intersection.

Every one of these seven centers satisfies

R-rho < |c| < R+rho,

and hence lies in the FIXED conservative open annulus

1-3U < |c| < 1-U,

whose exact radii are295897/1000000 and765299/1000000.
An additional nonowner disk covers the origin, so its center has norm
at mostrho<=U. It is DISTINCT from all seven annulus centers, since
1-3U>U. Thus B17 covers need at least eight nonowner disks, and at most
eight of their at most nine nonowner disks can meet the core circle.

An optional finite-point relaxation retains six regular-hexagon vertices on
the core circle and the origin. Every pair of distinct hexagon vertices is
at distance at leastR>2rho, and every vertex is at distanceR from the origin.
These seven points therefore require SEVEN DISTINCT nonowner disks.
The finite-point condition alone is weaker than full core-circle coverage
and must not be presented as its equivalent.

## Actual obstruction found in the eight previously narrowed source states

The exact witness report
outputs/n26-b17-eight-actual-radial-relaxation-witnesses-v1.json
constructs below-Rstar realizations of ALL present rods and the new inward
boundary-owner/short-gap constraint for all eight selected actual prefixes.
These are NOT disk covers. Their nonowner centers have norm about0.8,
so none lies in the required inner annulus and all miss the origin.

This proves that no sound method using ONLY those present-rod inequalities,
the original angular domain and the single inward-owner constraint can
exclude those eight necessary-model domains. It does NOT prove that their
true covers are feasible, that their full descendant rod graphs are
feasible, or that global n26 infeasibility is false. Additional future-face
constraints or actual inner-core coverage constraints are indispensable.

No frozen source, executor, paid leaf, history or strict ledger is changed.
The new condition is not yet admitted to the current enumeration. Whole-state
exclusion still needs complete branch coverage, independent source binding,
and the actual geometry/current/final chain before any payment.
