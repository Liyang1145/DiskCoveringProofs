# Ten-disk gap yields quantitative separation (analytic)

Assumptions: global C450/C451 at s=19/50: every11disk cover of unitD at radius<=s has exactly9boundary-contacting disks and2indispensable interior disks. Centers arbitrary. We use no symmetry, saturation or positive-metric premise.

## 1. Ten disks cannot cover at radius s
Suppose10closed disks radius s coverD. A radius s disk covers at most2asin(s) of unit-circle arclength. Because8asin(s)<pi, at least9of the10disks contact the unit circle (positive total arc needed). Append one new radius s disk internally tangent to unitcircle at a direction distinct from all existing centers. This produces11disk cover with at least10boundary-contacting disks, contradicting C451 (contact includes tangency). Thus no10disk cover at radius<=s; smaller radius can be enlarged to s first.

## 2. Every pair in an11disk cover is separated
Let11radius r<=U<s disks coverD and centers ci,cj at distance d. Replace their two disks by one centered at midpoint m and radius r+d/2; enlarge remaining9disks to same radius. Triangle inequality B(ci,r) union B(cj,r) subset B(m,r+d/2) proves10disks coverD. Therefore r+d/2>s and
 **d>2(s-r)>=2(s-U)=:delta>0**.
This is global for every pair, no inward representative needed. For rigorously certified candidate upper choose simple exact U=37999/100000=.37999, giving delta=1/50000=.00002. Existing C249 upper<U and C825 lower>3/8 ensure relevant covering radii in(3/8,U]. This deliberately sacrifices tight constants for explicit rational bounds.

## 3. Uniform site-face and switch bounds after inward replacement
After inward replacement at actual allowanceR in[3/8,U], it is again an11radiusRcover, hence all site distances>delta. Site triangle circumradiusrho<=R<=U has every sine-law angle a satisfying sin a=d/(2rho)>delta/(2U)=1/37999. Thus
 **asin(1/37999)<a<pi-asin(1/37999)**.
In particular no site triangle can become collinear within this bounded-R genuine-cover family, even in limits. Every site-face circumradius is>delta/2.

For switch P between ci,cj, let rho=|P-ci|=|P-cj|<=R, d=|ci-cj|, midpointm. Withb half the angle atP, sin b=d/(2rho)>1/37999. All inward site norms<=sqrt(1-R²): ring byroot reduction, hubs even<=1-R. Hence |m|<=sqrt(1-R²). Isosceles height |P-m|>=1-|m|>=1-sqrt(1-R²). Since cosb=|P-m|/rho,
 **cos b >= (1-sqrt(1-R²))/R = R/(1+sqrt(1-R²)) >= R/2 >=3/16**.
Therefore asin(1/37999)<b<=acos(3/16)<pi/2. All20factor local radiirho>delta/2 and<=U; their actual ratios bounded between1/37999 and37999. In the C839 rootface gauge gamma_f=rho_f/rho_0, this gives explicit box
 **1/37999<gamma_f<37999**.
This is much stronger than multiplying19tree sine bounds. It follows from global no10cover gap, not arbitrary log cutoff; necessary search domain for inward genuine covers or exact-model realizations known to satisfy inward bounds. Pair separation and local radii apply to ANY C835 realization withR<=U. Switch cosine bound additionally uses inward norms; do not impose it on arbitrary C835 models unless inward necessity suffices for the lower-bound direction.

## Remaining singularity
This does not yet give a positive lower bound for sector triangle height or exclude alpha=pi limits. Widths in genuine nearest diagrams satisfy w_i>=2pi-16asinU>0 (nine widths sum2pi, every otherwidth<=2asinU). Sector chord lengths therefore bounded below; endpoint radii also bounded below. At alpha=pi, atan2-based sector angles require continuous boundary interpretation (L=T=0, nonzero chord), not invalid zero denominator. A closed-domain compactification may retain such sector degeneracy; no claim all29triangles uniformly positive. C837 strict-allowance infimum argument remains available.
