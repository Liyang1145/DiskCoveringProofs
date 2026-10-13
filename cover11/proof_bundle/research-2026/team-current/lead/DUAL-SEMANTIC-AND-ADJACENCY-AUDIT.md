# Semantic interface audit of C450 and the new hub-adjacency consequence

Scope: R=19/50, e in [0,7/50], hub reference h=(e,0); any disk B(c,R) meeting S(0,1). This checks the analytic semantics of verify_directional_fixed.py independently of the original limiting-circle motivation. The separate arithmetic/domain audit is flash-compute/AUDIT-C450-DIRECTIONAL.md. No new optimization or numerical assumption is used here.

## Exact single-disk quantity

Write c=rho(cos(phi),sin(phi)), rho in [1-R,1+R]. The outer-circle intersection is phi+[-t,t], with cos(t)=(1+rho^2-R^2)/(2rho), 0<=t<=asin(R). Solving gives both rho=cos(t) +/- sqrt(R^2-sin(t)^2). Tangencies t=0 are allowed. For v=cos(phi), cos(k phi)=T_k(v), k=1,2,3.

Relative to h, ell^2=(rho-e)^2+2rho e(1-v), ell>=1-R-e>=.48>0; cos(psi)=(rho v-e)/ell. The disk meets S(h,R) in the arc psi+[-b,b] where b=acos(ell/(2R)) if ell<2R, and b=0 otherwise. There is no full-circle or ell=0 branch in this domain. Its maximum b has cos(b)>=.48/.76=12/19>.6, precisely inside the implemented acos interval.

For either target circle, with angular weight W(theta)=a0+sum_{k=1}^3 ak cos(k theta), half the integral over the intersection arc equals

 a0*t + sum ak*sin(k*t)*cos(k*phi)/k

(or t,phi replaced by b,psi). This uses angular measure dtheta, NOT Euclidean arc length, so there is no missing target-circle radius factor. The code's mt[1:4]=(sin(t),sin(t)cos(t),sin(t)(4cos(t)^2-1)/3) exactly equals sin(k*t)/k. The analogous mb entries are identical identities, with cos(b)=ell/(2R). Its cheb implements T1,T2,T3 exactly. Hence atom is an interval enclosure of Q=one half of the sum of the two weighted angular coverages.

## Threshold interfaces

For ell>=2R the inner contribution is zero. If an interval crosses ell=2R, clip(ell/(2R),0,1) includes 1; the image formula includes beta=0, sin(beta)=0, and hence the zero inner contribution in addition to all ell<2R values. The returned interval remains sound (no need to sum an extra interval for a disjoint branch). The zero-radicand clamp near the slightly enlarged t endpoint discards only points with no real root, never a valid geometric center. rho in [.62,1.38] and cos(psi) in [-1,1] are independently valid for all geometric inputs. These clamps need this geometric domain, not arbitrary interval arguments.

## Nonnegative coverage inference

The exact rational coefficient check a0>=sum |ak| ensures W(theta)>=0 pointwise for each circle. Complete weighted angular mass/2 is pi*a0; the two-circle mass is B=pi(a00+a10)>0. If m disks cover both circles, then their summed indicator functions are >=1 on each circle, whence sum Q_i>=B. Overlap is permitted and only increases the sum; intersection points between the two target circles need no subtraction, since these are TWO tagged angular measures. Finite sums make measurability immediate. At target tangencies the zero angular measure also agrees with the formula.

The source certificate proves Q_i<B/10 throughout both roots and the entire (t,v,e) domain. Nine disks covering the two circles therefore imply simultaneously sum Q_i>=B and sum Q_i<9B/10, contradiction. This remains valid whether S(h,R) coverage was obtained by an exterior limiting argument, directly assumed, or proved through a Voronoi facet argument. No source hypothesis saying 'exactly ten actual disks' is used in this per-disk inference.

## New consequence: C802

Assume a 9-boundary-disk + 2-strictly-interior-hub covering at r<=R. Hub full Voronoi cells are compact in int(D), contain a neighborhood of their sites, and lie in their radius-r disks. Ring sites have norm>=1-r>=1-R. The open core B(0,1-2R) is ring-free even after enlargement, so belongs to the union of the two unchanged Voronoi cells. If those cells meet in at most a point, connectedness of a punctured open disk puts the whole core in one cell. Taking closure gives |h|<=3R-1=7/50.

That cell is a bounded full-dimensional polygon with no facet opposite the other hub. At every boundary exit q=h+t*u of a ray (t>0), including a vertex, at least one genuine ring facet is active. Here t<=r<=R and |c-h|^2=2t*u dot(c-h), so |h+R*u-c|^2-R^2=|c-h|^2(1-R/t)<=0. Thus the nine enlarged ring disks cover S(h,R); they still cover S(0,1). The dual inequality above contradicts this. Therefore the hub cells share a positive-length edge. Strictly-interior status refers to the ORIGINAL radius-r cover, not necessarily enlarged radius R; containment of the unchanged cells was proved before enlargement, so there is no hidden enlarged-hub interior assumption.

Review result: C802's analytic implication is sound, conditional on the existing C450 arithmetic certificate (audited separately) and established 9+2 input. It does not itself establish a sharp n11 lower bound. No general position, zero overlap, O1, or ring-triple exclusion is used.
