# Fixed finite test sets cannot certify this sharp radius

Let X be a finite nonempty set of centers, d_X(p)=min_c|p-c|, and R=max_{p in D}d_X(p)<1 for unit closed disk D. Suppose d_X(0)<R. Then for every finite Q subset D, its unconstrained |X|-center covering radius is strictly smaller than R.

## Deepest set is finite (no acute/genericity assumption)
Take closed Voronoi cells V_c (duplicate sites may first be removed). On V_c, d_X²(p)=|p-c|², a strictly convex quadratic. A deepest point in intD cannot lie in the relative interior of a positive-dimensional Voronoi face: along a small line segment in that face, strict convexity contradicts its being a maximum. Hence interior deepest points are among the finitely many zero-dimensional faces. At a boundary deepest point nearest to c, simultaneously |p|=1 and |p-c|=R. These two circles have at most two intersections unless c=0,R=1. The exceptional case is ruled out by R<1. Thus E={p in D:d_X(p)=R} is finite, with no nondegeneracy or acute-triangle hypothesis.

## Rotation argument
For q≠0 and e≠0 the equation Rot_theta(q)=e forbids at most one theta modulo2pi (none if norms differ). Since E finite and 0 notin E, there are only finitely many forbidden theta from Q×E. Choose another theta. Then all rotated q have d_X<R; finiteness of Q gives max_q d_X(Rot_theta q)<R. This equals the covering radius of Q by Rot_(-theta)X. Empty Q is trivial. The chosen theta can be arbitrarily small while avoiding the finite forbidden set.

## Application
C892 yields R*=.37998...<1; one exact C891 hub has norm<.15<R*, so d_X(0)<R*. Therefore EVERY fixed finite Q subset D has r_11(Q)<R*. Not only the18 critical points, and not only sets with<=11 points. Larger and denser finite Q may approach R* but can never equal it. This is a method limit for an exact sharp proof by a single finite set with unrestricted disk-center assignments, not a disproof of global optimality. A configuration-dependent witness family or infinite family can escape this obstruction. If one artificially fixes an orientation of the centers for the finite problem, its lower bound is not automatically a lower bound for the unrestricted original problem.

Independent application/control: r20-stress/GLOBAL-FIXED-WITNESS-NONSHARPNESS.md and global_rotation_nonsharpness.py. Those numerical/interval improvements are unnecessary for this analytic theorem.
