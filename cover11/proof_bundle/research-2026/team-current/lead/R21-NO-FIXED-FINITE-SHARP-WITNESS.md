# Rotation obstruction to a fixed finite sharp witness

## Proposition (analytic, conditional on a stated cover)
Suppose C={c1,...,cn} covers the unit closed disk D by radius-r disks, r>0. Assume:
(i) every ci is nonzero;
(ii) the origin is strictly covered: min_i|ci|<r.
Then for EVERY finite set P subset D there exists a rotated copy Q_theta C and a radius r_P<r that covers P. Therefore no single finite fixed target-point set P can certify a global n-disk covering lower bound of r.

Proof. Rotation preserves covering D at radius r. For each nonzero p in P and each nonzero ci, equality
 |p-Q_theta ci|²=r²
is equivalent to p dot Q_theta ci=(|p|²+|ci|²-r²)/2. The left side is a nonconstant sinusoid, so equality has at most two angles modulo2pi (or none). The union of these exceptional angles over finitely many p,i is finite. Choose theta outside it. Every p!=0 remains covered by some disk, and no distance equals r, hence at least one covering distance is strictly below r. If p=0, hypothesis(ii) gives strict coverage invariant under theta. The maximum of finitely many nearest-center distances is thus r_P<r. Empty P is trivial. QED.

## Critical scope
This is a method obstruction, NOT disproof of the main n11 optimum or of finite descriptions/certificates generally. It rules out proving r_D(n)>=r solely by an infeasible cover of ONE fixed finite subset of D, when a cover satisfying (i)(ii) exists at r. It does not rule out:
- finite-point certificates for every r<rstar, with points depending on r and cardinality growing;
- moving witnesses depending on the ring parameters or separating line;
- symbolic finite equations with quantified geometric parameters;
- using a fixed finite set for a restricted fixed-ring problem (rotating all rings is then not allowed);
- a candidate neighborhood proof with a rotation gauge plus moving support points.

For n11 the saved near-optimal candidate visibly has no center at origin and strict origin coverage; any exact target cover with those same properties would meet the proposition. A certificate only giving an upper allowance U applies at U, not automatically at the unknown sharp rstar. Do not identify decimal C249 with exact rstar. This lemma diagnoses why the originally contemplated fixed finite target witness cannot close sharpness in a single step; it supports changing to ring-dependent witnesses or stress, rather than ever larger fixed grids.

Relation to previous work: C455 prohibits a universal bounded-size infeasible core for arbitrary finite2disk instances; C457 prohibits checking only fixed convex-hull vertices of a curved hole. This rotation argument has different quantifiers: all n disks free, fixed finite P, exact sharp target r with an actual cover. It does not reproduce those statements.
