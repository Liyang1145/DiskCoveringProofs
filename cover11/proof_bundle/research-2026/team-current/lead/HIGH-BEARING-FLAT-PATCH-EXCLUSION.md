# High-bearing flat q0 patch exclusion: boundary, endpoints, stationary values

Scope: frozen C849 necessary relaxation for an actual flat q0 sector2 (alpha2=pi), actual physical r in [.379,.37999], bearings bj in [1,acos r], all legal independent width fibers. This is a restricted class, NOT a global n11 sharp optimum or full q0 exclusion.

## Endpoint lemma (analytic)
Fix r,b1,b2 and widths. C861 proves the smooth hub objective attains its maximum on at least one of the three circle boundaries, and the closed feasible set misses v=0 and both wedge rays. The norm-circle boundary is bounded by C863.

On face1 circle, the positive-H branch can be written H=2r sin(2b1-delta), delta in(-b2,b1). On face2 circle, H=2r sin(2b2+delta), same delta interval. These follow exactly from |x-Di|²-r²=H(H-cap_i), H>0. Thus they cover every legal point of each face circle, without a missing branch. Since v>0 and |delta|<acos r<pi/2, polar angle is a smooth parameter. Differentiating the Cartesian face-circle chart gives |dx/ddelta|=2r>0, so it is regular even at extrema of H.

At a feasible face-circle point not on another disk boundary, all remaining inequalities are strict; a small open face-circle arc remains feasible. A maximum there has G'=0 (and G''<=0). Otherwise the point is on the norm circle or both face circles. The two distinct face circles pass through the origin (H=0, excluded by norm disk). Their other intersection has delta=b1-b2,H=2r sin(b1+b2), since equality of caps factors as 4r cos(b1+b2)sin(b2-b1+delta)=0. Here cos(b1+b2)<0 and |b2-b1+delta|<pi, so this is the only positive-H intersection. It is precisely the ridge bounded in C869. Degenerate singleton feasible arcs must be on another boundary, so are covered as well.

It therefore suffices to bound values at stationary points on each legal face arc; it is NOT necessary (and C868 proves false) to exclude all stationary local maxima.

## Stationary-value certificate
certify_stationary_face_bound.py covers both face charts with r outward enclosing [.379,.37999], bj in [1,1.1863995522992576] and delta in [-1.1863995522992576,1.1863995522992576]. This contains all legal bj<=acos r and -b2<delta<b1. Necessary-only filters test bearing, wedge, H>0, other cap, and norm disk. Opposite cap sign may equivalently use delta<=b1-b2 on face1 and >= on face2 within this chart.

1. face_derivative_outer_jet.py differentiates the Cartesian hub expression explicitly with respect to delta, then applies 4-variable full-extension interval AD to this derivative. An outer mean-value enclosure proves G' nonzero on many boxes. Active-face terms are simplified exactly: e=r sin(A)/R0 and phi=A (face1), or e=r sin(B)/R0 and phi=B (face2), with delta derivatives respectively -,+. The other face uses the generic atan2 derivative and length derivative. No physical clipping enters this derivative enclosure.
2. face_second_jet.py independently implements scalar second-order AD and the saturated polar expression. Natural and centered derivative bounds are intersected. At any stationary point d* in a box with midpoint m in the delta interval, ordinary scalar Taylor about d* gives G(m)=G(d*)+G''(xi)(m-d*)²/2. Thus G(d*) belongs to G(m)-G''(box)*(m-d*)²/2. All other outer variables are held fixed in this argument, and interval evaluation covers every such fixed choice. The analytic extension is smooth on the whole box whenever evaluation succeeds, regardless of whether intermediate delta values are physically feasible.
3. Add the existing width-fiber upper bounds and K(r), retaining all terminal uppers. Rejecting a width-infeasible entire outer box is necessary-only. No root finding or sampling is used for completeness. A positive G'' box, if any, would also exclude stationary local maxima; the finished run did not need that branch.

Source hashes and frozen coefficient hash are stored in stationary_face_bound_certificate.json. Independent controls check_face_derivative_outer.py compare Cartesian second AD with the explicit first derivative and its delta derivative at30 points, plus outer finite differences (calibration only, not the continuum proof).

## Assembly and remaining implication
See highbearing_boundary_assembly.json: max of norm, ridge and stationary upper bounds plus the matching22 factors and dual constant is strictly below pi. Combined with the endpoint lemma and C861, this excludes the entire stated high-bearing flat-patch class, not just a local bearing box.

Still open: patches with min(b1,b2)<1; the implications from any restricted flat-patch exclusion to complete q0 class coverage; and the original sharp global n11 optimality theorem. Neither this note nor a zero-live queue supplies those reductions.

Repro: py -3 -B research-2026/team-current/lead/certify_stationary_face_bound.py; py -3 -B research-2026/team-current/lead/assemble_highbearing_boundary.py.
