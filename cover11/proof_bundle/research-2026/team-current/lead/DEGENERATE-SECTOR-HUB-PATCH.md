# Seven-factor patch adjoining a flat middle sector

Scope: the actual inward q0 graph, sector2 alpha2=pi, allowance r in[3/8,U]. The corner lemma gives c2=(s,0), P1=(s,-r), P2=(s,r), s=sqrt(1-r²). Distances from P1 to c1,c2 and P2 to c2,c3 are exactly r. Local nearest ordering fixes
 c1-c2=2r sin(b1)(-cos(b1),-sin(b1)),
 c3-c2=2r sin(b2)(-cos(b2),+sin(b2)).
The two site faces [9,1,2],[9,2,3] fill the angle at c2: A+B=b1+b2, with A,B>0. Parameterize hub distance H=|c9-c2|>0 and delta=b1-A; then
 c9=(s-H cos delta,-H sin delta), B=b1+b2-A.
No hub symmetry is assumed.

## Circumradius constraints eliminate the H feasibility surfaces
Let D1=2r sin b1,D2=2r sin b2. Face1 has angle A at c2 and adjacent lengths H,D1. Its circumradius squared is
 rho1²=(H²+D1²-2HD1 cosA)/(4sin²A).
Thus rho1<=r iff
 2r sin(b1-A)<=H<=2r sin(b1+A),
 obtained from the quadratic roots D1 cosA +/- sinA sqrt(4r²-D1²). This uses 0<b1<pi/2 and 0<A<pi.
Similarly face2 uses B,b2. Since b2-B=A-b1=-delta, their combined lower bound is
 **H>=2r |sin delta|**,
and their upper bound is
 **H<=2r min(sin(b1+A),sin(b2+B))**.
An empty interval means the proposed patch is impossible; no positivity of the upper sine terms is assumed without checking.

The hub is strictly interior: |c9|<=1-r is necessary. Therefore also
 H²-2s cos(delta) H+2r(1-r)<=0.
If D=s² cos²delta-2r(1-r)<0, the patch is empty. Otherwise intersect the H interval with
 [s cosdelta-sqrt(D),s cosdelta+sqrt(D)].
This imposes one physical hub shared by the two faces, rather than independent circumradii or averaged edge matching.

## Evaluation
Given H,A,B, each face's remaining angles follow the triangle law. For face1 its hub angle is atan2(D1 sinA,H-D1 cosA); its ring1 angle is pi-A-hubangle. Face2 analogously. The circumradii above determine their normalized radius arguments. Sum the ORIGINAL atoms for faces1/2, switches1/2, sectors1/2/3. Pointwise matching and the angle sum at ring2 cancel automatically in this sum. Keep the original global constant unchanged.

The neighboring sector variables remain those in ADJACENT-SECTOR-CLUSTER.md, namely (t=r/R0,alpha1,u1,alpha3,v3). They determine b1,b2 by local circle closure. Add A and H: seven scalar variables. The interval formulas above may replace H by an affine parameter in[0,1] after all bounds are computed. This is a necessary local patch domain; realization of the remaining graph and nearest inequalities beyond the patch are still omitted, so a rigorous maximum over this domain would be a SAFE upper bound only after domain coverage is verified.

## Actual allowance interface
Because alpha2=pi forces its endpointdistance to equal actual r, t is not merely an independent normalized switch radius here. Neighbor distances must satisfy u1,v3<=t and their inward predicates use t², not just max(tau²,u²,v²). The initial patch diagnostic omitted this strengthening (a safe enlargement, not an invalid exclusion). `probe_seven_factor_actualr.py` retains it. It changes the best numerical aggregate negligibly:3.1442897309148634, still abovepi. No conditional exclusion results.

## Controls
`check_hub_patch.py`: exact symbolic factorization of the face quadratic;6641 offcandidate coordinate patches check both angles, independently solved circumcenters and hubnorm. These are calibration, not domain certification. `seven_patch_cancellation_control.json` verifies at the diagnostic point mu2 coefficient=-pi, four sharedendpointcoefficients=0, closurecoefficients113/114=pi. The exact cancellations follow metricidentity andangleclosure, not this numeric control.
