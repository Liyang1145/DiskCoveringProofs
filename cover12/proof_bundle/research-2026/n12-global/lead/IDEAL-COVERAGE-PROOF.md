# Ideal algebraic configuration covers the closed unit disk

Object: unique F,G,H,T root(a,t,r,w) in evidence/root-t-certificate.json's exact rational box. Put b=(1+a+r)/2, v=w/√3, d=a+r. Centers are hubs a u(120j°), lows t u(60°+120j°), highs (b,±v) rotated120j°, j=0,1,2. This is exactly D3-symmetric by construction; no original rounded literal is used.

## Boundary coverage (analytic, no sampling)
Let β=atan(v/b), α=π/3−2β. Certified b>w>0 ensures0<β<π/6 and0<α<π/3. H=0 gives (1−b)²+v²=r². The high disk at(b,v), whose ray isβ, therefore contains both unit-circle points at angles0 and2β. Every intermediate angle has smaller/equal squared distance because cos(θ−β)≥cosβ. G=0 gives
cosα=(1+t²−r²)/(2t),
using cos(π/3−2β)=(3b²−w²+6bw)/(2(3b²+w²)). Therefore low disk on60° ray covers the entire arc[2β,120°−2β]. The reflected high disk covers[120°−2β,120°]. Rotate these three intervals by120° and240°: they tile S1 with shared endpoints. All endpoint distances are exactlyr; no interval containing0 is being used to infer an identity.

## Triangles of the center polygon
Ring ordering: +β,60°,120°−β,120°+β,180°,240°−β,240°+β,300°,360°−β. Label0..8 in this order; hubs9..11 at0°,120°,240°. Start with triangle-block333 graph and relabel ring i→i−2 mod9, hubs unchanged. The13 faces are listed in evidence/ideal-coverage-certificate.json.

lead/ideal_coverage_certificate.py uses scaled coordinates(x,Y), physical y=Y/√3. Rotation120° is exactly(x,Y)↦((-x−Y)/2,(3x−Y)/2). It evaluates the root box via exact outward Fraction intervals and certifies:
1. Every ring polygon edge has every other ring and hub strictly to its left. Thus P=conv(all centers) is the strictly convex ring polygon; all centers are insideD.
2. Every oriented face determinant is positive. The oriented sum of all face boundaries equals the oriented9-edge polygon boundary exactly (integer incidence check). Hence the13 positively oriented triangles coverP. One elementary justification is winding number: away from their finite edges, the sum of triangle indicator functions equals the polygon indicator function, because their oriented boundary chains agree. Since each triangle is inP and positively oriented, there are no uncovered open components or overlapping interiors; closure covers the edges as well.
3. Seven nonactive faces have circumradius strictly<r, with exact rational positive squared-radius margins.
4. The remaining six faces have an exact common radius-r witness: HRR faces(8,0,9),(2,3,10),(5,6,11) use d u(120j°); HHR faces(9,10,1),(10,11,4),(11,9,7) use(t−r)u(60°+120j°). H proves the HRR identities (d=2b−1); F proves the HHR identities: a²+(t−r)²−a(t−r)−r²=F. Their third distances are exactlyr by definition.

**Common-witness triangle lemma.** If vertices c_i lie withinr of z, then their triangle is covered by the radius-r disks centered at those vertices. For x=Σλ_i c_i, λ_i≥0,Σλ_i=1,
Σλ_i|x−c_i|²=Σλ_i|z−c_i|²−|x−z|²≤r².
At least one distance is≤r. Thus all13 triangles, and henceP, are covered. This does not require each triangle to be acute or its witness to lie inside it.

## Outside the center hull
For x∈D\P, let y be its Euclidean projection onto convexP and v=x−y≠0. For each center c∈P, v·(y−c)≥0. Along x+s v, s≥0, all squared distances to centers increase strictly, since v·(x+s v−c)≥(1+s)|v|²>0. The ray meets S1 at some u. Boundary coverage gives a center c with |u−c|≤r, hence |x−c|≤r. Combining withP coverage proves all ofD is covered, including its boundary.

## Scope and reproduction
This establishes an attaining configuration at the algebraic candidate radius r*, so r_D(12)≤r*. It does not by itself prove any lower bound or exclude k10/k11. Numerical decimal r*≈.361102963744508644113087702017 is only a display; root definition is exact.

Reproduce from workspace:
`py -3 -B research-2026/n12-global/lead/root_t_certificate.py`
`py -3 -B research-2026/n12-global/lead/ideal_coverage_certificate.py`
Independent audit completed in members/finite-reduction/coverage-audit/REPORT.md, with exact F/H identities and an independent geometric/kernel implementation. C985 records this upper bound; no numerical scan is part of the proof.
