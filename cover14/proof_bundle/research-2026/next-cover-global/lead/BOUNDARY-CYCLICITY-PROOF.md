# Global necessary boundarycyclicity in the normalized clipped representation

## Scope and assumptions
Unitdisk after scaling; cover radius rho<1/3; all sites strictly inside norm bound sqrt(1−rho²), as supplied by outwardclipping C1171. Positive ownerarcs form cyclic partition, each length theta_v<=2asin rho<pi. Boundaryanchor A belongs to exactly two cells W_u,W_v, joined to genuine inward Voronoi facet AO with O inside disk. Angle variables radians. Degeneracies obtained by constantgraph compact limits, not arbitrary atan2(0,0).

## 1. Owner lies on inner side of its anchor chord
For an owner w with arc length theta and middle unitvector n, both anchor endpoints satisfy n·A=cos(theta/2). Normbound gives n·w<=|w|<sqrt(1−rho²)<=cos(theta/2). Therefore w lies strictly on origin-side of the chord. This statement applies to OWNEDarc endpoints, not only the disk's full boundary intersection. If either endpoint equals the other, use limitingangles.

## 2. Exact order of rays at a switchanchor
Let A_- be previousanchor, A_+ nextanchor; W_u owns arc A_-A, W_v owns AA_+. Let b be the inward bisector ray AO. The four rays Au, Av, AA_-, AA_+ lie in the open inward tangent halfplane at A, an angular interval of length pi. In that interval the bisector line has exactly one ray b. The nearest-halfplanes place AA_- and Au on its u-side, and AA_+ and Av on its v-side. Thus b lies between the two chordrays. The unitcircle minus the minorarc A_-A lies on the origin-side of chord A_-A; in particular A_+ lies there. By §1, u also lies on that side. Within the inward angular semicircle, this implies Au is on the b-side of AA_-. Combining this with Au being on the AA_--side of b places Au between AA_- and b. The identical argument places Av between b and AA_+. The ray order is therefore AA_-, Au, b, Av, AA_+, or its reverse. No premise concerning whether O is in an owner wedge triangle is used.

More explicitly the fact b lies between the chordrays follows simply from nearest-halfplane: A_- and A_+ lie on opposite sides of bisector, both rays in the same open angular semicircle, so its inward ray lies between them. No claim O lies in the owner wedge triangle is needed. Site-ray order then follows from same-side-of-b plus inner-side-of-owner-chord.

## 3. Middle angle and closure
C1250 proves A is on exterior side of siteedge uv and gamma_A∈(0,pi/2), with no assumption about the sign of realcircumcenter height. Isosceles triangle Auv has angle 2gamma_A at A, bisected by b. From §2 the minor polygoninteriorangle between AA_- and AA_+ equals
 delta_(u,A)+2gamma_A+delta_(v,A).
For consecutive unitcircle anchors, that interiorangle is pi−(theta_u+theta_v)/2. Therefore
 **2gamma_A+delta_(u,A)+delta_(v,A)+(theta_u+theta_v)/2=pi.**
No modulo2pi ambiguity remains in this representation.

## 4. Relation to radiusvariables and limits
At a nondegenerate ownertriangle with angle alpha_v∈(0,pi), anchor distances a_prev,a_next>0:
 L_v²=a_prev²+a_next²−2a_prev a_next cos alpha_v;
 theta_v=2asin(L_v/2);
 delta_(v,prev)=atan2(a_next sin alpha_v,a_prev−a_next cos alpha_v), analogousnext.
At a nondegenerate boundaryfacet beta_e∈(0,pi), realradius R_f andanchorradius a_e:
 gamma_A=atan2(R_f sin beta_e,a_e−R_f cos beta_e).
In a degeneratelimit, retain compact angles delta,gamma,theta along the same subsequence. The LINEARcyclicity identities persist. Trigonometriclength/angle equalities persist, but defining a limitingangle as principal atan2(0,0) is invalid. This is a global NECESSARY representation theorem for arbitrary covers after C1171 normalization/clipping, not a claim every formal angle/radius solution is realizable.

## Independent converse interface
CYCLIC-POLYGON-CLOSURE.md proves a closed ordinary flatpolygon whose sidelengths are 2sin(theta_i/2) and whose signed exterior turns are (theta_i+theta_(i+1))/2, withsumtheta=2pi, is unitcyclic. This separate complexchord inference verifies the intended geometric meaning; it does not replace global emptycircle/embedding obligations.
