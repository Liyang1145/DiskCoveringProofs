# Boundary-first chart adjoining a flat sector (analytic derivation)

Actual allowance r∈[3/8,U]; set s=sqrt(1-r²), phi=asin r. Flat sector2 has P1=(s,-r),c2=(s,0),P2=(s,r). The left neighbor has c1=(s-2r sinb cosb,-2r sin²b), with b=b1.

For the unit-circle arc owned by c1 immediately BEFORE P1 in counterclockwise order to have positive width, P1 must be the counterclockwise end of its radius-r covered arc, since |P1-c1|=r. The disk intersection with the unit circle is a connected proper arc (norm c1>0, r<1). Thus cross(c1,P1)>0. Directly
 cross(c1,P1)=r[-s cos(2b)+r sin(2b)]=-r cos(2b+phi).
Since0<b<pi/2 and0<phi<pi/2, positivity gives
 **b>(pi/2-phi)/2=acos(r)/2**.
Inwardness ofc1 gives |c1|²−s²=4r sinb(r sinb−s cosb)<=0, hence
 **b<=acos r**.
Let D=c1 dot P1=s²−2sr sinb cosb+2r²sin²b>0 (indeed D=(1+|c1|²-r²)/2>0). Let X=cross(c1,P1)>0. Then the full coveredarc width is
 **W(r,b)=2 atan2(X,D)**.
Therefore for the actual positive nearest sector1, the predecessorP0 is exactly a clockwise rotation ofP1 by some w1 with
 **g<=w1<=W(r,b)**,
where g=2pi−16asin(R0) is the uniform necessary nearest-sector floor. The covered arc is the entire clockwise interval, so this is an EXACT description of local boundary coverage and inwardness given this neighbor placement; other sites' nearest inequalities omitted.

The rightneighbor is the reflection, withb2 andw3 analogous. This replaces the constrained (alpha1,u1) variables by (b1,w1) with explicit interval fiber, and similarly on the right. Endpointdistanceu1=|P0−c1|/R0 and sectoranglealpha1=angle(P0−c1,P1−c1) recover the original sector atoms. Their orientation within the target switch polygon forcesalpha1∈(0,pi]; verify that as a chart interface rather than assuming opposite branch. At endpointsW, two endpointdistances equalr, not an assumption throughout.

Combined with C848, sevenfactorpatch has coordinates (r,b1,b2,w1,w3,A,H). Widths have explicit intervals [g,W], H has C848 interval. A∈(0,b1+b2) andr∈[3/8,U]; all originalrepresentations remain available forcalibration. No symmetry or saturation of sitefacecircumradii asserted.
