# Independent coordinate derivation of the ray ordering

This verifies C1252 by explicit dot products instead of a planar diagram. It does not use the rejected member report.

Rotate A=(1,0). Previousanchor A_-=(cos theta_u,−sin theta_u), nextanchor A_+=(cos theta_v,sin theta_v). Eachtheta∈(0,2asinrho), so theirsum<2pi. Use inwardpolarvector w(psi)=(-cospsi,sinpsi), psi∈(-pi/2,pi/2). Every vectorfromA toaninteriorsitehasthisuniqueangle. Chorddirections are
 psi_- = -pi/2+theta_u/2,
 psi_+ = pi/2-theta_v/2,
 hence psi_-<psi_+ and theirdifference pi−(theta_u+theta_v)/2, NOT universallypi orpi/2.

Commonanchor distancea>0 gives u=A+a w(psi_u), v=A+a w(psi_v). Let m=(psi_u+psi_v)/2, d=(psi_v−psi_u)/2∈(-pi/2,pi/2). Distinctsites implyd!=0. Foranychordray X−A=L w(psi), L>0,
 (X−A)·(v−u)=2aL sin(psi−m) sin d.
The halfplane |X−u|<=|X−v| is exactly (X−A)·(v−u)<=0 because |A−u|=|A−v|. Ownership atpreviousanchor gives sin(psi_-−m)sin d<=0; atnextanchor gives sin(psi_+−m)sin d>=0. Eachpsi−m∈(-pi,pi), so sinehassignofitsargument. Ifd<0, theseimplypsi_->=m>=psi_+, contradiction. Thusd>0, psi_u<psi_v, andpsi_-<=m<=psi_+.

Now useinnerchordside. Previouschordnormal n_-=(cos(theta_u/2),−sin(theta_u/2)) obeys n_-·(u−A)<0 bynormcap. Writeu−A=(-p,y) withp>0. Then -p cos(theta_u/2)−y sin(theta_u/2)<0, i.e. y/p>−cot(theta_u/2), which is exactlypsi_u>psi_- bystrictmonotonicityoftan ontheinwardsemicircle. Similarlynextchordnormal n_+=(cos(theta_v/2),sin(theta_v/2)) givespsi_v<psi_+.

Combining gives
 **psi_- < psi_u < m < psi_v < psi_+.**
Theinwardperpendicularbisectorray hasdirectionw(m): w(psi_u)+w(psi_v)=2cosd w(m), cosd>0. Thereforemiddleangle2gammaA=2d, endpointanglesdelta_u=psi_u−psi_-, delta_v=psi_+−psi_v. Telescopinggives
 delta_u+2gammaA+delta_v=psi_+−psi_-=pi−(theta_u+theta_v)/2.
This establishes the unwrappedidentity directly, noThalesassumption, no globalfacecircumcenterneeded forrayorder. ConnectinggammaAtoR,beta additionallyusesactualinwardfacet/C1250 asintheoriginalproof. Strictnormcap ensuresstrictchordside; closurelimits preserve linearequalitywithretainedanglevariables.
