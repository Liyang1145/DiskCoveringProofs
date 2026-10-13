# Local cyclic boundary closure — draft, branch obligation explicit

For boundaryowner v, consecutiveanchors A_prev,A_next have radii U*y_prev,U*y_next fromv and angle alpha_v. Put
 theta_v=2asin(U*sqrt(y_prev²+y_next²−2 y_prev y_next cosalpha_v)/2).
 If alpha∈(0,pi) andtriangle nondegenerate, endpointangleatA_prev is
 delta_(v,prev)=atan2(y_next sin alpha,y_prev−y_next cos alpha),
 andatA_next analogous. Bothin(0,pi), theirsum=pi−alpha.

Atboundaryedgee=uv, virtualoppositeangle gamma_A=h(y_e,x_f,beta_e). On the ordinary nonoverlapping star branch (A outside siteedgeuv), theangle between Au,Av is2gamma_A. Theanchorpolygon interiorangleisdelta_(u,e)+2gamma_A+delta_(v,e). Foranchors onunitcircle inCCWorder, this mustequal pi−(theta_u+theta_v)/2. Thus
 2gamma_A+delta_(u,e)+delta_(v,e)+(theta_u+theta_v)/2=pi.
This supplies localboundarycyclicity, beyondthetotalperimeteridentity. Forqanchors the qequationshaveatleastonesumdependency.

`boundary_cyclicity_control.py/json` verifiesall10equationsatcandidate residual<2e−15; relaxednear-covers failat1e−5to3e−5 despitearea deficitonly1e−9. Reconstruction independentlyfindsanchor-circle radialspread1e−5to3e−5. Thus theseequationsdetectabearinggap missedbyarearesidual.

BRANCH GAP: generalnecessaryinterface mayallowh_A>0 (gamma_A>pi/2), invertedboundary-site triangle, zeroalpha, fanedges. Then orientedangle unwrapping can add2pi; cannotassertthisprincipal equationgloballywithoutprovingthecorrectstarwinding/owner-normalizationbranch. Radius-deficit lemma explicitlyallows h_A ofeither sign; doNOTreintroducepositivityassumption. Safe generalexpression is congruencemod2pi, orcomplexproductconstraint; branchcertificationneededforstrongunwrappedrelation.

Potentialroute: expressunit tangentatA fromeachincidentowner wedge, then equalityofthesetangents ascomplexrotationproduct, avoidingatanunwrapping. Exactcomplexclosure mayreplace q−1 area-cyclicitymissingconstraintsandcanbepolynomializedusingchord/dot data. Needanalyticglobalnecessitynotjustcandidatecalibration.
