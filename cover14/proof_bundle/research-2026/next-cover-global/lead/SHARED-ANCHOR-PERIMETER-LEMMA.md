# Shared-anchor perimeter bound from the normalized norm disk

Fix U<1/3 and s=sqrt(1−U²). For any U-cover, first normalize at U (graph may change existentially). Let q positive owners and switchanchors A_i have common nearest distances a_i∈[1−s,U]. Define
 f(a)=acos((1+s²−a²)/(2s)),  a∈[1−s,U].
Then **sum_i f(a_i)>=pi**. In particular
 sum_i a_i >= q sqrt(1+s²−2s cos(pi/q)).

Proof. For a site c of norm t<=s and a unitanchor A with |A−c|=a<=U, let phi be the minor angular distance from direction c to A. A boundaryowner has t>=1−U>0. Cosine rule gives cosphi=(1+t²−a²)/(2t). Differentiation with respect to t gives [t²−(1−a²)]/(2t²)<=0, since t²<=s²<=1−a². Thus phi<=f(a). For an owner between consecutiveanchors A_(i−1),A_i, the circle's angular metric triangle inequality gives theta_i<=f(a_(i−1))+f(a_i), since theta_i<pi is their minor separation. Sumtheta_i=2pi yields the assertion.

Concavity: f'(a)=a/(s sin f)>0. For interiora,
 f''(a)=[s² sin²f−a² s cosf]/(s³ sin³f)
 =[(s−cosf)(1−s cosf)]/(s² sin³f)<=0,
because cosf>=s and1−s cosf>0. Therefore Jensen gives pi<=sum f(a_i)<=q f(mean a), yielding displayed lowerbound. Endpointa=1−s obtained by continuity; no differentiability there needed. At U, f(U)=asinU andf'(U)=1/s.

A simpler linear deficit bound follows the concave tangent atU:
 f(a)<=asinU−(U−a)/s,
 hence **sum_i(U−a_i)<=s(q asinU−pi)**.
The Jensen bound is stronger except infinitesimaldeficits. Both are global necessary constraints on shared anchor radii, not owner endpointdistances chosen independently. They require no cyclicityformula, giving an independent route to coupling neighbor wedges.

Equality in the Jensen inequality requires all a_i equal (strictconcavity awayfromU); equality in perimeter additionally forces every boundarysite norm s and its radialdirection between the incidentanchor directions. This is not assumed atcandidate, whose boundarysite norms vary.

Scope: normalized cover atU, q positiveowners; directunitdiskgeometry, no Voronoi triangularface assumptions. In outwardclippedrepresentation apply at inflatedrho thenlimit toU. Doesnot exclude anygraph onitsown. Next bounded test shouldmeasure this constraint on the saved sharedradius fake-nearcovers to decide whether it adds leverage independentlyofcyclicity.
