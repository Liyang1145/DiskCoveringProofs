# Alternative global area decomposition with real triangle angles

Originalpairedfacetarea is convenientforsite-beta ledger but localfaceenvelopes discard realtriangleangle sums at eachsite. A secondexactdecomposition mayretainthose directly.

For a genuine realDelaunay triangle withcircumradiusR<=U and anglesgamma1+gamma2+gamma3=pi, itsarea=2R² sin gamma1 sin gamma2 sin gamma3. Thisispositiveevenifcircumcenteroutside. BoundingRbyU yieldsclassictrianglearea envelope.

Boundaryedgeuv hasanchorA onexteriorside(C1250), |Au|=|Av|=a<=U andangleuAv=2gammaA∈(0,pi). Its trianglearea=.5 a² sin(2gammaA); anglesat u,v bothpi/2−gammaA. Boundaryownerwedge triangle(c,Aprev,Anext) hasarea=.5 a_prev a_next sin alpha, endpointanglesdelta withdelta_prev+delta_next=pi−alpha. Boundaryarc capadds(theta−sintheta)/2.

For a straight triangulatedsite polygon plusoutwardboundaryedge triangles andownerwedges, these piecesmightgive exactdiskpartition; needcheck sitespolygonboundary canbenonconvex andfantrianglesoverlap. ActualVoronoicell-star triangles providea topologicalstraight embeddingwhenlocalDelaunay andboundaryhAnegative; globalrealizationmustbeaudited. DoNOTassumeallnormalizedboundaryownersareconvexhullvertices (q11pockets explicitlyallow nonconvex sitepolygon).

Ifvalid, siteangleclosure is
 hidden: sum(realtrianglegamma_at_v)=2pi;
 boundary: sum(realtrianglegamma_at_v)+sum_adjacentedges(pi/2−gammaA_e)+alpha_v=2pi,
 hence sum(realtrianglegamma_at_v)+alpha_v−gammaA_prev−gammaA_next=pi.
These constraints supplementfaceangles andboundarycyclicity. Candidatecontrolsnecessarybeforecertificatework.

Areaalgebra canbeverifiedwithoutpartition: subtractpairedfacetdecomposition andcancelcircumcenterspokes. For eachrealface R²/2 sumsin2gamma =area; onboundary virtualhalfspokes havea²/2 sin2gammaA. Therefore sumrealtrianglearea+sumboundarytrianglearea =sumpairedfacetarea. This cancellation uses sharededgelength2R sin gamma=2T sin gammaother andgamma+gammaother=pi−beta; identityatoneedge:
 .5[R² sin2gamma+T² sin2gammaother]=RT sinbeta.
Thus no convexsitepolygonassumptionneededforAREAidentity. Positiveboundarytrianglearea followsC1250; per-siteangleledger stillrequiresstraightDelaunaystarorientation butstandardplanar triangulation.

Potentialhigher-leveragedual: optimize mixed realtriangle angles (sum pi) + gammaA withlinearvertexangles, andjointboundarywedge/perimetercaps. Circumradiusratio sharededges maybedroppedfirst; exactareaanglesalreadycoupledwith hiddenvertexangles. Boundedcandidate+6graphprobe beforeanyscale.
