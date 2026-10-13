# Next structural interface: Delaunay face angles and shared lengths

Draft obligation, no new claims or exclusions. Current area-angle graph relaxation only keeps per-site sums. It discards the common Euclidean triangle represented by three incident circumcenters. Need restore metric consistency, not just refine the same angle bounds indefinitely.

For an interior Delaunay edgeuv with opposite verticesw1,w2 and circumcentersO1,O2, let γ1=angle(uw1v),γ2=angle(uw2v) in(0,π). Empty-circle Delaunay givesγ1+γ2≤π. Conjectured exact Voronoi siteangle identity β_uv=π−γ1−γ2, via signed right-angle deviations of O_j−u from v−u. This needs careful branch proof if either triangleobtuse and when thecircumcenterliesoutsideitsdualtriangle. Addedfanedges haveβ=0 andγ1+γ2=π in cyclicfaces, consistent.

Every dualtriangle has its threepositiveinteriorangles summingπ. Every facecircumradiusR_f≤r; every sharededge satisfies

 |u−v|=2R_f sinγ_{f,uv}=2R_g sinγ_{g,uv}.

The ratios are a potentially strong global compatibility constraint. Cyclicproducts aroundcycles of dualfaces equal1, eliminating R variables locally. This is not automatically enforced by vertex-angle equations. Need a bounded structural test on strongest savedrelaxationcandidate, plus actualcover calibration, before a largeimplementation.

Boundary edges require a unitcircleanchor ratherthana secondtrianglecircumcenter; analogous signedangle contribution has extraanchorradius/center-locationgeometry. A jointcertificate might connect those with innernormenvelope and avoid independent alpha/beta maxima.

## Interior-edge identity proof (nondegenerate)
Putu=(0,0),v=(l,0), w1 aboveaxis,w2below. Circumcenters areO1=(l/2,(l/2)cotγ1), O2=(l/2,−(l/2)cotγ2). Theirargumentsatuareφ1=π/2−γ1 andφ2=γ2−π/2, bothin(−π/2,π/2), validalsoobtuse. Delaunayγ1+γ2<=π givesφ1>=φ2, henceβ=φ1−φ2=π−γ1−γ2∈[0,π]. Reflectioninvbisectorgivessameβatv. Identitypassescompactanglelimits. No acutenesspremise needed. Actualcover19interioredgesnumericcontrolpassed (`face-angle-control.json`).

Linearfaceangleextension on12savedrelaxedproposals ALLfeasible, so thatinstrumentalone isnotyetstructuralgain. Sharedlength constraints remainbearingmissingpiece.
