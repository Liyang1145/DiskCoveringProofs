# Shared face radius: next structural representation

For any dualtriangle f (boundaryvirtualanglesallowed), let R be its circumradius andγ_e its realoppositeangles (Σγ=π). Atedgee withangleβ_e, otherendpointradiusT_e obeys
 R sinγ_e=T_e sin(γ_e+β_e), 0<γ_e<π−β_e,
 so T_e/R=k_e=sinγ_e/sin(γ_e+β_e)>0.
Normalizedx=R/U, y_e=T_e/U=x k_e. All<=1. Groupedexactpairedfacetarea = U² x² Σ_e k_e sinβ_e.
Forfixedγ,β, maximizeoverx<=1,min_e(1/k_e) gives
 A_face(β)<=U² max_{γ>0,Σγ=π,γ_e+β_e<π} [min(1,min_e 1/k_e)]² Σ_e k_e sinβ_e.
Thisisnecessaryupperboundgroup, NOTglobalpartitionbyallfaces; stilluseedge-disjointpacks. Beta-domain feasibility requiresΣβ<2π; ifΣβ>=2π nondegenerateγsimplexempty (closedlimitallowed). Thislinearface-angleboundalready followsΣγ+Σγ_other=3π−Σβ andΣγ=π.

Atcandidateslackfaces, R≈.32082 andallT_e=U, henceallk_e=U/R equal; theirrealγvalues satisfyΣγ=π. Ifthislocalfaceoptimization maxoccursatthatintersection, itwouldrecoverALLactualedgedeficitforthese2faces, unlikeweaklinearfacepenalty. Need proveoptimalityorcomputecontrolledcounterexample; don'tassumeallneighborssaturate.

Equivalent parametrization forfixedβ,x,y: γ_e=atan2(y_e sinβ_e,x−y_e cosβ_e) withcorrectbranchin(0,π−β_e). Angleincreaseswithy_e atfixedx. Thismaygivewaterfilling/concavityroute, butallcurvatureclaimsrequirederivation. Domainendpointsβ=0 orγ=0arecompactlimits; ratioformulaalonecannotbeusedthere.
