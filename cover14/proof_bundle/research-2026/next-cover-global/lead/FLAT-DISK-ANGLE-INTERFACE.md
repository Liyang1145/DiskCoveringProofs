# Completing the angle interface for FLAT-DISK-REALIZATION

Strict data: oriented triangulated disk K, q boundarysites, m hidden; paired beta_e in(0,pi), realface R_f>0, anchor a_e>0, all radii<=U. Eachface-edge gamma_fe=atan2(T sinbeta,R_f−T cosbeta) in(0,pi), withsum_over3edges gamma_fe=pi; T isotherfacerealradius orboundaryanchorradius. Acrossinterioredge gamma_fe+gamma_ge=pi−beta_e by elementarytriangleofcenters sine/cosinelaw. Atboundary define gammaAe analogouslyandrequire0<gammaAe<pi/2. Then gamma_fe+gammaAe=pi−beta_e. Everyedge hascommonlength l_e=2R_f sin gamma_fe=2T sin gamma_ge (virtualA forboundary).

Assign originalface as triangle withoppositeedgeangles gamma_fe andcircumradiusR_f, so l_e indeedits sidelength. The sameedge in virtualtriangle A_euv haslength2a_e sin gammaAe; itsapexangle2gammaAe andbaseangles pi/2−gammaAe. For eachboundaryowner v define alpha_v=2pi−sum_incidentbeta, require0<alpha_v<pi. Itsownertriangle hasanglealpha_v atv andadjacentanchor lengths a_prev,a_next. Thus itsotheranglesdelta sumto pi−alpha_v, withbaseL_v fromcosinelaw. NeedL_v<2, theta_v=2asin(L_v/2), sumtheta=2pi, and C1252 closureateachanchor.

## Interior site angle ledger
Hiddenvertex degree d hasdrealtriangles. Itsrealangles sumto d*pi minusallgamma forincidentsides; pairingthese sides gives
 d*pi−sum_incidentedges(pi−beta)=sum beta=2pi.

Boundarysite hasdegree d in K, d−1 realfaces, d−2 interioredges and2boundaryedges. Sumrealangles
 =(d−1)pi−sum_interiorincident(pi−beta)−gamma_f,b1−gamma_f,b2
 =pi+sum_interiorincident beta−gamma_f,b1−gamma_f,b2.
Add thetwo virtualbaseangles andowneranglealpha:
 2pi+sum_interior beta−(gamma_f,b1+gammaA,b1)−(gamma_f,b2+gammaA,b2)+alpha
 =sum_allincident beta+alpha=2pi.
Thus all14interiorvertices ofaugmented K+ areflat. This identity explains whyaddingrealvertexledgerrows tooldLPwasredundant, but here it supplies anembeddinghypothesis ratherthan anextrainequality.

Explicit abstract-data hypothesis at every hidden site: sum_incident beta=2pi. Explicit abstract-data hypothesis at every anchor A_e: delta_(u,A)+2gammaAe+delta_(v,A)=pi−(theta_u+theta_v)/2. The latter is the equation proved NECESSARY in C1252; it is imposed, not inferred, in this sufficiency theorem. Traverse the boundary with interior on the left so its signed turns are pi minus these interior angles. Atanchor A_e, the3incidenttriangleangles aredelta_(u,A), 2gammaAe, delta_(v,A); the imposed equation gives pi−(theta_u+theta_v)/2. They arepositiveandsum<pi, sothedevelopedboundaryisstrictlyconvex. C1251 complexedge argument withlengthL_v=2sin(theta_v/2) makesitscircleunitradius. FLAT-DISK-REALIZATION thenproduces anactualunitdiskcover fromthese strictdata WITHOUT globalemptycircumcircle tests. For the reverse direction actualnormalizedcover data satisfytheconstraints fromVoronoiextraction.

Scope: strictpositiveface/radii/edge/ownerangles andvaliddisktriangulation. Candidateitselfhasalpha=pi forsomeowners; treatasclosureofstrictsystems ifapproximabilityproved, orseparateflatdegenerateembeddingargument. Aformaldegeneratealgebraicsolutionnotautomaticallyrealizable. Since necessarycovers canbe outwardclippedandlimited, a global exclusionproofmay use thelargercompactrelaxation safely. A constructionclaimedfromdegeneratesolutionsneedsmore.
