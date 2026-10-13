# Boundary anchor is on the exterior side of its site edge

NEW analytic observation, uses the unitdisk geometry omitted by radius-only relaxation.

Strict clipped representation: distinct sitesu,v inintD, genuine boundaryfacet [O,A], A∈S1, O∈intD. Choose u=(0,0),v=(l,0), l>0 and trianglethirdsitew withw_y>0. Nearestinequality givesh_A<h_f forA=(l/2,h_A),O=(l/2,h_f). Letm=(u+v)/2. Ifh_A>0, thenh_f>h_A>0 and
 A=(1−h_A/h_f)m+(h_A/h_f)O.
Bothm andO areinintD, soA∈intD, contradiction. Ifh_A=0,A=m∈intD, also contradiction. Thus **h_A<0**. Noassumptionh_f>0: obtusefacesh_f<0allowed.

Consequences: virtualangle gamma_A=pi/2+atan(2h_A/l) lies(0,pi/2). AtA theinwardfacet rayAO divides theanglebetweenAu,Av into twoanglesgamma_A. Realfacegamma_f+gamma_A=pi−beta asbefore. Therefore onboundaryedges
 gamma_A<pi/2, equivalently y_e−x_f cosbeta_e>0,
 usinggamma_A=atan2(x_f sinbeta_e,y_e−x_f cosbeta_e).
This is a NEWnecessaryinequality, not a premise needed for olddeficitproof. Thatproofsafelyallowedbothsigns; its warnings againstassumingpositiveh_A remaincorrect. CurrentargumentprovesNEGATIVEh_A from convexity of theclippingdisk and actualinwardfacet, notfromradii alone.

For eachboundaryownercell, under the ADDITIONAL normalized normcap and ownedarc bounds, the ray-order proof in BOUNDARY-CYCLICITY-PROOF.md shows the site rays lie between their corresponding anchor chord and the inward bisector. Do not infer this from h_A<0 alone or assume an entire wedge triangle tiles the cell. Consequently the interiorangleofpolygonofboundaryanchors is
 delta_(u,A)+2gamma_A+delta_(v,A),
 withnonnegative summands, noextra2pi branch. Theanchorpolygon isconvex sinceanchorsorderedonS1. Itsinteriorangleequals pi−(theta_u+theta_v)/2, whereadjacentownedarcangles theta<pi. Thus **allboundarycyclicityequations inBOUNDARY-CYCLICITY-INTERFACE.md holdunwrapped globally** in strictclippedrepresentation. Limits retainnon-strictinequalities/equalitiesprovidedendpointanglevariablesretained; atanformulas aloneundefinedondegeneracies andmustbereplacedbyangle/lengthrelations.

Degenerateextension: passconstantgraph/compactangles beforecapU. Forzerolength/fanedges useangle-limitvariables; doNOTdefineatan2(0,0). Consecutiveanchorsmaymerge, buttheta=0 andlimitingdelta retained. Thelinearcyclicityequations persist. Thisismorethan sumtheta=2pi; theirsumhasoneautomaticdependencyfromEuler/siteangleledger.

Next: independently testh_A<0 onlegal perturbedcovers and derive angle-only necessarylinearconstraints includingdelta andgammaA, beforebuilding global certificates. No newgraphcount inthisnote.
