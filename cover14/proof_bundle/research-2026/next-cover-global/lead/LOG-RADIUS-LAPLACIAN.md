# Fixed-angle radii: convex Dirichlet kernel, not convexity in beta

Let l_f=log R_f, l_g=log T_g, beta_e∈(0,pi) fixed. The paired angle atface f is h(R_f,T_g,beta_e). Directdifferentiation gives
 dh/dl_g = -dh/dl_f = w_e = sin beta_e/[2(cosh(l_f−l_g)−cos beta_e)] >0.
Thus G_f(l)=pi−sum_e h(R_f,T_g,beta_e) has symmetricJacobian: diagonals sumincidentw, offdiagonal −w. Forfixedboundaryanchorlogradii, quadraticform is
 z^T DG z = sum_interiorfaceedges w_e(z_f−z_g)² + sum_boundaryfaceedges w_e z_f².
On a connectedfacetnetwork touchingboundarythisispositivedefinite. Therefore G isgradientofastrictlyconvexpotentialon allrealface logvariables, uniquecriticalpoint ifexists. Thisis astrongerformofthefixed-anglecomparison theorem: the16realradii may inprinciplebeeliminated deterministicallygiven29betasand10anchorradii, subjecttoexistence/radiuscaps. No claimpotentialconvexityinbeta, no jointglobalcoverconvexity.

Risk interface: beta→0orpi orradiusratiosunbounded can destroyuniformpositiveconditioning; numericalNewtonconvergence notexistencecertificate. A verifiedpositivebox+intervalJacobian/rootinclusion can certifytheDirichletsolutionatfixedparameters, notarbitraryparametercontinuumwithoutbounds. Eliminatingradii stillleaveshardboundarycyclicityconstraints; notgloballysolved.

Literature alreadycovers thisfamily: Bobenko–Springborn, Variational principles for circle patterns and Koebe's theorem, Trans. AMS356(2004),659–689, https://www.ams.org/journals/tran/2004-356-02/S0002-9947-03-03239-2/ . TheirEuclideanfunctionalstrictconvexitymodscaling andcoherentangleexistence principle are relevant. No noveltyclaim. Currentbeta is angleatsharedsitebetweenradiusrays; matchtheirinterior/exteriorintersection conventions before importing anyexistence theorem. Directkernelabove needs no externaltheorem.
