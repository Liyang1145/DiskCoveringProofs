# Parameterized scalar stationary-root contraction (necessary only)

Let u=(r,b1,b2), p boundary parameter and g(u,p)=∂F/∂p. For a box U×J smooth in p and a fixed midpoint m∈J, every stationary (u,p*) satisfies 0=g(u,m)+g_p(u,xi)(p*−m). If interval C encloses g_p(U,J) and 0∉C, p*∈m−g(U,m)/C. Intersect J with this interval; emptiness excludes all stationary points. When C crosses0 or any smooth enclosure refuses, do not contract. Apply at mosttwice; no assertion about nonstationary arc points. Any legal stationarymaximum remains in contracted box.

low_stationary_contract.py implements this. Outer derivatives via all_boundary_derivative.py; norm derivative9point firstADcontrols and3secondorderADcurvaturecontrols; scalarface derivative original audited Cartesian formula. check_stationary_contraction.py calibrates5 rootinclusions with separate Brent roots; calibration not mathematicalproof.

After contraction low_stationary_bound.py may use: direct legalCartesianvaluebound; gradientinterval excludes0; positivecurvature excludeslocalmaximum; or stationary-only Taylor f(u,p*)=f(u,m)−.5*f_pp(u,xi)*(p*−m)^2. This last formula requires the whole interpolation segment in the full smooth extension, NOT in the physical legal domain. Physical constraints used only for separate direct value bound. If derivative/angle/sqrt extension fails, only value bound survives.

Corner endpoints are C873. To combine stationaryvalueswithcorners one still must prove all legal arc endpoints accounted, exclude source poles/wedge edges in positivewidthdomain and handle coincidentfacecircles. C871 gives nointeriorhubmaximum; it does not automatically certify all these boundaryinterfaces.
