# Safe area-angle relaxation: arbitrary boundary subarcs allowed

## Geometric necessary interface
Use C1171 at outward clipping radiusRε, then normalizeD to1 andρ=(r+ε)/Rε. Sites satisfy norm<sρ, all cells contain their sites, every positiveboundaryowner hasonearc, hiddenfullcellsbounded. Let q positiveowners, N distinctsites, and triangulateddual diskgraphG.

Each actual interior Voronoi facet is asegment p–q sharedbytwocells. The triangles c_i p q and c_j p q arecongruent: samepq, equal endpointdistancesfromci,cj, andsitesonoppositesidesofbisector. Their angles atsites equalβ_e∈[0,π]. Each endpointdistance≤ρ. Pairarea≤ρ²sinβ_e. For an inserted triangulation diagonal, takeβ_e=0; its copiedcommonwitness giveszerotriangle. Thussumedgepairs boundsallstraight-facetwedgeareas.

Forboundaryowner i, itsarcθ_i∈(0,L], L=2asinρ. Normci≤sqrt(1−ρ²)≤cos(θ_i/2), so ci isontheorigin'ssideofchordbetweenarcendpoints: projectionontochordnormal≤normci≤cos(θ_i/2). Thus the curved wedge angleα_i atci is in[0,π], and wedgearea equals trianglearea+(θ_i−sinθ_i)/2. Trianglearea≤(ρ²/2)sinα_i. NO assertion relatingθ_i toα_i is made; theprevious falsef(α) bound isnotused.

Convexity of g(θ)=θ−sinθ on[0,L] andg(0)=0 givesg(θ)≤θ g(L)/L. SinceΣθ_i=2π, totalcaparea≤π(1−sinL/L). Site-angle sums give

    α_i+Σ_(e incident i)β_e=2π   (boundary site),
         Σ_(e incident i)β_e=2π   (hidden site).

Therefore everycoverforces

    π ≤ cap(ρ) + (ρ²/2)Σ_i sinα_i + ρ²Σ_e sinβ_e,
    cap(ρ)=π(1−sin(2asinρ)/(2asinρ)),

for some α,β∈[0,π] satisfying thelinearangleequations. Allmixedsitecouplingsarekept. Degeneratefacets andfan-addeddiagonals handledbyzeroβ. ForstrictupperboundatU, usemonotonicityρ² andcap(ρ): sinL/LdecreasesforL∈(0,π), so upperthresholdvalidforanyρ≤U; tohandleoutwardclip, aSTRICTcertificateatU persistsforρ>U sufficientlyclose. Finitecatalogue/limitC1171 completesnecessaryreduction.

## Rigorous supporting-plane certificate
Variables t_j = α_i,β_e, coefficients a_j=U²/2 orU², incidence matrixB with one1forboundaryangle andtwo1sforedgeangle. LegalBt=2π1. ChooseANYrationalproposal t0_j∈[0,π] andANYrationalnodepotentials y. Concavitysin on[0,π] gives

    a_j sin t_j ≤ a_j(sin t0_j−t0_j cos t0_j)+a_j cos t0_j t_j.

Subtract p_j=(Bᵀy)_j and bound0≤t_j≤π:

    totalarea ≤ cap(U)+Σ_j a_j(sin t0_j−t0_j cos t0_j)
               +2πΣ_i y_i +πΣ_j max(0,a_j cos t0_j−p_j).

EverythingontheRHS canbeenclosedbyexactdirectedintervals; nooptimized-pointfeasibilityorKKTassumptionneeded. AnegativegapRHS−π rigorouslyexcludesgraph. Numericaloptimizationonlyproposes t0,y. Failuretogetanegativebound isnotrealizability.

## Calibration / contrast
Naiveoldowned-subarc f(α) bound disprovedbyarea_wedge_counterexample.py. Newbound deliberatelydrops thatconstraintandneverusesitsnumericaloutputs. `area_safe_probe.py` tests12q11graphs, somebutnotallnominalmaxima<π. Exactsupporting-plane certifiernext. No claimregistereduntilconstantkernel+geometricinterfaceaudited.
