# Enlarged explicit local box: epsilon=1/50000

Same exact root,18positivecontacts,KKTidentityandgaugeas LOCAL-EXPLICIT-BOX.md; all28coordinatesfree, mixedHessiandirections retained. Replaceoldpenalty1000 byK=1:
 P(C)=sum_k [lambda_k delta_k+delta_k²/2]+y(X+)²/2.
Everycontact remainsvalid/nearest/interior throughoutroot-centered boxepsilon=2e−5; intervalchecks show2lambda_k+delta_k>0. Thus anycoverat<=r* inalignedgauge impliesP<=0.

The Hessian is sum[(lambda+delta)Hessf + gradf gradf^T]+e19e19^T. The oldinstrumentfirstformedallouterproducts inoriginalcoordinates andthencongruencetransformed, causing intervalwrapping. Newkernel transforms gradients BEFOREouterproducts: gW=g·W, thenadds(gW)^T(gW). Allentriesuse directedfixedpointintervals. This is algebraicallyidenticalbutavoidslargecancellation. The non-Gramterm istransformednormally. W is a fixedexactdyadicmatrix proposedfromK=1 rootmatrixCholesky; numericalproposalaccuracyisnotassumed.

For transformedHessianM throughoutbox, exactsumoverentries max(|Mlo_ij−delta_ij|,|Mhi_ij−delta_ij|)² <.771734<1. Hence ||M−I||_2<=||M−I||_F<1, provingMpositive definiteforallpoints. This is a fullmixed-direction test, not separateblockpositivity. W mustbenonsingularautomatically sinceM=W^THWpositive; replayalsoverifiesexactrank28 separately. Strictconvexity+exactstationarity givesP(C)>0 foranyotherpoint, contradiction. Therefore2e−5 box containsnoothercoverat<=r*, afterrotationalgaugealignment.

Scope remainsLOCAL, epsilon2000timesearlier1e−8 butNOT yetenoughfor~1e−4false-nearcovercoordinates. No promotiontoglobal, no samplingcertificate. Do not extrapolate froma successfulbox tolargerones.

Files: local_neighborhood_factored.py, local-neighborhood-factored-2e5.json/log/err. Matrix savedinfullrationalintervalform; local_matrix_fraction_replay.py independentlyrecomputesexactFrobenius boundandW rank, butshares savedgeometricenclosureinputs (notindependentADverification). BearingexactKKTidentity andADkernel remainthosealreadyusedin C1182.

ReproPowerShell:
 $env:N14_LOCAL_EPS='1/50000'; $env:N14_LOCAL_K='1'; $env:N14_LOCAL_MATRIX_TEST='frobenius'; $env:N14_LOCAL_OUTPUT='local-neighborhood-factored-2e5.json'
 py -3 -B research-2026/next-cover-global/lead/local_neighborhood_factored.py
 py -3 -B research-2026/next-cover-global/lead/local_matrix_fraction_replay.py
 Remove-Item Env:N14_LOCAL_EPS,Env:N14_LOCAL_K,Env:N14_LOCAL_MATRIX_TEST,Env:N14_LOCAL_OUTPUT

Failedtests: oldK1000epsilon1e−4failsfeasiblepenaltysign; K1originalouterproductepsilon1e−4failsintervalLDL; factoredK1epsilon1e−4 and5e−5 failintervalLDL, notdisproofs. epsilon1e−5 passesLDLminpivot.84708andFrobenius².192659; epsilon2e−5passesFrobenius².771734. Initialcopyindentationfailurefixedbeforemathematicalruns.
