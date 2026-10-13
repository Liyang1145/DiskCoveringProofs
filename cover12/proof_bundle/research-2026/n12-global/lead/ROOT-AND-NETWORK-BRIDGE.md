# Algebraic root and sharp candidate-network bridge

## Root (local algebraic existence and uniqueness, not coverage)
`root_t_certificate.py` defines integer-scaled F,G,H,T exactly as in EXACT-CANDIDATE-STRESS.md. Center is the saved numerical proposal rounded to exact rational grid10^-35, radius10^-30 in each of4 coordinates. Both center and endpoints are exact on the interval kernel's10^-45 grid (no hidden enlargement).

Let f=(F,G,H,T), Y the fixed rational preconditioner printed in evidence/root-t-certificate.json. On the whole closed box B, interval evaluation gives ||I−Y Df||_∞≤q<4.09×10^-28. For g(x)=x−Yf(x), interval mean-value enclosure K=c−Yf(c)+(I−YDf(B))(B−c) lies strictly inside B. Thus g is a self-map contraction, and Banach gives a unique fixed point x*∈B. Since ||I−YDf||<1, YDf is invertible and hence Y is invertible; fixed points are exactly zeros of f. This proves a unique F,G,H,T root in B, NOT absence of other roots elsewhere. Output contains exact rational box/image/preconditioner/contraction bound and self-map margins.

Guards a,t,r,w>0, b>w>0, r<U<1/2 are checked. b>w implies β=atan(w/(√3b))∈(0,π/6), hence α=π/3−2β∈(0,π/3). Remaining strict denominators and weight signs checked by stress_interval.verify on SAME box. H and G give high/low anchor distances exactlyr, with anchors0,2β,2π/3−2β,... and no squared-root branch ambiguity because angles are in these ranges. Consequently each owned arc gap≤2asin r≤2asin U (a radius-r disk cannot cover two unit-circle points separated along its shorter arc by more than2asin r; here each intended arc is shorter thanπ and centered on its site's ray).

## Graph identification
Full triangle block(3,3,3) graph in network_graph.py uses ring sites0..8, hub9 owning spoke edges0,1,2; hub10 edges3,4,5; hub11 edges6,7,8. Map ring index i→i−2(mod9), keep hub labels. Then hub9 owns7,8,0;hub10 owns1,2,3;hub11 owns4,5,6. Its HHR faces become(1,9,10),(4,10,11),(7,11,9), precisely stress_interval.py's active HHR faces. Its middle HRR faces become(8,0,9),(2,3,10),(5,6,11), the other3 active faces. Dropping other7 face witnesses is a relaxation; no assumption of slackness in a competing cover is required.

## Sharp lower bound for this graph
Positive weights, exact free force balance and exact angular balance follow identities in EXACT-CANDIDATE-STRESS.md with F,G,H,T=0. All36 retained edges have lengthr*. After normalization sumweights=1, candidate placement has energyr*². Free equilibrium and positive Dirichlet pivots identify it as the free-node minimizer. Certified M≥0 modulo rotations on the ENTIRE legal9-gap simplex shows global convexity of its Schur energy; stationary candidate anchors therefore minimize globally. Any placement of the full333 witness network must have at least one edge≥r*.

This is a lower bound on a specified relaxed graph for arbitrary (not D3-symmetric) competitors. It is NOT yet an upper bound at r*: the13-face ideal configuration's coverage is a separate obligation. It is also not yet unrestricted optimality: all remaining path/zero-block graphs and k10/k11 must be handled, and the cover→graph geometric interface audited.
