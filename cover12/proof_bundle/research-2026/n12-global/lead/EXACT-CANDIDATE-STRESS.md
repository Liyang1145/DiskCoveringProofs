# Exact candidate network stress from seven edge orbits

Conditional analytic theorem: assume (a,t,r,w) satisfies F=G=H=T=0 in a sufficiently small box around evidence/d3-chart-calibration.json, with the guards below. Root existence and full disk coverage are separate obligations; no identification of arbitrary competing topologies is asserted.

Set b=(1+a+r)/2, v=w/√3, d=a+r, s²=b²+v². The chart equations F,G,H are in D3-EXACT-CHART.md. Replace the purely optimizing determinant equation J there by the following force-balance polynomial (rational coefficients after substitution):
A=3b²−w²−2bw,
T=w(s²)²(2a−t+r)(1−t²−r²)+(s²−b)(2t−2r−a)t² A.
This is not an assertion J=T as polynomials. Defining the root by F,G,H,T suffices directly for the stress argument, bypassing any resultant or ideal-membership bridge.

## Geometry and unnormalized weights
Let β=arg(b+iv), α=π/3−2β. Boundary anchors around each sector occur at0,2β,2π/3−2β,2π/3. High sites are(b,±v) and rotations120°; low sites are t u(π/3) and rotations; hubs are a u(0) and rotations. Active HRR witness is d u(0); active HHR witness is(t−r)u(π/3). Equation H guarantees high sites distance r from both(1,0) and(d,0); F guarantees HHR distances; G implies low boundary distances on the intended α branch.

Assign the following seven weights, all rational functions of(a,t,r,w):
- x=−b r²/(s²−b): high site to shared anchor at its adjacent hub axis.
- y=(b−1)s²/(s²−b): high site to transition anchor.
- z=j r t/(1−t²−r²): low site to each transition anchor.
- p=1: HRR witness to each high site.
- q=2(1−b)/r: HRR witness to hub.
- u=q r/(2a−t+r): each HHR witness to either adjacent hub.
- j=u(2t−2r−a)/r: HHR witness to low site.
Total W=6x+6y+6z+6p+3q+6u+3j. Normalize every edge weight by W.

## Free-node equilibrium: direct vectors
At an HRR witness(d,0), the two p edges sum2(d−b)u(0) and the hub edge adds qr u(0). Since d=2b−1,2(d−b)+qr=0.
At a hub(a,0), its q edge contributes−qr u(0). Its two HHR witnesses at(t−r)u(±π/3) contribute u(2a−t+r)u(0); definition of u cancels them.
At HHR witness in its rotated axes, the two hubs are(a/2,±√3a/2), so their weighted force is u(2t−2r−a)u(0). Low site contributes−jr u(0), hence zero.
At a low site, its two anchor vectors sum2(t−cosα)u(0); witness contributes jr u(0). G gives cosα=(1+t²−r²)/(2t), hence2(cosα−t)=(1−t²−r²)/t and definition of z gives zero.
At a high site(b,v), its three neighbors are anchor(1,0), anchor(cos2β,sin2β), witness(d,0). Solving the two linear vector equations gives exactly x,y above, using(d−1)(d+1−2b)=0 and (1−b)²+v²=r². In particular this is an identity on H=0, not an assumed nullspace rank.

## Anchor angular equilibrium
At each hub-axis anchor, reflection cancels tangential force. At a transition anchor at angle2β, the high site angular cross component is−v; the low site component is+t sinα. Tangential balance is yv=z t sinα.
Using sinα=(3b²−w²−2bw)/(2√3 s²)=A/(2√3 s²), this is
2y w s²−z t A=0.
Substitute y,z,q,u,j; factor the common nonzero2(b−1), and multiply by(s²−b)(2a−t+r)(1−t²−r²). The remaining equation is T=0 above. Thus angular gradient of the minimized Schur energy vanishes exactly, not merely to numerical precision.

## Guards and certification status
Need: r,t,w>0; b<1; s²−b<0;2a−t+r>0;1−t²−r²>0;2t−2r−a>0;0<β<π/6 and intended tiling α>0. These hold numerically with margins and the relevant weight/division signs are certified on the narrow input box by stress_interval.py. Geometric branch guards must be checked in root-cover certificate.

All36 positive-weight edges have exact lengthr. Free equilibrium with positive Dirichlet Laplacian means the depicted free placement is the unique energy minimizer for these anchors. Hence E(θ*)=r² exactly. Combining exact angular stationarity with GLOBAL-STRESS-CONVEXITY.md and its certified M gives the global lower bound for this relaxed network on the entire legal anchor simplex.

## Interval kernel run
lead/stress_interval.py used a rational box of halfwidth10^-38 about the recorded65-place numeric root coordinates. Every arithmetic primitive is rounded outward to the exact rational grid10^-45; divisors require a strict sign. It certified7 positive weight orbits,18 positive Dirichlet elimination pivots, nonnegative Schur conductances and8 positive pivots of the constant Hessian principal minor. Evidence: evidence/stress-interval.json. This proves conditional matrix inequalities throughout the box, NOT that a root lies in it. Candidate member must certify a root of F,G,H,T in this box or supply another box to verify().
