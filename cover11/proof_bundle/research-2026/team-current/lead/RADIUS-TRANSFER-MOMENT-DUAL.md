# Radius transfer of moment/closure exclusion certificates: direct source audit

Scope: fixed graph and fixed saved rounded-rational dual coefficients in certify_shared_moments_dense.py, certify_q0_moments.py, certify_q0_closure.py and lower375 closure kernel. This checks transfer in radius, NOT the underlying face decomposition or graph-class exhaustion.

## Correct constant and signs
All use
C0(r)=pi(sum z[:9]+2sum z[9:11]+sum z[50:71]−2z[71]−2z[72])+2z[72]asin(2r),
with closure kernels additionally subtracting pi*sum z[112:]. There are NO extra r factors multiplying the linear pi penalties. Slots71/72 mean lam/eta consistently in these source files.
Saved q1 orbit0: lam=0, eta=.437458336 after9-place rounding; orbit2: lam=0, eta=1.357679461. Thus eta is NOT zero in q1; C0 is nevertheless nondecreasing, since eta>=0 and r<1/2. q0(4,9): lam=.482812259, eta=0. Closure k3/k4: both0. All ring C=lam+(eta if i>=3 else0)>=0. All closure coefficients h_i=z[112+i] are strictly positive in the two saved closure proposals; ordinary rounding to9places preserves this.

## Pointwise comparison, not interval-algorithm monotonicity
Use normalized variables u,v in[0,1], triangular angles a,b,c>=0,sum=pi, and switch b in[0,pi/2]. The other linear and quadratic moment terms have r-independent coefficients.
Face radius parameter x>=0 enters area as 2r²*x*sin(a)sin(b)sin(c), hence pointwise nondecreasing in r. Taking its supremum (implemented as quadratic support in sqrt(x)) preserves the inequality.
Switch area is r²*x*sin(2b)/2, again nondecreasing for x>=0.
Ring q=(u−v)²+4uv sin²(a/2) in[0,4], w(r)=2asin(r sqrt(q)/2) is nondecreasing. Its r-dependent part is
r² uv sin(a)/2 +(w−sin w)/2+Cw,
whose derivative is r uv sin(a)+[(1−cos w)/2+C] w'(r)>=0.
Closure adds (h_left−h_right)*beta−h_right*a+h_right*pi+(h_left+h_right)*w/2. Here beta=atan2(v sin(a),u−v cos(a)) is independent of r (limits treated by the closed original domain). Since h_left+h_right>=0, this extra part is nondecreasing too.
Therefore the EXACT factor functions and their domain suprema, not necessarily the implementation's intersected interval bounds as functions of r, are monotone. An enclosure for the supremum at R bounds all smaller-radius suprema once domain nesting is checked.

## Closure-domain nesting
The closure ring screen uses q>=qmin(r)=4sin²(pi−8asin r)/r². Nine boundary arcs, each at most2asin r, force r>=sin(pi/9); smaller r are already impossible for a9ring cover. On sin(pi/9)<=r<=19/50<sin(pi/8), A(r)=pi−8asin r lies in(0,pi/9]. Both sin A(r) and1/r are positive decreasing; thus qmin(r) decreases. Hence for r<=R, the smaller-radius permitted q-domain is a SUBSET of the domain at R. The same holds when R=3/8. Screened-out boxes at R cannot contain a legal smaller-radius q.
Combining nesting, factor monotonicity and nondecreasing C0 proves total_bound(r)<=the certified upper at R, for every legally possible smaller r in the relevant9ring class. No rerun at scaled r and no new coefficient optimization is required.

## Audit corrections
The member's first alleged transfer gap was based on a wrongly transcribed constant. Its corrected version still incorrectly asserted eta=0 in q1, ignored closure w-term and radius-dependent qmin, and called the area2r²product 'twice area' (it is the actual area when sides=2r sin angles). These assertions are not used here. No registered exclusion is downgraded on those drafts. This note closes only the radius-transfer interface using the actual source and sign data.
