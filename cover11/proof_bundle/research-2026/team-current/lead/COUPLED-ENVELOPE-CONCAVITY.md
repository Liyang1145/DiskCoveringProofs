# Correct coupled concavity test for secant radial hub envelopes

Fix outer(r,b1,b2) and a convex hub subdomain C on which each local distanceLj lies in a verified positive interval[lj,uj], and the angle branch is continuous. Let beta>0,gamma<0,a>0 as in RADIAL-SECANT-HUB-ENVELOPE.md. Exact radialsecant:
 beta Lj²+gamma Lj <= mj Lj-beta lj uj, mj=beta(lj+uj)+gamma.
Assume mj<0 and set cj=-mj. The candidate envelope is affine+sum(aj theta_j-cj Lj-beta_j lj uj).

**Individualterms are NOT concave.** In radial/tangent basis Hess(aj theta-cj L) has entries [[0,-aj/L²],[-aj/L²,-cj/L]] up to reflection/sign. Determinant=-aj²/L⁴<0. A lowerbound L>=aj/cj cannot change this. Testing only the radial/tangent diagonal directions misses positive mixedcurvature.

**Sufficient coupled criterion, pointwise:** let nj be the unit radial vector in the common(v,t) coordinates, pj=cj/Lj>0. The negative norm Hessian is
 -S, S=p1(I-n1n1^T)+p2(I-n2n2^T).
It has trace p1+p2 and determinant p1p2(1-(n1·n2)²)=p1p2 sin²omega. Thus
 lambda_min(S)=(p1+p2-sqrt((p1+p2)²-4p1p2 sin²omega))/2.
Each angleHessian has spectralnorm aj/Lj², invariant under reflections. By Weyl's inequality,
 Hess(envelope) <= [a1/L1²+a2/L2²-lambda_min(S)] I.
If the bracket <=0 on the ENTIRE convexdomain C, the envelope is concave on C. If strictlynegative, it is stronglyconcave. This criterion is sufficient, not necessary; fullmatrix intervalbounds can be sharper.

An interval-friendly weaker lowerbound is lambda_min(S)>=det(S)/trace(S), since lambda_max<=trace. Therefore a verified bound
 a1/l1²+a2/l2² <= (p1_low p2_low sin²omega_low)/(p1_high+p2_high)
certifies concavity. Directions nearlyparallel make this bound useless (methodlimit). Angles/singularities/sourcepoints must be handled, not assumedaway.

Once concavity is established on C, ANY selectedX0∈C gives globaltangentupper Fenv(X)<=Fenv(X0)+gradFenv(X0)·(X-X0). Optimize the affine form over C by a rigorous supportbound (eachdiskalone gives support, minimum ofthoseupperbounds valid; dualcombinations may sharpen). If using a constrainedKKT point instead, exact/interval stationarityplusnormalcone conditions suffice, but solveroutputalone doesnot.

Scope: analytic criterion for a fixedouterparameter convexsubdomain and radialsecantupperenvelope. It is not a proof of concavity of originalobjective, not globalridgeelimination, and not a completed sector2exclusion. C860 demonstrates the latter ridgehypothesis is false evenfor b1,b2>.9.
