# Sharp independent-factor certificate: inverse feasibility interface

Purpose: audit the proposed q0 29-factor inverse problem BEFORE optimization. This is an elementary necessary-condition reduction; solving the linear system is not a global certificate. General finite factors, evaluated at a specified simultaneous feasible candidate x*. Use physical R=rstar, not a larger allowance.

Suppose a valid upper-area certificate has
 B(z)=c(z)+sum_k sup_{x_k in D_k} f_k(x_k;z),
 f_k=b_k(x_k)+a_k(x_k).z,
and at the candidate
 c(z)+sum_k f_k(x_k*;z)=pi+sum_j lambda_j s_j*,
where lambda_j>=0 and geometric inequality slacks s_j*>=0 (all equality terms vanish). Then
 B(z)-pi=sum_j lambda_j s_j* + sum_k [sup_Dk f_k-f_k(x_k*)].
Every summand is nonnegative. Hence B(z)=pi iff (i) lambda_j s_j*=0 for every inequality j, and (ii) each x_k* is a GLOBAL maximizer of its own factor. This equality decomposition avoids accidental cancellation of slack constraints and cannot be replaced by stationarity alone.

## Linear necessary conditions at smooth candidate points
For any factor coordinate q, define d_q=partial_q b and A_q=partial_q a. Its derivative is d_q+A_q.z. The area term b is fixed, NOT scaled by z, so the inverse system is AFFINE, not homogeneous. Artificial normalization z_i=1 or ||z||=1 can exclude all genuine solutions. If instead homogenizing with an objective multiplier z0, impose z0=1; z0=0 solutions are abnormal and do not certify the stated area objective.
- interior coordinate: d_q+A_q.z=0.
- upper endpoint coordinate with independent feasible decrease: d_q+A_q.z>=0.
- lower endpoint coordinate with independent feasible increase: d_q+A_q.z<=0.
- coupled active domain boundaries: use full tangent cone, not individual coordinate signs. At maxima every feasible tangent derivative is <=0.
Equality multipliers are unrestricted unless a deliberately narrower certificate family is specified. Inequality multiplier signs follow the exact assembled identity, not labels such as 'closure'. Strictly slack inequalities must have multiplier0 for sharpness.

## Independent copies versus shared variables
Original factorization is a Cartesian product of factor domains. For n11: 11 site triangles each (a,b,y) =33 variables; 9 switches each (b,y)=18 variables; 9 sectors each (alpha,u,v)=27 variables; total78 local copies. A switch radius y must not silently be replaced by a sector v or adjacent sector u before differentiating a SINGLE factor. If one intentionally couples these copies, they form a JOINT factor and differentiation must SUM all affected terms. The joint-factor global maximization problem then differs from the original29-factor relaxation. Shared candidate values do not identify independent optimization variables.

## Instrument gates
1. Verify assembled candidate value equals pi+explicit nonnegative slack, independently from geometric area.
2. At an arbitrary z, verify directional derivative of full f equals d+A.z (including d); residual .37 is failure, not float tolerance.
3. Known sign controls: maximize x on [0,1] at1 -> derivative+1 allowed; maximize -x at0 -> derivative-1 allowed. Interior b(x)=(x-.3)^2 at x=.2 plus z*x gives stationary z=.2, which a homogeneous test would miss. Stationarity here is not maximality (second derivative+2).
4. Enforce complementary slackness before testing sharp inverse feasibility.
5. If feasible affine LP, test necessary Hessian sign on each factor critical cone, THEN global competitors. Finite sampling may disprove a proposed support by a strictly better point; absence of a better sample cannot certify support.
6. A failed single z does not refute the family. A rigorous affine infeasibility/Farkas witness can refute the specified sharp-support family (not main covering theorem). Numeric finite-difference infeasibility is diagnostic only until matrices and candidate are rigorously enclosed.

## Current artifacts quarantined
r20-gluing/r20_kkt_active.py and r20_kkt_global.py as inspected initially omitted d, reversed endpoint signs, used69 variables by silently sharing switch/sector copies, and normalized a homogeneous cone. Active control reported .3708645. No claim is supported by those versions; member has been instructed to rebuild the interface, preserve erroneous outputs as nonbearing history, and calibrate before further scans. R=.38 versus candidate-radius confusion was an additional earlier issue. This note records root causes rather than patching outputs.
