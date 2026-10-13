# Lead mathematical audit of local network certificate

This is a direct analytic/code audit, not an independent-member review. The initial closure-kernel report contains incorrect algebra and is NOT bearing evidence. Corrected prose in that report is not used as a premise either.

## Object and exact identities
At the exact C891 root, C909 supplies normalized nonnegative edge lengths weights alpha0 on all45 carrying edges, harmonic at the20 free nodes, with radial anchor loads. Convert force magnitudes w_e to energy weights alpha_e=w_e: each edge length is the same R*, so force equilibrium for w_e*(Xv-Xw)/R* is equivalent to energy balance for alpha_e*(Xv-Xw). Thus B alpha0=e40, T alpha0=0. Root geometry and raw labels in lines14–30 match the active faces of C892; the two slack auxiliaries are absent, not silently pinned. Reduced energy is a global lower bound for full-oracle squared radius for any nonnegative normalized alpha, even with those six zero edges.

## Validated solve
For any real M,b contained in input intervals, dyadic Ci and y are fixed. E=I−Ci M has infinity norm <=q<1, computed with outward interval sums (q inflation now interval too). Therefore Ci M is invertible and M,Ci are invertible. The exact correction e to y obeys e=v+Ee, v=Ci(b−My). For multiple RHS, matrix infinity norm is submultiplicative, so ||e||inf <=||v||inf/(1−q). This uniform entry box encloses the solution; each interval substitution v+E*box continues to enclose e, with no need to infer equality from residual containment. Twelve iterations tighten only. All floating inverse/QR choices are proposals, subsequently enclosed and verified.

The selected45-row subsystem encloses alpha0 whose full identities are guaranteed by C909. No omitted T equation is inferred from intervals. The41-column B subsystem is invertible, giving rankB=41 and nullity4 by rank-nullity, independently of C909. Setting four free columns to I and solving defines exact N with BN=0, rankN=4. Each alpha0±N_j/1000 is normalized and harmonic. alpha_min>.0029 and max|N|/1000<.0029 are directly verified.

## Angular spaces and singular-value bounds
T differentiates the UNNORMALIZED energy: T_ij=2 sign*(Xv−Xw)·JU_i for anchor i. Because the SAME free candidate coordinates minimize every finite-family energy, their gradients at the candidate are ±G_j/1000, G=TN. Fix theta8, and use G8 (8x4). A verified4x4 minor proves rankG8=4. K (9x4 with last row0) solves G^T K=0 and spans this fixed-chart kernel.

A=(G8^T G8)^−1 is symmetric positive definite. Its largest eigenvalue is <=||A||inf, not >=. If the interval matrix norm upper bound is a, sigma_min(G8)>=1/sqrt(a). The code verifies this lower bound>1/4.

The weighted graph Laplacian L has positive weights and every free component attached to anchors, hence Lff is positive definite (also inverse certified). Schur Lambda is the Dirichlet response. On unit anchors,
f=tr Lambda + sum_{i!=j}Lambda_ij cos(theta_i−theta_j).
Thus H_ij=2 Lambda_ij cos(theta_i−theta_j) for i!=j, H_ii=−sum_{j!=i}H_ij. H need NOT be positive semidefinite: row sum zero is not sufficient for that.

Put HK=K^T H K. Exact dyadic Q is separately verified invertible, and interval Gershgorin gives Q^T HK Q >=.95 I. Any fixed-chart critical x has the form x=KQz. Then x^T H x>=.95||z||² and ||x||²<=||KQ||F²||z||². Consequently H restricted to the critical space has lower Rayleigh bound .95/||KQ||F²>1/600, as the code verifies. No claimed relation involving Q^{-1} and KQ is needed.

## Uniform angular remainder, independently checked
For every normalized nonnegative stress in our finite family, maximum principle/Schur elimination gives Lambda_ij<=0 for i!=j and zero row sums. Schur minimization gives Lambda<=Laa in PSD order. There are no direct anchor-anchor edges, so tr Laa=sum(endpoint weights)<=1. Hence W=sum_{i!=j}|Lambda_ij|=tr Lambda<=1. In a fixed-theta8 chart, |x_i−x_j|<=sqrt(2)||x||. Direct differentiation of the cosine sum gives |D²f[x,x]|<=2||x||² and |D³f[x,x,x]|<=2sqrt(2)||x||³ uniformly along the entire segment. These are genuine directional derivatives for every x, not sampled axes. Symmetry implies operator norm of H<=2. Taylor remainders are <=||x||² at first order and <=sqrt(2)||x||³/3<||x||³/2 at second order.

## Mixed terms and exact constants
In R8 let x=k+s with k in ker G8^T and s orthogonal. For four columns max_j|G_j·x|>=||G8^T s||/2>||s||/8. Multiplying eps=1/1000 yields c1=1/8000. Set q=||x||, s0=||s|| and M=2/c1=16000. If s0>=Mq² the finite branch lower bound c1*s0−q²>=q² suffices. Otherwise f0 is stationary and
f0−R*² >= (mu/2)||k||²−2||k||s0−s0²−q³/2
>= [mu/2−(2M+1/2)q−(mu/2+1)M²q²]q².
This retains the mixed term. With mu=1/600, rho=1/10^8, the code directly checks the exact rational sufficient inequality (2M+1/2)rho+(mu/2+1)M²rho²<mu/4. Therefore V²>=R*²+||x||²/2400 for ||x||<=rho. growth=1/2400 is the theorem's mu/4, not a conclusion from a JSON field being read downstream.

## Status and limits
Every arithmetic premise above is replayed by interval_network_envelope.py; all exact identities are justified structurally. This proves an explicit local patch only. It does not exclude any other part of P and cannot complete n11 global optimality. The exact-root domain is C891, not C529 decimal centers. No successful independent member review is claimed.
