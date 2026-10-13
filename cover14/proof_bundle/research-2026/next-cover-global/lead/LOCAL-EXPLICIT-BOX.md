# Explicit local exclusion box: 10^−8 per center coordinate

Depends on the exact KKT stationarity proof in LOCAL-SOSC-PROOF.md. Candidate C* and r* are C1167's exact root construction; multipliers λ are the exact positive normalized solution certified there. Use only the 18 positive-multiplier contacts. Gauge y(X+)=0.

For δ_k(C)=f_k(C)−r*² define

    P(C)=Σ_positive [λ_k δ_k(C)+500 δ_k(C)²]+500 y(X+)².

At C*, P=0 and ∇P=0 exactly by the active contact identities and KKT stationarity. On the axis-aligned box |C_j−C*_j|≤10^−8:

1. Each positive contact remains a genuine nearest-site witness (boundary or interior); all nondegeneracy, branch, interior and other-site separation inequalities are checked by directed intervals.
2. The kernel proves 2λ_k+1000δ_k(C)>0 throughout the box. If a configuration covers at radius≤r*, every δ_k≤0, whence δ_k(λ_k+500δ_k)≤0. In the gauge this implies P(C)≤0.
3. The kernel proves the Hessian

    Σ_positive [(λ_k+1000δ_k) Hess f_k
                   +1000 ∇f_k∇f_k^T] +1000 e_19 e_19^T

is positive definite throughout the entire box. All 28-coordinate mixed directions are included. A numerically proposed inverse Cholesky factor of the root matrix is converted to a fixed exact dyadic matrix W; interval LDL certifies Wᵀ Hess(P) W positive definite, hence also proves W nonsingular and Hess(P) positive definite. There is no assumed numerical inverse accuracy. The successful 10^−8 run has minimum transformed LDL pivot lower bound >0.9697.

The interval domain in code encloses the root coordinate intervals plus/minus 10^−8, hence contains the stated exact-root-centered box and every segment from C* to a point in it. Strict convexity and P(C*)=∇P(C*)=0 imply P(C)>0 at every other point of the box. This contradicts item2 for any other cover of radius≤r*.

Therefore this explicit gauged box contains **no other configuration covering D at radius≤r***. Rotations may first be removed by the gauge; the box condition applies after alignment, not to arbitrarily chosen unaligned coordinates. This is a local statement and does not exclude remote configurations or other graph branches globally.

Reproduce (PowerShell, ensure N14_LOCAL_EPS unset for default):

    py -3 -B research-2026/next-cover-global/lead/local_neighborhood_certificate.py

Evidence: local-neighborhood-certificate.json. Default epsilon=1/100000000. Initial attempts at10^−6 and10^−7 failed interval LDL because of enclosure width, NOT a counterexample to local convexity. No need to scale this instrument merely to enlarge a small neighborhood before the global representation is ready.
