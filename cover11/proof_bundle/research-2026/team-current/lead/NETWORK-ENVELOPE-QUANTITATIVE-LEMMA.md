# Quantitative finite harmonic-stress envelope, angular chart

Take theta8 fixed (8 Euclidean angular variables x, ninth component0). Let alpha0 be C909's normalized radial stress, and let N (45x4) be any exact basis of normalized fixed-anchor harmonic-stress variations. Every alpha0 +/- eps N_col is nonnegative when eps max|N_jk| < min alpha0. They then belong to A*: normalized, balanced, supported on45 tight edges. Therefore all nine reduced energies f0,fk+/- attain R*² at theta*, and are global lower bounds for V(theta)². At the candidate their angular gradients are 0 and +/-eps G_col respectively, G=T N. This linearity of the gradient at the candidate uses harmonicity of the SAME candidate free coordinates for all stresses; it does not assume the Schur complement is linear in alpha.

## Uniform remainder control (independent of small stress eigenvalues)
For any normalized nonnegative stress on the graph, eliminate its free nodes to get the boundary Laplacian Lambda. It is a Laplacian: offdiagonal<=0 and Lambda*1=0. This follows from the Dirichlet energy minimum/maximum principle (or elimination of a positive conductance node); isolated free components can be discarded. Also Lambda<=L_AA in PSD order. Here L_AA is diagonal (no anchor-anchor edges) and tr L_AA is the sum of the18 endpoint weights, <=1. Thus
 W=sum_{i!=j}|Lambda_ij|=tr Lambda<=1.
The diagonal term is constant on unit-circle anchors, and
 f(theta)=tr Lambda+sum_{i!=j}Lambda_ij cos(theta_i-theta_j).
For a direction x (ninth component0), |x_i-x_j|<=sqrt(2)||x||. Consequently
 |D²f[x,x]|<=2||x||²,
 |D³f[x,x,x]|<=2sqrt(2)||x||³.
Hence ||H||_2<=2 everywhere and the Taylor remainder after second order is <=sqrt(2)/3 ||x||³< ||x||³/2. First-order remainder has absolute value<=||x||². These bounds hold uniformly for every member of the finite stress family; no unproved 'quadratic in angles' assertion is used.

## Explicit sufficient radius
Let S=im G (in the8-coordinate chart), K=ker G^T, and sigma_min(G)>=sigma>0. Define c1=eps*sigma/2. Since four coordinates satisfy max|v_j|>=||v||/2,
 max_{k,+/-} (+/-eps G_col·x)>=c1||x_S||.
Assume H0 restricted to K has Rayleigh lower bound mu>0. Put M=2/c1. For q=||x|| and s=||x_S||:
- If s>=M q², a finite-family branch gives f-R*²>=c1*s-q²>=q².
- If s<M q², use f0 (whose gradient is exactly0), ||H0||<=2 and k²=q²-s²:
 f0-R*² >= (mu/2)q² - (mu/2+1)s² -2s q -(1/2)q³
 >= [(mu/2) -(2M+1/2)q -(mu/2+1)M² q²]q².
Choose any rho>0 for which
 (2M+1/2)rho +(mu/2+1)M²rho² <=mu/4.
Then V(theta*+x)²>=R*²+min(1,mu/4)||x||² for ||x||<=rho.
This gives an explicit certified local patch once eps,sigma,mu are enclosed. It is not a global lower bound on the entire8D angular domain.

## Kernel plan and checks
interval_network_envelope.py uses C891's interval root to construct all carrying nodes; its balances use UNNORMALIZED displacements, equivalent to unit-force balances since every carrying edge length is exactly R*. C909 supplies existence of a full radial solution; the validated square subsystem only encloses that known solution, and does not declare other rows zero from interval residuals. The41x45 normalized harmonic matrix has an invertible41column minor, hence full row rank; its4 free coordinates construct N exactly. Four selected angular rows give exact rank4 of G; the fixed-theta8 kernel K is constructed by another inverse. The Schur matrix uses only20 nonisolated free nodes. All inverse bounds are Neumann-preconditioned interval enclosures; floating inverses/QR/Cholesky only select exact dyadic preconditioners, each checked by contraction. Congruence H_K is interval-positive with a dyadic Q and interval Gershgorin margin>.95; Q invertibility is checked independently by contraction.
