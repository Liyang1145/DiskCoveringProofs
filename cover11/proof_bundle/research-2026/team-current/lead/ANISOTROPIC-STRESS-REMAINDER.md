# Direction-dependent stress loss (not a uniform b*q bound)

Same C891/C909 root, raw8 chart, q=||x||, p=||G8^T x||; Q=tau N G8^T. Let B=max_e ||N_e||/alpha_e, and let A map t in R4 to anchor flux of stress Nt at root. Then beta(x):=max_e |(Qx)_e|/alpha_e <= tau B p; ||Mx||<=tau ||A|| p. Both vanish on the critical kernel G8^T x=0, unlike the old bounds b*q,m*q.

Retain the finite-Taylor setup of ADAPTIVE-STRESS-FINITE-REMAINDER.md. Put R_i=U_i(x)-U_i-v_i+(x_i^2/2)U_i, ||R||<=q^3/6 (valid both signs). Let J8 map raw8 x to the9vector tangential v, and radial9 z to components U_i z_i. Define C_cross=||J8^T (Lambda0 tensor I2) Rad8||_op, with x8=0. Then
 2<v,Lambda0 w>=- x^T Cmat x^{(2)} +2<v,Lambda0 R>
 >=-C_cross q^3 - (d/3)q^4.
(The full i,j sum is indispensable; offdiagonal terms do not vanish.)

Variational comparison gives delta^T Lambda_alpha delta >= delta^T Lambda0 delta -beta(x) delta^T Lambda0 delta. Using Lambda0<=dI and ||delta||<=q, this loses at most tau B d p q^2. Adaptive flux Taylor loses at most tau ||A|| p q^2. Discard w^T Lambda0 w>=0, retain exact radial lower. Hence, whenever tau B p<1,
 V²-R*² >= .5 x^T H0 x +tau p² - C_cross q³ -(d/3)q⁴ -tau(Bd+||A||) p q².

Choose 0<tau0<tau for which H0+2tau0 GG^T>=mu0 I. Complete the square:
 (tau-tau0)p²-tau(Bd+||A||)p q² >= -tau²(Bd+||A||)² q⁴/[4(tau-tau0)].
Therefore
 V²-R*² >= [.5 mu0 - C_cross q - {d/3+tau²(Bd+||A||)²/[4(tau-tau0)]}q²] q².
This is a proved analytic implication given certified root constants and tau B ||G^T|| rho<1. No constant yet certified here. It replaces the large b*d cubic loss by a quartic loss, since stress does not vary in the critical kernel. This is the intended structural gain, not a claimed numeric ball.

Further directional refinement is possible (radial A replaces full A, generalized metric instead of mu0), but not assumed above.
