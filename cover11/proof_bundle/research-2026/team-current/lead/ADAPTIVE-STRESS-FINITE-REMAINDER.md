# Smooth adaptive stress: finite remainder without inverse derivatives

Same exact C891 root and C909/C912 carrying graph (45 edges,9 anchors,20 free nodes). The six slack edges of the full51 oracle have weights identically ZERO for every x and do not occur in Q. B is the 41x45 geometric root equilibrium matrix: its first40rows are signed edge-displacement coordinates at the20free nodes; its last row is all ones. Therefore BN=0 includes both geometric equilibrium and 1^T N=0. It is not a bare incidence matrix. Let alpha0>0 be normalized radial stress, B N=0, and G=G8=T8 N. Put Q=tau N G^T and alpha(x)=alpha0+Qx, where x is raw theta8-pinned angular displacement. Identities are exact; interval arithmetic only bounds their constants.

For every t near zero, alpha0+Nt has the SAME harmonic free nodes at U0: free equilibrium is B's first40rows, and positive weights give unique Dirichlet minimizer. All carrying lengths equal R*. Hence E_alpha(U0)=R*² for every such alpha; its anchor flux l_alpha=Lambda_alpha U0 is linear in alpha at U0, since free coordinates are unchanged. Write l_alpha=l0+Mx (M: R8→R18).

Choose rational b,d,m,mu>0 with
1. |(Qx)_e|<=b alpha0_e ||x|| (sufficient b>=max_e ||Q_e||2/alpha0_e);
2. Lambda0 <= d I in the scalar anchor Dirichlet form;
3. ||Mx||F<=m||x||;
4. H0+2tau GG^T >= mu I on raw8 chart;
5. radial anchor fluxes l0_i=a_i U0_i have a_i>=0.

A sufficient d is max anchor incident alpha0-weight: Laa is diagonal in this graph, Lambda0=Laa-Laf Lff^-1 Lfa<=Laa. Positivity Lambda0>=0 is the Dirichlet energy principle.

For q=||x|| and bq<1, weights alpha(x)>0, sum=1. Variational comparison of edge energies gives
(1-bq)Lambda0 <= Lambda_alpha(x) <= (1+bq)Lambda0
as quadratic forms. This compares minimized energies, not interval implementations.

Set delta_i=U_i(x)-U0_i, v_i=J U0_i x_i and w=delta-v (x8=0). Exact integral Taylor bounds give ||delta||F<=q, ||v||F=q, ||w||F<=q²/2. Explicitly w_i=x_i² integral_0^1 (1-s) U_i''(s*x_i) ds, so |w_i|<=x_i²/2 since |U_i''|=1; then sum x_i^4 <= (sum x_i²)^2. This holds for either sign of x_i and is not an asymptotic Taylor truncation. Expanding the quadratic Dirichlet energy at U0,
F(x)=E_alpha(x)(U(x))=R*²+2<l0+Mx,delta>+<delta,Lambda_alpha(x)delta>.

Radial term: since a_i>=0 and cos s>=1-s²/2,
2<l0,delta>=sum_i 2a_i(cos x_i-1)>=-sum_i a_i x_i².

Adaptive linear term:
2<Mx,delta>=2<Mx,v>+2<Mx,w>
>=tau x^T GG^T x - m q³.
Here T_je=2 s_je (X_v-X_w)·J U0_j for an edge incident to anchor j, and zero otherwise; s_je is its signed incidence. Flux change (Mx)_j=sum_e s_je(Qx)_e(X_v-X_w), with no factor2. Direct summation therefore gives 2<Mx,v>=x^T T8 Qx=tau x^T G G^T x. This is an algebraic identity, not a residual containing zero. Likewise H0=2[J_U^T (Lambda0 tensor I2) J_U - diag(a_0,...,a_7)], by differentiating E_alpha0(U(x)); hence its quadratic term is exactly half x^T H0 x.

Quadratic term:
<delta,Lambda_alpha delta> >= <delta,Lambda0 delta>-bq<delta,Lambda0 delta>
>=<v,Lambda0 v>-d q³-bd q³.
The first loss uses cross term 2<v,Lambda0 w> and discards nonnegative <w,Lambda0 w>; the second uses Lambda0<=dI and ||delta||<=q.

Combining (H0 is exactly the angular Hessian of E_alpha0),

V(U(x))² >= F(x) >= R*² + (mu/2 - [d(1+b)+m] q) q².

Thus any rational rho with b rho<1 and [d(1+b)+m]rho<=mu/4 certifies the ENTIRE ball q<=rho with growth >=mu q²/4. This requires no guessed third-derivative bound, no fixed-free-node trial energy lower bound, and no assumption that E_alpha is linear in alpha away from U0.

Status: analytic lemma conditional on the five explicit constants/identities. Next instrument checks constants at exact C891 root. This is local, not a global reduction.
