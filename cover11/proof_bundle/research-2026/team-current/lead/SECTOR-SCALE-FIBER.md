# Exact interval elimination of the sector scale fiber

Scope: the C844 necessary local domain in fixed R0=19/50 units. This is an exact reparameterization of that relaxed domain, not sufficiency for a global cover. Use alpha in (0,pi], u,v in (0,1], and t0=75/76. Define
 d=(log u-log v)/2, s=sqrt(uv), E=exp(2|d|),
 Q=2(cosh(2d)-cos alpha), K=R0*sqrt(Q)/2,
 omega=w/2=asin(K*s).
Thus u=(sin omega/K)exp(d), v=(sin omega/K)exp(-d). K>0 since alpha>0. The endpoint-radius condition u,v<=1 is exactly
 0<omega<=asin(K exp(-|d|)).
Its asin argument is <=R0: Q exp(-2|d|)<=4 by the chord law.

C844 has two parts:
 (A) s² sin(alpha-omega)>=t0² sin omega;
 (B) sin(alpha-omega)>=E sin omega.
The first, since sin omega>0 and s=sin omega/K, becomes
 sin omega sin(alpha-omega)>=K²t0²,
 equivalently **cos(2omega-alpha)>=B := cos alpha+2K²t0²**.
B>-1 since K>0 and cos alpha>=-1. If B>1 the fiber is empty. Otherwise theta=acos B, and because 2omega-alpha lies in (-pi,pi), the exact solution of (A) is
 (alpha-theta)/2 <= omega <= (alpha+theta)/2.
There are no hidden periodic branches.

For alpha<pi, (B) is
 sin alpha cos omega >= (E+cos alpha) sin omega.
Here E+cos alpha>0, hence equivalent to
 omega<=atan2(sin alpha,E+cos alpha).
For alpha=pi,d!=0, it is impossible (E>1 and sin omega>0). For alpha=pi,d=0, it is an identity, hence no bound from (B). In that exceptional fiber, K=R0 and (A) reduces sin omega>=R0t0; the endpoint upper is sin omega<=R0. This recovers u=v=s in[t0,1] exactly.

Therefore, apart from the explicit pi branch, the admissible omega form one closed interval obtained by intersecting
 [(alpha-theta)/2,(alpha+theta)/2],
 (0,asin(K exp(-|d|))],
 (0,atan2(sin alpha,E+cos alpha)].
The existing nearest-width lower bound can be imposed as omega>=pi-8asin(R0)>0 (or the sharper U bound where appropriate). Empty intersections are discarded. This removes an implicit feasibility surface in (alpha,u,v), replacing it by explicit fiber endpoints; no all-radii saturation or u=v assumption is made.

For actual covers C840 additionally bounds u,v away from zero, yielding bounded d; that compact restriction is optional in this local identity. Optimizing a general dual factor over the remaining omega interval is NOT automatically an endpoint problem: the sine-area and linear/quadratic radius terms have mixed coefficients. No monotonicity of the objective is asserted.
