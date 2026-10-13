# Quantitative compactness and anchor nonexpansiveness for C1261

Same finite connected fixed-beta Dirichlet network, c=pi-beta, strict cuts. This concerns the abstract radius solution, NOT a global cover bound.

## Uniform energy remainder
For d>=0 write h_beta(d)=atan2(sin beta,exp(d)-cos beta). Since h(-d)=c-h(d), the primitive phi(d)=-integral_0^d h(s)ds satisfies EXACTLY
 phi(d)=-c min(d,0)-F_beta(|d|), F_beta(t)=integral_0^t h_beta(s)ds>=0.
Moreover 0<=F_beta(t)<=pi²/6 uniformly for beta∈(0,pi). For s>0 the principal logarithm power series gives h_beta(s)=sum_{k>=1} exp(-ks)sin(k beta)/k. Integrate s from epsilon>0 to infinity (absolute convergence), then let epsilon down0 by bounded/monotone convergence of the positive h integrals and absolute convergence of sum sin(k beta)/k². Hence integral_0^infinity h=sum sin(k beta)/k²<=sum1/k²=pi²/6. No positivity of individual Fourier terms is presumed.

First set ALL anchors equal to1 (log0), allowed by C1261 because cutconditions do not depend on their radii. Energy normalized as in audit is E(l)=P(l)-sum_edges F_beta(|l_f-l_g|), with anchor l_g=0. Thus E(0)=0 and at its minimizer l^0,
 eta||l^0||infty <=P(l^0)<=E(l^0)+|E|pi²/6<=|E|pi²/6,
where eta is the minimum of BOTH strict-cut margins. Therefore |log R_f^0|<=B=|E|pi²/(6eta).

## Arbitrary positive anchors without the additive-energy ambiguity
By comparison/homogeneity (COUPLED-RADIUS-MAXIMUM-PRINCIPLE.md), a_min R_f^0<=R_f(a)<=a_max R_f^0. Thus explicit box
 **a_min exp(-B)<=R_f(a)<=a_max exp(B)**
for every face. All quantities are given data. This is crude but turns qualitative existence into a bounded search domain without guessing solver initialization. On a beta-box with all beta strictly in(0,pi) and a certified positive lower bound eta0 for all cut margins, the same bound is uniform withB=|E|pi²/(6eta0). Because margins affine in beta, interval lower bounds require no transcendental optimization apart from pi representation. Do not extend across zero cutmargin.

More sharply, for two anchor assignments a,b at fixedbeta,
 min_e log(a_e/b_e)<=log(R_f(a)/R_f(b))<=max_e log(a_e/b_e).
So the solution map in logarithmic anchor variables is globally1-Lipschitz in supnorm, is order-preserving, and commutes with common shifts. Analytic derivatives obey partial l_f/partial L_e>=0 and sum_e partial l_f/partial L_e=1. This follows directly from comparison+homogeneity without invoking a black-box M-matrix theorem. Consequently verified logradius enclosures for one anchor assignment extend to an entire anchor-logbox by its coordinate extrema. This does NOT bound effects of changing beta, nor prove radiuscap or cyclicity.

Scope/falsifier: failure of a positive solution at strict cuts would contradictC1261; a counterexample tosupnormbound would contradict the exact maximum-ratio comparison proof. No numeric claim is needed; nearcutboundary the explicitB diverges and is not a useful sharpcover bound. Structural use is finite parameter enclosure for strict boxes and removalofsolverinitialization as existence evidence, not new graph exclusions.
