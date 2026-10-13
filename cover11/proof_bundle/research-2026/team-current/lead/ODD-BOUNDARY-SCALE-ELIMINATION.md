# Nine-boundary odd-cycle inversion eliminates covering scale from circle closures

Scope: positive q0k4 intrinsic triangle metrics of METRIC-GLUING-SUFFICIENCY.md. Dimensionless lengths are in units of a prospective covering radiusR; all11site-face circumradii and9switch radii <=1. Shared sides,11triangle sums,2hub sums and9ring angle sums hold. No boundary circle imposed yet. Each sector has center angle alpha_i and endpoint angles L_i,T_i, each switch angle2b_i. Let its normalized chord length ell_i>0 (ell_i²=u_i²+v_i²−2u_i v_i cos alpha_i). Define boundary turns
 tau_i=pi−T_i−L_(i+1)−2b_i.

## Euler angle sum (analytic exact)
The11site triangles have total angle11pi, hubs total4pi, hence ring-site angles sum7pi. The9ring angle equations give Σalpha_i=2pi+2Σb_i. Therefore
 Σtau_i=9pi−Σ(L_i+T_i)−2Σb_i=Σalpha_i−2Σb_i=2pi.
No width or circle assumption used. This is discrete Gauss–Bonnet, not a new independent equation to add to a Jacobian.

## Odd inversion
Circle closure is tau_i=(w_i+w_(i+1))/2. For9indices the matrix I+cyclicShift is invertible: alternating recurrence yields
 **w_i=Σ_{k=0}^8 (−1)^k tau_(i+k)**.
Hence w_i+w_(i+1)=2tau_i and Σw_i=Σtau_i=2pi identically. No nullspace or free alternating parameter (unlike even boundary count). Require computed w_i∈(0,pi); positive tau alone does NOT guarantee these inequalities.

## Scale removal / exact positive-domain equivalence
For each sector define R_i=2sin(w_i/2)/ell_i. The9nonlinear original boundary equations using w_i=2asin(R ell_i/2) are equivalent, on w_i∈(0,pi), to **R_0=R_1=...=R_8=:R**, with R>0. This is8scale-free equations and explicit R formula. They encode actual cyclic polygon closure; no further circle realization equation is missing once full positive flat gluing holds. WithR<1 and all intrinsic face/switch radii<=1 the development theorem constructs a covering of unitD by radiusR disks.

The optimization can therefore be written purely over intrinsic shape: minimize2sin(w0/2)/ell0 subject to8ratio equalities, original shared-metric constraints and positivity; R no longer an independent search variable. Simultaneous uniform rescaling of all intrinsic lengths rescales R inversely. Thus at optimum at least one of20local radii is1 (otherwise scale up all intrinsic lengths until maxradius1, preserving angles/ratios and decreasingR). This proves ONLY max(localradii)=1, never all switches/faces saturated.

Nondegenerate necessity assumes chosen triangulation with all29faces positive. Degenerate coverings remain handled by original closed relaxation, not silently excluded. No global uniqueness/optimality claim. Odd inversion and scale elimination are analytic exact and graph-independent for any odd boundary count with corresponding flat disk structure.

Next practical use: optimize/interval-bound shape with8circle consistency constraints; avoid redundant total-width equation and separateR subdivision. This representation may support algebraic circle constraints or local certified uniqueness, but does not by itself solve global shape optimization.
