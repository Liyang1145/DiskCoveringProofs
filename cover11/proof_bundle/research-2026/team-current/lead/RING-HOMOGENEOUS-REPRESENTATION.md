# Homogeneous ring factor representation (exact covering of domain)

Each ring has endpoint radii u,v in[0,1]. Split into u>=v or v>=u. In first branch write u=t,v=tk, t,k in[0,1]; second branch swaps endpoints and the left/right multipliers. On genuine ring chord q_original>=qmin>0, so t>0 and representation covers the full admissible set. Angle a unchanged. Sector base angle at first endpoint becomes beta=atan2(k sin a,1−k cos a), independent of t. Other base angle=pi−a−beta. q_shape=1+k²−2k cos a; physical chord squared R²t²q_shape. Condition t²q_shape>=qmin avoids all shape singularities on the genuine domain.

Advantages: curvature angle depends on2 variables, common scale t removed from atan2; potential independent or analytic radial maximization later. No symmetry imposed: both ordered branches are required. At k=1,a=0 use broad beta enclosure until domain filter discards; never point atan2(0,0).

Derivatives for q_shape>0:
 beta_a=(k cos a−k²)/q_shape, beta_k=sin a/q_shape, beta_t=0.
 w=2asin(R t sqrt(q_shape)/2), den=sqrt(1−R²t²q_shape/4).
 w_a=R t k sin a/(sqrt(q_shape) den), w_k=R t(k−cos a)/(sqrt(q_shape) den), w_t=R sqrt(q_shape)/den.
These follow from direct differentiation; mean-value bounds require shape q>0 on entire box; use direct otherwise. Graph-independent representation usable in C817+factor bounds; does not tighten mathematical relaxation itself.
