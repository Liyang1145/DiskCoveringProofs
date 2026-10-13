# q=1 degree-four hub exclusion by cluster capacity plus area

Scope and dependencies: all eleven equal-disk covers of the unit disk, r<=R=19/50, with the inward-root/global 9+2/refined-dual reductions used in C812. This proves only that q=1 cannot have a refined hub of degree four. No q0 degree-four exclusion is claimed.

## Extra necessary inequality

Fix the sole ear triple (0,1,2). Its three disks share the corresponding true Voronoi vertex, even when the ear was introduced at a cocircular degeneration. If p is that common point, every point covered by those three disks lies within 2r of p. Hence their union on S1 has angular measure at most 2 asin(2r)<=2B, B=asin(2R). This standard window bound is obtained by maximizing the S1 intersection of a disk of radius 2r<1 over its center distance (maximum halfwidth asin(2r)).

The nearest-owned arcs of these three labels are subsets of that union. Thus the six outside rings 3..8 own total boundary angle at least 2pi−2B. From the corrected C812 envelope w_i<=W(alpha_i),
  sum_{i=3..8} W(alpha_i) >= 2pi−2B.
This is a necessary bound on owned arc measure, not a false sum bound on overlapping actual arcs.

## Dual and full graph coverage

Add eta>=0 times the new constraint to C812's dual:
  D = 2pi(sum mu−lambda−eta)+2eta B
      + sum_edges sup[R²sin t−(mu_i+mu_j)t]
      + sum_rings sup[F(a)+(lambda+eta 1_{i>=3})W(a)−mu_i a].
Degree four means the smaller hub has three consecutive core-ring neighbors. The core is [0,2,3,4,5,6,7,8]; its eight starting positions have four equivalence classes under label reflection i->(2−i) mod9:
 starts {0,7}, {1,6}, {2,5}, {3,4}.
Reflection is just relabeling the entire arbitrary configuration, not assuming it is geometrically symmetric. Both hubs may be exchanged. The exact checker asserts the four representatives and reconstructs their complete neighbor sets.

## Exact certificate

`check_degree4_triple_fraction.py` uses Fraction arithmetic only, rational sine Taylor bounds and positive asin series with explicit tails; no floating trigonometry or optimizer required. Proposed mu,lambda,eta are rounded to 8 decimal exact rational coefficients. N=8192 grid over [0,22/7] and rigorous Lipschitz margins cover the complete variable intervals. For B=asin(.76), a 70-term positive series with tail x^141/(1−x²) bounds B from above. The sign eta>=0 makes that substitution safe. Uses rational pi lower 3.14159 and upper 22/7.

Four certified area upper bounds (rounded upward, exact rationals):
 start0: 3.1082;
 start1: 3.1234;
 start2: 3.1303;
 start3: 3.1240.
All are <3.14159<pi, excluding the covering.

Evidence `degree4_triple_fraction_control.json`; repro:
 py -3 -B research-2026/team-current/lead/check_degree4_triple_fraction.py
The multiplier proposal is `area_triple_dual.json`; the script is the certificate, not the optimizer status. This uses the same Fraction kernel as C812, not a newly independent arithmetic implementation. Geometry has an additional separately derived owned-arc union inequality.

## Structural consequence

Combining C812 with this result leaves refined degree pairs:
 q0: (4,9),(5,8),(6,7);
 q1: (5,7),(6,6).
q1's two remaining degree classes and the q0 sharp metric bound remain open. The same loose area dual numerically exceeds pi for balanced q1 classes; that is method diagnostic, not a proof of impossibility or feasibility.
