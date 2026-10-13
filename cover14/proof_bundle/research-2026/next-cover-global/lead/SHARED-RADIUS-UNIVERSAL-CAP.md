# Possible universal face cap — unproved diagnostic route

Conjecture: for the full three-edge localradius/angleinterface, sum pairedfacetareas<=3sqrt(3)U²/2. Equalityregularrealtriangle, allfourradiiU,beta_i=gamma_i=pi/3. This would improve the crude sumsin<=3 on broad angle ranges, but requires proof; numeric memberglobalmax experiments are insufficient.

Reduction via real opposite angles gamma_i andcentralradiusR=xU:
 y_i sin beta_i = x sin gamma_i cos gamma_i + sin gamma_i*(y_i cos delta_i),
 delta_i=pi−beta_i−gamma_i,
 y_i cos delta_i <= sqrt(1−x²sin²gamma_i) (allowobtusedelta; upperpositivebranch).
 Therefore A/U² <= sum_i [x²sin gamma_i cos gamma_i + x sin gamma_i sqrt(1−x²sin²gamma_i)], sum gamma=pi.
A Jensenproof wouldneedconcavity ofthebracketfunctionin gamma oranothertriangleinequality; itisnotasserted. Atgamma_i=pi/3, optimizingx∈[0,1] yieldsmax3sqrt3/2atx=1. Unequalgammas/obtusebranchesremainproofobligation.

No use in any accepted certificate. Purpose is an exact reduced expression for a potentially stronger, low-dimensional universal bound.
